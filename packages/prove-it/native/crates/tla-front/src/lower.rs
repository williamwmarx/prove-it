//! The lowering of a linked environment to the engine IR, as `lowerToIr` in `src/engine/ir.ts`
//! writes it: the nodes and definitions the model reaches, in the order `ir.ts` meets them, the
//! texts in the order it first uses them, and the builtins and constants the names resolve to.
//! `tla_ir::encode` writes the blob.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use tla_ir::{
    ActionProperty as IrActionProperty, Atom as IrAtom, AtomKind, Bound as IrBound,
    Builtin as IrBuiltin, ConfigName, Constant, Definition as IrDefinition, DefinitionForm,
    EnabledActions, EvaluatedDefinition, Index, Ir, Junction, LiveProperty, LiveTerm, Model,
    Name as IrName, Node, NodeId, NodeKind, Nodes, Param, PathStep, Pattern, PermutedSet, Possible,
    Printed, Resolution, Scope as IrScope, ScopeBinding, Selector as IrSelector,
    SourceRange as IrRange, Startup, Symmetry, TextId, Update, Value, Values,
};

use crate::ast::*;
use crate::config::ConfigValue;
use crate::dependencies::{DefinitionFacts, create_definition_facts};
use crate::environment::Environment;
use crate::errors::{FrontError, describe_range};
use crate::hash::{FastMap, FastSet};
use crate::live::{Live, Liveness};
use crate::resolve::{Result, SymbolKind};
use crate::values::ValueOrder;

/// SyntaxTreeNode.getHumanReadableImage, which joins the tokens of an expression without spaces,
/// or none for an expression whose tokens the AST doesn't keep.
fn get_expression_image(expression: &Expression) -> Option<String> {
    let name = match &expression.kind {
        ExpressionKind::Apply { operator, .. } => operator.clone(),
        _ => expression.reference().unwrap_or_default(),
    };
    match &expression.kind {
        ExpressionKind::Identifier { .. } => Some(name.to_string()),
        ExpressionKind::Number { text, .. } => Some(text.to_string()),
        // A string's token is written with its quotes; one with an escape isn't kept as written.
        ExpressionKind::String { value }
            if !value
                .chars()
                .any(|character| matches!(character, '\\' | '"') || character.is_control()) =>
        {
            Some(format!("\"{value}\""))
        }
        ExpressionKind::Apply { args, .. } => {
            let args = args
                .iter()
                .map(|arg| get_expression_image(arg))
                .collect::<Option<Vec<String>>>()?;
            if is_prefix_word(&name) {
                // `SUBSET S`, `UNION S` and `DOMAIN f` are tokens with no parentheses.
                (args.len() == 1).then(|| format!("{name}{}", args[0]))
            } else if name
                .chars()
                .next()
                .is_some_and(|first| first.is_ascii_alphabetic() || first == '_')
            {
                Some(format!("{name}({})", args.join(",")))
            } else if args.len() == 2 {
                Some(args.join(&name))
            } else {
                None
            }
        }
        // The braces and commas are tokens of the enumeration's node.
        ExpressionKind::SetEnumeration(elements) => {
            let elements = elements
                .iter()
                .map(|element| get_expression_image(element))
                .collect::<Option<Vec<String>>>()?;
            Some(format!("{{{}}}", elements.join(",")))
        }
        // The angle brackets, the brackets, `|->`, `:`, `\in` and CHOOSE are tokens of their
        // nodes, as the commas between their parts are.
        ExpressionKind::Tuple(elements) => {
            let elements = elements
                .iter()
                .map(|element| get_expression_image(element))
                .collect::<Option<Vec<String>>>()?;
            Some(format!("<<{}>>", elements.join(",")))
        }
        ExpressionKind::Record { is_set, fields } => {
            let separator = if *is_set { ":" } else { "|->" };
            let fields = fields
                .iter()
                .map(|field| {
                    Some(format!(
                        "{}{separator}{}",
                        field.name,
                        get_expression_image(&field.value)?
                    ))
                })
                .collect::<Option<Vec<String>>>()?;
            Some(format!("[{}]", fields.join(",")))
        }
        ExpressionKind::FunctionConstruction { bounds, body } => {
            let bounds = bounds
                .iter()
                .map(|bound| get_bound_image(&bound.pattern, Some(&bound.set)))
                .collect::<Option<Vec<String>>>()?;
            Some(format!(
                "[{}|->{}]",
                bounds.join(","),
                get_expression_image(body)?
            ))
        }
        ExpressionKind::Choose { pattern, set, body } => Some(format!(
            "CHOOSE{}:{}",
            get_bound_image(pattern, set.as_ref())?,
            get_expression_image(body)?
        )),
        _ => None,
    }
}

/// The name of the definition TLC takes for the SYMMETRY: the one the configuration substitutes
/// for it with `<-`, if any, which `SpecProcessor.processConstants` puts in `defns` in its place.
/// One substituted in a module's scope (`<-[M]`) replaces only what the definition's node
/// evaluates to, not the body `getSymmetryPerms` evaluates.
fn get_symmetry_name<'c>(config: &'c crate::config::ModelConfig, name: &'c str) -> &'c str {
    config
        .substitutions
        .iter()
        .find(|substitution| substitution.module.is_none() && substitution.name == name)
        .map_or(name, |substitution| substitution.target.as_str())
}

/// The image of a bound: its name or its tuple of names, and `\in` its set where it has one.
fn get_bound_image(pattern: &BoundPattern, set: Option<&Expr>) -> Option<String> {
    let names = match pattern {
        BoundPattern::Name { name, .. } => name.to_string(),
        BoundPattern::Tuple { names, .. } => format!("<<{}>>", names.join(",")),
    };
    match set {
        Some(set) => Some(format!("{names}\\in{}", get_expression_image(set)?)),
        None => Some(names),
    }
}

/// Where a definition passes its parameter to `TLCGet` and does nothing else, the position of
/// that parameter: an INSTANCE of TLC copies `TLCGet` as `I!TLCGet(argument0) == TLCGet(argument0)`
/// after the INSTANCE's own parameters (`createLocalAlias`), which reads only what `TLCGet` of the
/// argument reads.
fn get_tlc_get_alias(definition: &Definition, environment: &Environment) -> Option<usize> {
    let DefinitionKind::Operator { params, .. } = &definition.kind else {
        return None;
    };
    let ExpressionKind::Apply { args, .. } = &definition.body.kind else {
        return None;
    };
    let [arg] = args.as_slice() else {
        return None;
    };
    let ExpressionKind::Identifier { name, .. } = &arg.kind else {
        return None;
    };
    if definition.body.reference().as_deref() != Some("TLCGet")
        || environment.definitions.contains_key("TLCGet")
        || arg.reference().as_ref() != Some(name)
    {
        return None;
    }
    let position = params.iter().rposition(|param| param.name == *name)?;
    (params[position].arity == 0).then_some(position)
}

/// The argument a call of `TLCGet`, or of a definition that passes its argument to it (`aliases`
/// holds the LET ones), gives `TLCGet`.
fn get_tlc_get_index<'a>(
    expression: &'a Expression,
    environment: &Environment,
    aliases: &[(Name, usize, usize)],
) -> Option<&'a Expr> {
    let ExpressionKind::Apply { operator, args, .. } = &expression.kind else {
        return None;
    };
    let key = expression.reference()?;
    if &*key == "TLCGet" && !environment.definitions.contains_key("TLCGet") {
        return (args.len() == 1).then(|| &args[0]);
    }
    let (position, arity) = match aliases.iter().rev().find(|(name, ..)| *name == *operator) {
        Some((_, position, arity)) => (*position, *arity),
        None => {
            let key = environment.substitutions.get(&key).cloned().unwrap_or(key);
            let definition = environment.definitions.get(&key)?;
            let DefinitionKind::Operator { params, .. } = &definition.kind else {
                return None;
            };
            (get_tlc_get_alias(definition, environment)?, params.len())
        }
    };
    (args.len() == arity).then(|| &args[position])
}

/// The builtin an operator or a name stands for where nothing replaces it: no definition of the
/// spec's, no substitution and no Java method a configuration binds.
fn get_plain_builtin<'a>(expression: &Expression, environment: &'a Environment) -> Option<&'a str> {
    let key = expression.reference()?;
    if environment.definitions.contains_key(&key)
        || environment.substitutions.contains_key(&key)
        || environment
            .operator_objects
            .method_aliases
            .contains_key(&key)
    {
        return None;
    }
    let builtin = environment.builtins.get(&key)?;
    builtin.intrinsic.is_none().then_some(&*builtin.name)
}

/// A set enumeration of naturals, of which `is_duration` tells reads of the duration apart, and
/// number literals that isn't empty, or of literals alone.
fn is_filled_set(operand: &Expression, is_duration: &impl Fn(&Expression) -> bool) -> bool {
    let is_number = |operand: &Expression| matches!(&operand.kind, ExpressionKind::Number { value, .. } if *value >= 0.0);
    let is_literal = |operand: &Expression| {
        is_number(operand) || matches!(&operand.kind, ExpressionKind::String { .. })
    };
    matches!(&operand.kind, ExpressionKind::SetEnumeration(elements)
        if !elements.is_empty()
            && (elements.iter().all(|element| is_number(element) || is_duration(element))
                || elements.iter().all(|element| is_literal(element))))
}

/// Whether a function over `bounds` with `body`, as a constructor or a function definition
/// (`f[i \in S] == e`), has a domain TLC builds without failing whatever the duration
/// (OPCODE_fc's `toFcnRcd`, `FcnLambdaValue`'s domain): sets `is_filled_set` takes, and a body
/// that is a literal, a read of the duration or a bound name, which TLC doesn't evaluate for it.
fn is_filled_domain(
    bounds: &[Bound],
    body: &Expression,
    is_duration: &impl Fn(&Expression) -> bool,
) -> bool {
    let is_literal = |operand: &Expression| {
        matches!(&operand.kind, ExpressionKind::Number { value, .. } if *value >= 0.0)
            || matches!(&operand.kind, ExpressionKind::String { .. })
    };
    bounds
        .iter()
        .all(|bound| is_filled_set(&bound.set, is_duration))
        && (is_literal(body)
            || is_duration(body)
            || matches!(&body.kind,
                ExpressionKind::Identifier { name, .. }
                    if body.is_locally_resolved()
                        && bounds.iter().any(|bound| matches!(&bound.pattern,
                            BoundPattern::Name { name: bound, .. } if bound == name))))
}

/// The value of `TRUE`, `FALSE` or a comparison whose result is the same for every duration TLC
/// may report, which is a natural (`(int) ((System.currentTimeMillis() - startTime) / 1000L)`):
/// `d >= 0`, `0 <= d`, `d < 0`, `0 > d`, `d \in Nat`, `d \in Int` and their `\notin`, where `d`
/// is a read of the duration that `is_duration` tells apart. Evaluating it reads nothing else.
fn get_value_for_any_duration(
    expression: &Expression,
    environment: &Environment,
    is_duration: impl Fn(&Expression) -> bool,
    is_filled_function: impl Fn(&Expression) -> bool,
) -> Option<bool> {
    let ExpressionKind::Apply { args, .. } = &expression.kind else {
        return match &expression.kind {
            ExpressionKind::Identifier { .. } => match get_plain_builtin(expression, environment) {
                Some("TRUE") => Some(true),
                Some("FALSE") => Some(false),
                _ => None,
            },
            _ => None,
        };
    };
    let [left, right] = args.as_slice() else {
        return None;
    };
    let operator = get_plain_builtin(expression, environment)?;
    let is_zero = |operand: &Expression| matches!(&operand.kind, ExpressionKind::Number { value, .. } if *value == 0.0);
    let is_naturals = |operand: &Expression| {
        matches!(&operand.kind, ExpressionKind::Identifier { .. })
            && matches!(get_plain_builtin(operand, environment), Some("Nat" | "Int"))
    };
    // A set enumeration of naturals and number literals that isn't empty, or the domain of a
    // function TLC builds over such sets of a bound name, a natural or a literal (OPCODE_fc's
    // `toFcnRcd`), which TLC builds without failing whatever the duration, compared with `{}`.
    // A string beside an integer fails as TLC normalizes the set (`IntValue.compareTo`), with a
    // message that prints the duration where the integer is one: literals alone fail alike on
    // either side, which the engine evaluates.
    let is_filled = |operand: &Expression| {
        is_filled_set(operand, &is_duration)
            || matches!(&operand.kind, ExpressionKind::Apply { args, .. }
                if get_plain_builtin(operand, environment) == Some("DOMAIN")
                    && matches!(args.as_slice(), [function]
                        if is_filled_function(function)
                            || matches!(&function.kind, ExpressionKind::FunctionConstruction { bounds, body }
                                if is_filled_domain(bounds, body, &is_duration))))
    };
    let is_empty = |operand: &Expression| matches!(&operand.kind, ExpressionKind::SetEnumeration(elements) if elements.is_empty());
    if matches!(operator, "=" | "#" | "/=")
        && (is_empty(left) && is_filled(right) || is_filled(left) && is_empty(right))
    {
        return Some(operator != "=");
    }
    let decided = match operator {
        ">=" | "\\geq" | "<" => is_duration(left) && is_zero(right),
        "<=" | "\\leq" | ">" => is_zero(left) && is_duration(right),
        "\\in" | "\\notin" => is_duration(left) && is_naturals(right),
        _ => false,
    };
    decided.then_some(matches!(operator, ">=" | "\\geq" | "<=" | "\\leq" | "\\in"))
}

/// The longest run, in seconds, for which a read of the duration counts as a natural no larger
/// than this: TLC reports `(int) ((System.currentTimeMillis() - startTime) / 1000L)`, and a run of
/// 2^24 seconds (194 days) is assumed never to happen.
const DURATION_BOUND: u64 = 1 << 24;

/// The bound a LET operator's parameters stand for where the operator counts as a natural of
/// naturals: its applications check that each argument is no larger.
const PARAMETER_BOUND: u64 = 1 << 26;

/// TLC's `int` values end at `Integer.MAX_VALUE`, past which `+` and `*` fail with
/// `TLC_MODULE_OVERFLOW` (`Naturals.Plus` and `Naturals.Times`).
const INT_BOUND: u64 = i32::MAX as u64;

/// Whether an expression reads the duration and nothing else (`get_duration_bound`).
fn is_duration_read(
    expression: &Expression,
    environment: &Environment,
    stats: &[Name],
    durations: &[(Name, u64)],
    aliases: &[(Name, usize, usize)],
    depth: usize,
) -> bool {
    get_duration_bound(expression, environment, stats, durations, aliases, depth).is_some()
}

/// Where an expression reads the duration and nothing else, the largest value it may have for a
/// run shorter than `DURATION_BOUND`, which TLC computes without failing: `TLCGet("stats").duration`
/// or `TLCGet("duration")` of `TLCGet` or of a name that passes its one argument to it, or a name
/// of the spec's or a LET's (`stats`, `durations`, each with its bound) for one of them.
fn get_duration_bound(
    expression: &Expression,
    environment: &Environment,
    stats: &[Name],
    durations: &[(Name, u64)],
    aliases: &[(Name, usize, usize)],
    depth: usize,
) -> Option<u64> {
    let is_tlc_get_of = |expression: &Expression, key: &str| {
        matches!(&expression.kind, ExpressionKind::Apply { args, .. } if args.len() == 1)
            && get_tlc_get_index(expression, environment, aliases).is_some_and(
                |index| matches!(&index.kind, ExpressionKind::String { value } if &**value == key),
            )
    };
    let get_bound = |name: &Name| {
        durations
            .iter()
            .rev()
            .find(|(duration, _)| duration == name)
            .map(|(_, bound)| *bound)
    };
    match &expression.kind {
        ExpressionKind::FieldAccess { record, field } => (&**field == "duration"
            && match &record.kind {
                ExpressionKind::Identifier { name, .. } if stats.contains(name) => true,
                _ => is_tlc_get_of(record, "stats"),
            })
        .then_some(DURATION_BOUND),
        // A sum or a product of naturals, one of them a read of the duration, and an operator of
        // a LET's whose body is one for any naturals (`durations`) applied to naturals, are
        // naturals too, which a comparison decides alike, where they can't pass `INT_BOUND`.
        ExpressionKind::Apply { operator, args, .. } => {
            if is_tlc_get_of(expression, "duration") {
                return Some(DURATION_BOUND);
            }
            if depth >= 16 {
                return None;
            }
            let get_natural_bound = |operand: &Expression| match &operand.kind {
                ExpressionKind::Number { value, .. }
                    if *value >= 0.0 && *value <= INT_BOUND as f64 && value.fract() == 0.0 =>
                {
                    Some(*value as u64)
                }
                _ => get_duration_bound(operand, environment, stats, durations, aliases, depth + 1),
            };
            let builtin = get_plain_builtin(expression, environment);
            if let (Some(operation @ ("+" | "*")), [left, right]) = (builtin, args.as_slice()) {
                let (left_bound, right_bound) =
                    (get_natural_bound(left)?, get_natural_bound(right)?);
                let bound = if operation == "+" {
                    left_bound.checked_add(right_bound)?
                } else {
                    left_bound.checked_mul(right_bound)?
                };
                return (bound <= INT_BOUND
                    && args.iter().any(|operand| {
                        is_duration_read(operand, environment, stats, durations, aliases, depth + 1)
                    }))
                .then_some(bound);
            }
            let bound = get_bound(operator)?;
            (expression.is_locally_resolved()
                && args.iter().all(|operand| {
                    get_natural_bound(operand).is_some_and(|bound| bound <= PARAMETER_BOUND)
                }))
            .then_some(bound)
        }
        ExpressionKind::Identifier { name, .. } if get_bound(name).is_some() => get_bound(name),
        // A definition of the spec's without parameters that reads the duration.
        ExpressionKind::Identifier { .. } if depth < 16 => {
            let key = expression.reference()?;
            let key = environment.substitutions.get(&key).cloned().unwrap_or(key);
            let definition = environment.definitions.get(&key)?;
            if !matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty())
            {
                return None;
            }
            get_duration_bound(&definition.body, environment, &[], &[], &[], depth + 1)
        }
        _ => None,
    }
}

/// Whether a LET's later definitions or body may name one of its definitions: TLC evaluates a
/// LET's definition only where it is named (`OpApplNode` of its `OpDefNode`).
fn may_name(expressions: &[&Expression], name: &Name) -> bool {
    expressions.iter().any(|expression| {
        let named = match &expression.kind {
            ExpressionKind::Identifier { name: written, .. }
            | ExpressionKind::Apply {
                operator: written, ..
            }
            | ExpressionKind::OperatorReference {
                operator: written, ..
            } => written == name || written.ends_with(&format!("!{name}")),
            _ => false,
        };
        named
            || expression
                .children()
                .iter()
                .any(|child| may_name(&[child], name))
    })
}

/// Whether evaluating an expression may read `TLCGet("stats").duration` or `TLCGet("duration")`
/// (`TLCGetSet.TLCGetStringValue`, `AbstractChecker.getStatistics`): a `TLCGet` of a string other
/// than those, or of a number, and a field other than `duration` of `TLCGet("stats")` or of a LET's
/// name for it, read no time, nor does a comparison whose result is the same for every duration
/// (`get_value_for_any_duration`), what follows it where it decides a junction or an IF, or a LET definition nothing names. `stats` holds the LET names
/// that stand for `TLCGet("stats")` in scope, `durations` those that stand for a read of the
/// duration, `aliases` the LET operators that pass their argument to `TLCGet` (a LET INSTANCE of
/// TLC) with that argument's position, `seen` the definitions already walked. Where `is_final`,
/// the expression is a postcondition's, which TLC evaluates once the search is done, and also an
/// argument of a parameter an operator the spec defines never names, two reads of
/// `TLCGet("stats")` compared and the DOMAIN of a LET function over durations compared with `{}`
/// (`functions`) read no time.
#[allow(clippy::too_many_arguments)]
fn may_read_duration(
    expression: &Expression,
    environment: &Environment,
    is_final: bool,
    stats: &mut Vec<Name>,
    durations: &mut Vec<(Name, u64)>,
    aliases: &mut Vec<(Name, usize, usize)>,
    functions: &mut Vec<Name>,
    seen: &mut FastSet<usize>,
) -> bool {
    let is_stats = |expression: &Expression, stats: &[Name], aliases: &[(Name, usize, usize)]| {
        match &expression.kind {
        ExpressionKind::Apply { .. } => get_tlc_get_index(expression, environment, aliases).is_some_and(|index| {
            matches!(&index.kind, ExpressionKind::String { value } if &**value == "stats")
        }),
        ExpressionKind::Identifier { name, .. } => stats.contains(name),
        _ => false,
    }
    };
    // `TLCGet` or a name for it, given as an operator's argument, may be applied to anything.
    let is_tlc_get_name = |expression: &Expression, aliases: &[(Name, usize, usize)]| {
        let (ExpressionKind::Identifier { name, .. }
        | ExpressionKind::OperatorReference { operator: name, .. }) = &expression.kind
        else {
            return false;
        };
        aliases.iter().any(|(alias, ..)| alias == name)
            || expression.reference().is_some_and(|key| {
                (&*key == "TLCGet" && !environment.definitions.contains_key("TLCGet"))
                    || environment
                        .definitions
                        .get(&environment.substitutions.get(&key).cloned().unwrap_or(key))
                        .is_some_and(|definition| {
                            get_tlc_get_alias(definition, environment).is_some()
                        })
            })
    };
    let get_value = |expression: &Expression,
                     stats: &[Name],
                     durations: &[(Name, u64)],
                     aliases: &[_],
                     functions: &[Name]| {
        get_value_for_any_duration(
            expression,
            environment,
            |operand| is_duration_read(operand, environment, stats, durations, aliases, 0),
            |function| {
                matches!(&function.kind, ExpressionKind::Identifier { name, .. }
                    if function.is_locally_resolved() && functions.contains(name))
            },
        )
    };
    match &expression.kind {
        _ if get_value(expression, stats, durations, aliases, functions).is_some() => false,
        ExpressionKind::FieldAccess { record, field } if is_stats(record, stats, aliases) => {
            &**field == "duration"
        }
        // TLC evaluates a junction's operands in order and stops at the first that decides it
        // (`Tool.evalAppl` of `OPCODE_cl` and `OPCODE_dl`).
        //
        // A comparison of a natural that reads the duration with a number never fails, so where
        // a later operand decides the junction, its value is that operand's either way: TLC
        // stops at the comparison, or goes on to operands that each go on for any duration, or
        // to the one that decides it.
        ExpressionKind::Junction {
            is_and, operands, ..
        } => {
            let is_compared = |operand: &Expression| {
                let ExpressionKind::Apply { args, .. } = &operand.kind else {
                    return false;
                };
                let is_number =
                    |operand: &Expression| matches!(operand.kind, ExpressionKind::Number { .. });
                let is_natural = |operand: &Expression| {
                    is_duration_read(operand, environment, stats, durations, aliases, 0)
                };
                matches!(
                    get_plain_builtin(operand, environment),
                    Some("=" | "#" | "/=" | "<" | ">" | "<=" | ">=" | "=<" | "\\leq" | "\\geq")
                ) && matches!(args.as_slice(), [left, right]
                    if is_natural(left) && is_number(right) || is_number(left) && is_natural(right))
            };
            let compared: Vec<bool> = operands
                .iter()
                .map(|operand| is_compared(operand))
                .collect();
            let mut is_undecided = false;
            for (operand, is_compared) in operands.iter().zip(compared) {
                let value = get_value(operand, stats, durations, aliases, functions);
                if value == Some(!*is_and) {
                    return false;
                }
                // An operand whose value is the same for every duration lets it go on.
                let is_compared = is_compared && value.is_none();
                if is_undecided && value != Some(*is_and) && !is_compared {
                    return true;
                }
                if is_compared {
                    is_undecided = true;
                    continue;
                }
                if may_read_duration(
                    operand,
                    environment,
                    is_final,
                    stats,
                    durations,
                    aliases,
                    functions,
                    seen,
                ) {
                    return true;
                }
            }
            is_undecided
        }
        // A quantifier over set enumerations of reads of the duration binds its names to them,
        // each as large as the largest of them.
        ExpressionKind::Quantified { bounds, body, .. }
            if let Some(names) = bounds
                .iter()
                .map(|bound| {
                    let BoundPattern::Name { name, .. } = &bound.pattern else {
                        return None;
                    };
                    let ExpressionKind::SetEnumeration(elements) = &bound.set.kind else {
                        return None;
                    };
                    let mut largest = None;
                    for element in elements {
                        let bound =
                            get_duration_bound(element, environment, stats, durations, aliases, 0)?;
                        largest = largest.max(Some(bound));
                    }
                    Some((name.clone(), largest?))
                })
                .collect::<Option<Vec<_>>>() =>
        {
            let outer = durations.len();
            durations.extend(names);
            let reads = may_read_duration(
                body,
                environment,
                is_final,
                stats,
                durations,
                aliases,
                functions,
                seen,
            );
            durations.truncate(outer);
            reads
        }
        ExpressionKind::If {
            condition,
            consequent,
            alternative,
        } if let Some(value) = get_value(condition, stats, durations, aliases, functions) => {
            let taken = if value { consequent } else { alternative };
            may_read_duration(
                taken,
                environment,
                is_final,
                stats,
                durations,
                aliases,
                functions,
                seen,
            )
        }
        ExpressionKind::Apply { operator, args, .. }
            if &**operator == "DOMAIN" && args.len() == 1 && is_stats(&args[0], stats, aliases) =>
        {
            false
        }
        // Two reads of `TLCGet("stats")` (or LET names for them) compared hold the same record:
        // a postcondition reads the final counts, and the same duration but where a second ends
        // between the two reads, a few microseconds apart, which is assumed never to happen.
        ExpressionKind::Apply { args, .. }
            if is_final
                && matches!(
                    get_plain_builtin(expression, environment),
                    Some("=" | "#" | "/=")
                )
                && matches!(args.as_slice(), [left, right]
                    if is_stats(left, stats, aliases) && is_stats(right, stats, aliases)) =>
        {
            false
        }
        ExpressionKind::Apply { args, .. }
            if get_tlc_get_index(expression, environment, aliases).is_some() =>
        {
            let index = get_tlc_get_index(expression, environment, aliases).expect("checked above");
            let reads = match &index.kind {
                ExpressionKind::String { value } => matches!(&**value, "stats" | "duration"),
                ExpressionKind::Number { .. } => false,
                _ => true,
            };
            // An INSTANCE's own parameters are evaluated as its other arguments are.
            reads
                || args.iter().any(|arg| {
                    !std::ptr::eq(arg, index)
                        && may_read_duration(
                            arg,
                            environment,
                            is_final,
                            stats,
                            durations,
                            aliases,
                            functions,
                            seen,
                        )
                })
        }
        ExpressionKind::Identifier { name, .. }
            if stats.contains(name)
                || durations.iter().any(|(duration, _)| duration == name)
                || functions.contains(name) =>
        {
            true
        }
        ExpressionKind::Apply { operator, .. }
            if durations.iter().any(|(duration, _)| duration == operator) =>
        {
            true
        }
        _ if is_tlc_get_name(expression, aliases) => true,
        ExpressionKind::Let {
            definitions, body, ..
        } => {
            let outer = stats.clone();
            let outer_durations = durations.clone();
            let outer_aliases = aliases.clone();
            let outer_functions = functions.clone();
            let mut reads = false;
            for (position, definition) in definitions.iter().enumerate() {
                // A later definition of the name hides an earlier one.
                stats.retain(|name| *name != definition.name);
                durations.retain(|(name, _)| *name != definition.name);
                aliases.retain(|(name, ..)| *name != definition.name);
                functions.retain(|name| *name != definition.name);
                let is_constant = matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty());
                if is_constant && is_stats(&definition.body, &[], aliases) {
                    stats.push(definition.name.clone());
                } else if is_constant
                    && let Some(bound) = get_duration_bound(
                        &definition.body,
                        environment,
                        stats,
                        durations,
                        aliases,
                        0,
                    )
                {
                    durations.push((definition.name.clone(), bound));
                } else if let DefinitionKind::Operator { params, .. } = &definition.kind
                    && !params.is_empty()
                    && params.iter().all(|param| param.arity == 0)
                    && let Some(bound) = {
                        // Its parameters stand for naturals up to `PARAMETER_BOUND`, which its
                        // applications check.
                        let outer = durations.len();
                        durations.extend(
                            params
                                .iter()
                                .map(|param| (param.name.clone(), PARAMETER_BOUND)),
                        );
                        let bound = get_duration_bound(
                            &definition.body,
                            environment,
                            stats,
                            durations,
                            aliases,
                            0,
                        );
                        durations.truncate(outer);
                        bound
                    }
                {
                    durations.push((definition.name.clone(), bound));
                } else if is_final
                    && let DefinitionKind::Function { bounds } = &definition.kind
                    && is_filled_domain(bounds, &definition.body, &|operand: &Expression| {
                        is_duration_read(operand, environment, stats, durations, aliases, 0)
                    })
                {
                    // A function whose domain TLC builds alike for every duration: its DOMAIN
                    // compared with `{}` reads nothing, and any other use of it does.
                    functions.push(definition.name.clone());
                } else if !may_name(
                    &(definitions[position + 1..].iter())
                        .map(|later| &*later.body)
                        .chain(definitions[position + 1..].iter().flat_map(
                            |later| match &later.kind {
                                DefinitionKind::Function { bounds } => {
                                    bounds.iter().map(|bound| &*bound.set).collect()
                                }
                                DefinitionKind::Operator { .. } => Vec::new(),
                            },
                        ))
                        .chain([&**body])
                        .collect::<Vec<_>>(),
                    &definition.name,
                ) {
                    // TLC never evaluates it.
                } else if let DefinitionKind::Operator { params, .. } = &definition.kind
                    && let Some(position) = get_tlc_get_alias(definition, environment)
                {
                    // A call of it is walked as one of `TLCGet`.
                    aliases.push((definition.name.clone(), position, params.len()));
                } else {
                    if let DefinitionKind::Function { bounds } = &definition.kind {
                        for bound in bounds {
                            reads |= may_read_duration(
                                &bound.set,
                                environment,
                                is_final,
                                stats,
                                durations,
                                aliases,
                                functions,
                                seen,
                            );
                        }
                    }
                    reads |= may_read_duration(
                        &definition.body,
                        environment,
                        is_final,
                        stats,
                        durations,
                        aliases,
                        functions,
                        seen,
                    );
                }
            }
            reads |= may_read_duration(
                body,
                environment,
                is_final,
                stats,
                durations,
                aliases,
                functions,
                seen,
            );
            *stats = outer;
            *durations = outer_durations;
            *aliases = outer_aliases;
            *functions = outer_functions;
            reads
        }
        _ => {
            if let ExpressionKind::Identifier { .. } | ExpressionKind::Apply { .. } =
                &expression.kind
                && let Some(key) = expression.reference()
            {
                let key = environment.substitutions.get(&key).cloned().unwrap_or(key);
                if let Some(definition) = environment.definitions.get(&key)
                    && seen.insert(Rc::as_ptr(definition) as usize)
                    && may_read_duration(
                        &definition.body,
                        environment,
                        is_final,
                        &mut Vec::new(),
                        &mut Vec::new(),
                        &mut Vec::new(),
                        &mut Vec::new(),
                        seen,
                    )
                {
                    return true;
                }
                // TLC binds an argument of an operator the spec defines to a `LazyValue`
                // (`getOpContext`), which it computes only where the body names the parameter,
                // so an argument of a parameter the body never names reads nothing (`a >= b ==
                // FALSE`).
                if is_final
                    && let ExpressionKind::Apply { args, .. } = &expression.kind
                    && !expression.is_locally_resolved()
                    && !environment.substitutions.contains_key(&key)
                    && !(environment.operator_objects.method_aliases).contains_key(&key)
                    && let Some(definition) = environment.definitions.get(&key)
                    && let DefinitionKind::Operator { params, .. } = &definition.kind
                    && params.len() == args.len()
                {
                    return params.iter().zip(args).any(|(param, arg)| {
                        (param.arity != 0 || may_name(&[&definition.body], &param.name))
                            && may_read_duration(
                                arg,
                                environment,
                                is_final,
                                stats,
                                durations,
                                aliases,
                                functions,
                                seen,
                            )
                    });
                }
            }
            expression.children().iter().any(|child| {
                may_read_duration(
                    child,
                    environment,
                    is_final,
                    stats,
                    durations,
                    aliases,
                    functions,
                    seen,
                )
            })
        }
    }
}

/// Whether evaluating an expression may read a value of `TLCGet("revision")` (`TLCGetSet`'s
/// REVISION, the build of TLC's jar): a `TLCGet` of it other than as the operand of DOMAIN, of a
/// key that isn't a literal, or `TLCGet` given as an operator's argument.
fn may_read_revision(expression: &Expression, environment: &Environment) -> bool {
    let is_revision = |expression: &Expression| {
        get_tlc_get_index(expression, environment, &[]).is_some_and(
            |index| matches!(&index.kind, ExpressionKind::String { value } if &**value == "revision"),
        )
    };
    match &expression.kind {
        ExpressionKind::Apply { operator, args, .. }
            if &**operator == "DOMAIN" && args.len() == 1 && is_revision(&args[0]) =>
        {
            false
        }
        ExpressionKind::Apply { args, .. }
            if let Some(index) = get_tlc_get_index(expression, environment, &[]) =>
        {
            match &index.kind {
                ExpressionKind::String { value } if &**value == "revision" => true,
                ExpressionKind::String { .. } | ExpressionKind::Number { .. } => {
                    args.iter().any(|arg| may_read_revision(arg, environment))
                }
                _ => true,
            }
        }
        ExpressionKind::Identifier { .. } | ExpressionKind::OperatorReference { .. }
            if expression.reference().is_some_and(|key| {
                &*key == "TLCGet" && !environment.definitions.contains_key("TLCGet")
            }) =>
        {
            true
        }
        _ => expression
            .children()
            .iter()
            .any(|child| may_read_revision(child, environment)),
    }
}

/// Whether nothing the spec writes may read what of TLC's run only TLC knows: the time it has run,
/// through `TLCGet("stats")` and `TLCGet("duration")` (`may_read_duration`), and its build,
/// through `TLCGet("revision")` (`may_read_revision`). Every definition counts, named or not, and
/// every assumption.
fn are_run_unknowns_unread(environment: &Environment) -> bool {
    let mut seen = FastSet::default();
    let mut reads = |expression: &Expression| {
        may_read_duration(
            expression,
            environment,
            false,
            &mut Vec::new(),
            &mut Vec::new(),
            &mut Vec::new(),
            &mut Vec::new(),
            &mut seen,
        ) || may_read_revision(expression, environment)
    };
    let definitions_read = environment.definitions.values().any(|definition| {
        let bounds_read = match &definition.kind {
            DefinitionKind::Function { bounds } => bounds.iter().any(|bound| reads(&bound.set)),
            DefinitionKind::Operator { .. } => false,
        };
        bounds_read || reads(&definition.body)
    });
    !definitions_read
        && !environment
            .assumptions
            .iter()
            .any(|assumption| reads(&assumption.expression))
}

/// An image without the parentheses outside its strings, where they are balanced.
fn remove_parentheses(image: &str) -> Option<String> {
    let mut depth = 0usize;
    let mut in_string = false;
    let mut removed = String::with_capacity(image.len());
    for character in image.chars() {
        if character == '"' {
            in_string = !in_string;
        }
        match character {
            '(' if !in_string => depth += 1,
            ')' if !in_string => depth = depth.checked_sub(1)?,
            _ => removed.push(character),
        }
    }
    (depth == 0).then_some(removed)
}

/// A prefix operator written as a word, which takes its operand without parentheses.
fn is_prefix_word(name: &str) -> bool {
    matches!(
        name,
        "SUBSET" | "UNION" | "DOMAIN" | "ENABLED" | "UNCHANGED"
    )
}

/// The byte offset in `text` of a node's 1-based line and column, on a line of ASCII only, where
/// a column counts characters.
fn get_text_offset(text: &str, line: u32, column: u32) -> Option<usize> {
    let mut offset = 0;
    for (index, written) in text.split('\n').enumerate() {
        if index + 1 == line as usize {
            let column = column as usize;
            if !written.is_ascii()
                || written.contains('\r')
                || column == 0
                || column > written.len()
            {
                return None;
            }
            return Some(offset + column - 1);
        }
        offset += written.len() + 1;
    }
    None
}

/// The texts TLC ranks, which come first in the IR's table, in rank order.
pub struct RankedTexts<'a> {
    pub texts: &'a [Rc<str>],
    pub ranks: FastMap<Rc<str>, u32>,
    /// The units of each ranked text with a lone surrogate, by the name it ranks by.
    pub wide: &'a FastMap<Rc<str>, Box<[u16]>>,
}

// Lookup uses the receiver's keys, then peeks once at the returned OpDef's body.
fn startup_receiver_body(
    definition: &Rc<Definition>,
    environment: &Environment,
) -> Option<Rc<Definition>> {
    let aliases: Vec<Name> = environment
        .definitions
        .iter()
        .filter(|(_, value)| Rc::ptr_eq(value, definition))
        .map(|(key, _)| key.clone())
        .collect();
    if aliases.iter().any(|key| {
        environment.constants.contains_key(key) || environment.operator_constants.contains_key(key)
    }) {
        return None;
    }
    if let Some(target) = aliases
        .iter()
        .find_map(|key| environment.substitutions.get(key))
    {
        return environment.definitions.get(target).cloned();
    }
    Some(definition.clone())
}

fn reaches_missing_operator_body(definition: &Rc<Definition>, environment: &Environment) -> bool {
    let mut definitions = vec![definition.clone()];
    let mut seen_definitions = FastSet::default();
    let mut seen_nodes = FastSet::default();
    while let Some(mut definition) = definitions.pop() {
        let Some(actual) = startup_receiver_body(&definition, environment) else {
            continue;
        };
        definition = actual;
        if !seen_definitions.insert(Rc::as_ptr(&definition) as usize) {
            continue;
        }
        if environment
            .missing_operator_bodies
            .contains(&(Rc::as_ptr(&definition) as usize))
        {
            return true;
        }
        let mut pending = vec![definition.body.clone()];
        while let Some(node) = pending.pop() {
            if !seen_nodes.insert(Rc::as_ptr(&node) as usize) {
                continue;
            }
            if matches!(
                node.kind,
                ExpressionKind::Lambda { .. } | ExpressionKind::OperatorReference { .. }
            ) {
                continue;
            }
            if !node.resolved.is_local.get()
                && let Some(name) = node.reference()
                && !environment.constants.contains_key(&name)
                && !environment.operator_constants.contains_key(&name)
                && let Some(target) = environment.definitions.get(&name)
            {
                definitions.push(target.clone());
            }
            pending.extend(node.children());
        }
    }
    false
}

/// `isStartupDefinition`: a constant definition without parameters the configuration doesn't
/// replace.
/// Why the front end stops at a constant definition or predicate that names a name spelled as a
/// variable (`Lowering::write_startup`).
const VARIABLE_SPELLING: &str =
    "a constant definition TLC takes for a variable's, naming a name spelled as a variable";

pub fn is_startup_definition(
    definition: &Rc<Definition>,
    environment: &Environment,
    facts: &DefinitionFacts,
) -> bool {
    let is_nullary = match &definition.kind {
        DefinitionKind::Operator { params, .. } => params.is_empty(),
        DefinitionKind::Function { .. } => true,
    };
    is_nullary
        && !environment.constants.contains_key(&definition.name)
        && !environment.substitutions.contains_key(&definition.name)
        && facts.is_constant_level(definition, environment)
}

/// Whether TLC holds a definition as the value of its literal body (`IrDefinition::LITERAL`):
/// `lookup` finds the literal's value, through the SubstInNode of an INSTANCE's copy too, so
/// `processConstantDefns` doesn't compute the definition.
fn is_held_literal(definition: &Rc<Definition>, environment: &Environment) -> bool {
    // A theorem's or an assumption's name, which has no body range, isn't one of TLC's definitions.
    matches!(
        definition.kind,
        DefinitionKind::Operator {
            body_range: Some(_),
            ..
        }
    ) && matches!(
        environment.get_written(definition).body.kind,
        ExpressionKind::Number { .. } | ExpressionKind::String { .. }
    ) && !environment
        .substitutes_for_definitions
        .contains(&definition.name)
}

/// The builtins whose effects show each time TLC evaluates them again: they print, set a
/// register, draw at random, or read the clock or TLC's registers. Reading a file or the process's
/// environment again reads the same.
pub(crate) const SHOWN_EFFECTS: [&str; 10] = [
    "Print",
    "PrintT",
    "TLCSet",
    "TLCGet",
    "JavaTime",
    "RandomElement",
    "RandomSubset",
    "RandomSetOfSubsets",
    "RandomSubsetSet",
    "TestRandomSetOfSubsets",
];

/// Whether evaluating the definition again can show, as by printing twice, other than through
/// `cached`, whose value TLC keeps.
fn reaches_shown_effect(
    definition: &Rc<Definition>,
    environment: &Environment,
    cached: Option<&Rc<Definition>>,
) -> bool {
    reaches_effect(definition, environment, cached, &SHOWN_EFFECTS, false)
}

/// The children of an expression its evaluation may reach: TLC computes the branch a constant IF
/// takes alone, and an operator's argument only where the operator reads its parameter
/// (`LazyValue`), which the evaluator follows where it can compute the condition.
fn get_reached_children(
    expression: &Expr,
    environment: &Environment,
    evaluator: Option<&crate::eval::Evaluator>,
) -> Vec<Expr> {
    match &expression.kind {
        ExpressionKind::If {
            condition,
            consequent,
            alternative,
        } => match evaluator.map(|evaluator| evaluator.evaluate(condition, None)) {
            Some(Ok(ConfigValue::Boolean(holds))) => vec![
                condition.clone(),
                if holds { consequent } else { alternative }.clone(),
            ],
            _ => expression.children(),
        },
        // TLC evaluates a junction's operands in order up to the first that decides it, and a
        // CASE's guards in order up to the first that holds.
        ExpressionKind::Junction {
            is_and, operands, ..
        } => {
            let constant = |operand: &Expr| match evaluator
                .map(|evaluator| evaluator.evaluate(operand, None))
            {
                Some(Ok(ConfigValue::Boolean(holds))) => Some(holds),
                _ => None,
            };
            let decided = operands
                .iter()
                .position(|operand| constant(operand) == Some(!*is_and));
            operands[..decided.map_or(operands.len(), |position| position + 1)].to_vec()
        }
        ExpressionKind::Case { arms, other } => {
            let mut reached = Vec::new();
            for arm in arms {
                reached.push(arm.condition.clone());
                match evaluator.map(|evaluator| evaluator.evaluate(&arm.condition, None)) {
                    Some(Ok(ConfigValue::Boolean(true))) => {
                        reached.push(arm.body.clone());
                        return reached;
                    }
                    Some(Ok(ConfigValue::Boolean(false))) => {}
                    _ => reached.push(arm.body.clone()),
                }
            }
            reached.extend(other.iter().cloned());
            reached
        }
        // TLC computes an implication's consequent only where the antecedent holds.
        ExpressionKind::Apply { operator, args, .. }
            if &**operator == "=>"
                && args.len() == 2
                && matches!(
                    evaluator.map(|evaluator| evaluator.evaluate(&args[0], None)),
                    Some(Ok(ConfigValue::Boolean(false)))
                ) =>
        {
            vec![args[0].clone()]
        }
        // TLC computes the body of a binder over an empty set nowhere.
        ExpressionKind::Quantified { bounds, .. }
        | ExpressionKind::SetMap { bounds, .. }
        | ExpressionKind::FunctionConstruction { bounds, .. }
            if bounds.iter().any(|bound| {
                matches!(
                    evaluator.map(|evaluator| evaluator.evaluate(&bound.set, None)),
                    Some(Ok(ConfigValue::Set(elements))) if elements.is_empty()
                )
            }) =>
        {
            bounds.iter().map(|bound| bound.set.clone()).collect()
        }
        ExpressionKind::SetFilter { bound, .. }
            if matches!(
                evaluator.map(|evaluator| evaluator.evaluate(&bound.set, None)),
                Some(Ok(ConfigValue::Set(elements))) if elements.is_empty()
            ) =>
        {
            vec![bound.set.clone()]
        }
        // TLC computes a LET's definition only where its body reads it.
        ExpressionKind::Let {
            definitions,
            instances: None,
            body,
            ..
        } => {
            let mut reached = vec![body.clone()];
            let mut is_reached = vec![false; definitions.len()];
            let mut pending = vec![body.clone()];
            while let Some(inner) = pending.pop() {
                if let Some(reference) = inner.reference()
                    && let Some(position) = definitions
                        .iter()
                        .position(|definition| definition.name == reference)
                    && !is_reached[position]
                {
                    is_reached[position] = true;
                    let definition = &definitions[position];
                    let parts: Vec<Expr> = match &definition.kind {
                        DefinitionKind::Function { bounds } => bounds
                            .iter()
                            .map(|bound| bound.set.clone())
                            .chain([definition.body.clone()])
                            .collect(),
                        DefinitionKind::Operator { .. } => vec![definition.body.clone()],
                    };
                    reached.extend(parts.iter().cloned());
                    pending.extend(parts);
                }
                pending.extend(inner.children());
            }
            reached
        }
        ExpressionKind::Apply { args, .. } if !expression.is_locally_resolved() => {
            let callee = expression.reference().and_then(|name| {
                let target = environment.substitutions.get(&name).unwrap_or(&name);
                environment.definitions.get(target).cloned()
            });
            let Some(callee) = callee else {
                return expression.children();
            };
            let DefinitionKind::Operator { params, .. } = &callee.kind else {
                return expression.children();
            };
            let mut is_read_param = vec![false; params.len()];
            let mut pending = vec![callee.body.clone()];
            while let Some(inner) = pending.pop() {
                if inner.is_locally_resolved()
                    && let Some(reference) = inner.reference()
                    && let Some(position) = params.iter().position(|param| param.name == reference)
                {
                    is_read_param[position] = true;
                }
                // An application within keeps its arguments, so a recursive operator ends.
                pending.extend(match &inner.kind {
                    ExpressionKind::Apply { .. } => inner.children(),
                    _ => get_reached_children(&inner, environment, evaluator),
                });
            }
            args.iter()
                .enumerate()
                .filter(|(position, _)| is_read_param.get(*position).is_none_or(|is_read| *is_read))
                .map(|(_, argument)| argument.clone())
                .collect()
        }
        _ => expression.children(),
    }
}

/// The builtins that made a definition impure before the engine checked TLCExt's
/// (`IMPURE_BUILTINS` in `dependencies.rs`).
const EARLIER_IMPURE_BUILTINS: [&str; 7] = [
    "Print",
    "PrintT",
    "Assert",
    "JavaTime",
    "RandomElement",
    "TLCGet",
    "TLCSet",
];

/// The TLCExt builtins the engine checks, which it declined before.
const NEW_BUILTINS: [&str; 4] = [
    "AssertEq",
    "TLCGetOrDefault",
    "TLCGetAndSet",
    "PickSuccessor",
];

/// Of `NEW_BUILTINS`, those a constant definition the engine computes at startup may not reach:
/// AssertEq, which TLCExt defines in TLA+ by PrintT, prints there as PrintT does, and
/// TLCGetOrDefault and TLCGetAndSet read and write TLC's registers there as TLCGet and TLCSet do.
const STARTUP_DECLINED_BUILTINS: [&str; 1] = ["PickSuccessor"];

/// Whether a definition reaches one of these builtins, past `cached`, and, with
/// `is_past_kept`, outside a TLCEval, whose value TLC keeps.
pub(crate) fn reaches_effect(
    definition: &Rc<Definition>,
    environment: &Environment,
    cached: Option<&Rc<Definition>>,
    effects: &[&str],
    is_past_kept: bool,
) -> bool {
    Reach::effects(environment, cached, effects, is_past_kept).definition(definition)
}

/// What a walk of `Reach` does at an expression: it finds there what it looks for, passes the
/// expression by with its parts, or follows the definition the expression names and then these
/// parts.
enum Visit {
    Found,
    Skip,
    Follow(Vec<Expr>),
}

/// A walk for whether an expression reaches something, through the definitions it names, where
/// what the walk does at an expression depends on the expression alone, so that a definition
/// reaches it or doesn't wherever a walk meets it. It keeps what each walk learns of the
/// definitions it met: those on the way to where it found it reach it, and every one a walk met
/// that ended without finding it doesn't. So walks from each definition of a long chain of them
/// take the chain once in all, not once each.
pub(crate) struct Reach<'a> {
    environment: &'a Environment,
    visit: Box<dyn Fn(&Expr) -> Visit + 'a>,
    /// The definition the walk doesn't enter, as `reaches_effect`'s `cached`.
    excluded: Option<usize>,
    reaches: RefCell<FastMap<usize, bool>>,
}

impl<'a> Reach<'a> {
    /// `reaches_in`'s walk, for these builtins.
    fn builtins(
        environment: &'a Environment,
        builtins: &'a [&'a str],
        evaluator: Option<&'a crate::eval::Evaluator>,
    ) -> Self {
        Self::new(environment, None, move |expression| {
            if let Some(name) = expression.reference()
                && !expression.is_locally_resolved()
                // TLCExt defines these in TLA+ too.
                && builtins.contains(&&*name)
            {
                return Visit::Found;
            }
            Visit::Follow(get_reached_children(expression, environment, evaluator))
        })
    }

    /// `reaches_effect`'s walk, for these builtins.
    pub(crate) fn effects(
        environment: &'a Environment,
        cached: Option<&Rc<Definition>>,
        effects: &'a [&'a str],
        is_past_kept: bool,
    ) -> Self {
        let excluded = cached.map(|cached| Rc::as_ptr(cached) as usize);
        Self::new(environment, excluded, move |expression| {
            // TLCExt's AssertEq prints only where its arguments differ, which two equal literals
            // never do.
            if let ExpressionKind::Apply { operator, args, .. } = &expression.kind
                && &**operator == "AssertEq"
                && !expression.is_locally_resolved()
                && !environment.definitions.contains_key("AssertEq")
                && let [left, right] = args.as_slice()
                && match (&left.kind, &right.kind) {
                    (
                        ExpressionKind::Number { value: left, .. },
                        ExpressionKind::Number { value: right, .. },
                    ) => left == right,
                    (
                        ExpressionKind::String { value: left },
                        ExpressionKind::String { value: right },
                    ) => left == right,
                    _ => false,
                }
            {
                return Visit::Skip;
            }
            if let Some(name) = expression.reference()
                && !expression.is_locally_resolved()
                && effects.contains(&&*name)
                && !environment.definitions.contains_key(&name)
            {
                return Visit::Found;
            }
            if is_past_kept
                && matches!(&expression.kind, ExpressionKind::Apply { operator, .. } if &**operator == "TLCEval")
            {
                return Visit::Follow(Vec::new());
            }
            Visit::Follow(get_reached_children(expression, environment, None))
        })
    }

    /// The walk for whether an expression may apply IOUtils's Serialize, however its arguments
    /// are written (`may_write_text`).
    fn serialize(
        environment: &'a Environment,
        evaluator: Option<&'a crate::eval::Evaluator>,
    ) -> Self {
        Self::new(environment, None, move |expression| {
            if let Some(name) = expression.reference()
                && !expression.is_locally_resolved()
            {
                let target = environment.substitutions.get(&name).unwrap_or(&name);
                let operator = target.split('@').next().unwrap_or_default();
                if operator == "Serialize" || operator.ends_with("!Serialize") {
                    return Visit::Found;
                }
            }
            Visit::Follow(get_reached_children(expression, environment, evaluator))
        })
    }

    fn new(
        environment: &'a Environment,
        excluded: Option<usize>,
        visit: impl Fn(&Expr) -> Visit + 'a,
    ) -> Self {
        Self {
            environment,
            visit: Box::new(visit),
            excluded,
            reaches: RefCell::default(),
        }
    }

    pub(crate) fn definition(&self, definition: &Rc<Definition>) -> bool {
        self.expression(&definition.body)
    }

    fn expression(&self, expression: &Expr) -> bool {
        let mut reaches = self.reaches.borrow_mut();
        let mut seen: FastSet<usize> = self.excluded.into_iter().collect();
        // The definition the walk met each definition in, or None for the expression it started
        // from: a path from there to every definition it met.
        let mut met_in: FastMap<usize, Option<usize>> = FastMap::default();
        // Every definition on the path to where the walk found it reaches it.
        fn found(
            reaches: &mut FastMap<usize, bool>,
            met_in: &FastMap<usize, Option<usize>>,
            mut definition: Option<usize>,
        ) -> bool {
            while let Some(address) = definition {
                reaches.insert(address, true);
                definition = met_in[&address];
            }
            true
        }
        let mut pending: Vec<(Expr, Option<usize>)> = vec![(expression.clone(), None)];
        while let Some((expression, within)) = pending.pop() {
            let children = match (self.visit)(&expression) {
                Visit::Found => return found(&mut reaches, &met_in, within),
                Visit::Skip => continue,
                Visit::Follow(children) => children,
            };
            if let Some(name) = expression.reference()
                && !expression.is_locally_resolved()
            {
                let target = self.environment.substitutions.get(&name).unwrap_or(&name);
                if let Some(callee) = self.environment.definitions.get(target) {
                    let address = Rc::as_ptr(callee) as usize;
                    match reaches.get(&address) {
                        Some(true) => return found(&mut reaches, &met_in, within),
                        Some(false) => {}
                        None => {
                            if seen.insert(address) {
                                met_in.insert(address, within);
                                pending.push((callee.body.clone(), Some(address)));
                            }
                        }
                    }
                }
            }
            pending.extend(children.into_iter().map(|child| (child, within)));
        }
        for address in seen {
            if Some(address) != self.excluded {
                reaches.insert(address, false);
            }
        }
        false
    }
}

/// Whether evaluating a definition may recurse, through a RECURSIVE operator or a recursive
/// function, its own or one it reaches, as a recursion without end overflows TLC's stack.
fn reaches_recursion(definition: &Rc<Definition>, environment: &Environment) -> bool {
    let is_recursive = |definition: &Definition| {
        definition.is_recursive || definition.is_self_referential.get() == Some(true)
    };
    if is_recursive(definition) {
        return true;
    }
    let mut seen: FastSet<usize> = [Rc::as_ptr(definition) as usize].into_iter().collect();
    let mut pending = vec![definition.body.clone()];
    while let Some(expression) = pending.pop() {
        match &expression.kind {
            ExpressionKind::FunctionConstruction { .. }
                if expression.resolved.is_recursive.get() =>
            {
                return true;
            }
            ExpressionKind::Let {
                definitions,
                recursive,
                ..
            } if !recursive.is_empty()
                || definitions
                    .iter()
                    .any(|definition| is_recursive(definition)) =>
            {
                return true;
            }
            _ => {}
        }
        if let Some(name) = expression.reference()
            && !expression.is_locally_resolved()
        {
            let target = environment.substitutions.get(&name).unwrap_or(&name);
            if let Some(callee) = environment.definitions.get(target)
                && seen.insert(Rc::as_ptr(callee) as usize)
            {
                if is_recursive(callee) {
                    return true;
                }
                pending.push(callee.body.clone());
            }
        }
        pending.extend(expression.children());
    }
    false
}

/// Whether the configuration names a definition one of its roles reads.
pub(crate) fn is_read_by_config(
    config: &crate::config::ModelConfig,
    is_named: &dyn Fn(&str) -> bool,
) -> bool {
    [
        &config.invariants,
        &config.properties,
        &config.constraints,
        &config.action_constraints,
        &config.postconditions,
        &config.possible,
    ]
    .into_iter()
    .flatten()
    .chain(
        [
            &config.init,
            &config.next,
            &config.specification,
            &config.symmetry,
            &config.view,
            &config.periodic,
            &config.rl_reward,
            &config.alias,
        ]
        .into_iter()
        .flatten(),
    )
    .any(|named| is_named(named))
}

/// Whether the model reads a definition by its name: the configuration names it, or a
/// definition or an assumption refers to it where its evaluation may reach.
fn is_read(
    name: &str,
    config: &crate::config::ModelConfig,
    environment: &Environment,
    evaluator: Option<&crate::eval::Evaluator>,
) -> bool {
    is_read_but(name, config, environment, evaluator, &|_| false)
}

/// The names the definitions and assumptions refer to where their evaluation may reach, which
/// `is_read` walks the spec for: one walk for every name it asks of.
fn get_referred_names(
    environment: &Environment,
    evaluator: Option<&crate::eval::Evaluator>,
) -> FastSet<Name> {
    let mut pending: Vec<Expr> = environment
        .definitions
        .values()
        .map(|definition| definition.body.clone())
        .chain(
            environment
                .assumptions
                .iter()
                .map(|assumption| assumption.expression.clone()),
        )
        .collect();
    let mut referred = FastSet::default();
    while let Some(expression) = pending.pop() {
        if !expression.is_locally_resolved()
            && let Some(reference) = expression.reference()
        {
            referred.insert(reference);
        }
        pending.extend(get_reached_children(&expression, environment, evaluator));
    }
    referred
}

/// `is_read`, leaving out the bodies of the definitions `is_skipped` names.
fn is_read_but(
    name: &str,
    config: &crate::config::ModelConfig,
    environment: &Environment,
    evaluator: Option<&crate::eval::Evaluator>,
    is_skipped: &dyn Fn(&Definition) -> bool,
) -> bool {
    let named = is_read_by_config(config, &|named| named == name);
    let mut pending: Vec<Expr> = environment
        .definitions
        .values()
        .filter(|definition| !is_skipped(definition))
        .map(|definition| definition.body.clone())
        .chain(
            environment
                .assumptions
                .iter()
                .map(|assumption| assumption.expression.clone()),
        )
        .collect();
    let mut is_referred = false;
    while let Some(expression) = pending.pop() {
        is_referred |= !expression.is_locally_resolved()
            && expression
                .reference()
                .is_some_and(|reference| &*reference == name);
        pending.extend(get_reached_children(&expression, environment, evaluator));
    }
    named || is_referred
}

/// The walk for whether an expression reaches TLCSet, through the definitions it applies, but
/// where it is of the literal key "exit" or "pause" and a literal value other than TRUE, which
/// sets nothing wherever TLC computes it.
fn reaches_register_write<'a>(
    environment: &'a Environment,
    evaluator: Option<&'a crate::eval::Evaluator>,
) -> Reach<'a> {
    Reach::new(environment, None, move |expression| {
        if let Some(name) = expression.reference()
            && !expression.is_locally_resolved()
            && &*name == "TLCSet"
        {
            let is_inert = match &expression.kind {
                ExpressionKind::Apply { args, .. } => match args.as_slice() {
                    [key, value] => {
                        matches!(&key.kind, ExpressionKind::String { value, .. } if matches!(&**value, "exit" | "pause"))
                            && is_plain_literal(value, environment)
                            && !matches!(&value.kind, ExpressionKind::Identifier { name, .. } if &**name == "TRUE")
                    }
                    _ => false,
                },
                _ => false,
            };
            if !is_inert {
                return Visit::Found;
            }
        }
        Visit::Follow(get_reached_children(expression, environment, evaluator))
    })
}

/// The system properties a builtin of a key, TLCSet or TLCGet, names where these expressions
/// reach it, through the definitions they apply: the names of its literal "-D" keys, or `None`
/// where a key isn't a literal string and may name any. Of constant expressions, which TLC
/// computes as it starts, a junction's operand without effects that fails, as `1 \div 0 = 1`,
/// stops TLC there, before the operands after it.
fn reached_property_keys(
    roots: Vec<Expr>,
    environment: &Environment,
    builtin: &str,
    evaluator: Option<&crate::eval::Evaluator>,
    is_constant: bool,
) -> Option<Vec<Rc<str>>> {
    let mut keys = Vec::new();
    let mut seen = FastSet::default();
    let mut pending = roots;
    // One walk for every operand it asks of, which keeps what it learns of the definitions.
    let reaches_shown = Reach::builtins(environment, &SHOWN_EFFECTS, None);
    while let Some(expression) = pending.pop() {
        if let Some(name) = expression.reference()
            && !expression.is_locally_resolved()
        {
            if &*name == builtin
                && environment.builtins.contains_key(builtin)
                && !environment.definitions.contains_key(builtin)
            {
                match &expression.kind {
                    ExpressionKind::Apply { args, .. } => match args.first().map(|key| &key.kind) {
                        Some(ExpressionKind::String { value, .. }) => {
                            if let Some(property) = value.strip_prefix("-D") {
                                keys.push(Rc::from(property));
                            }
                        }
                        Some(ExpressionKind::Number { .. }) => {}
                        _ => return None,
                    },
                    // The builtin passed as an argument may be applied to any key.
                    _ => return None,
                }
            }
            let target = environment.substitutions.get(&name).unwrap_or(&name);
            if let Some(callee) = environment.definitions.get(target)
                && seen.insert(Rc::as_ptr(callee) as usize)
            {
                pending.push(callee.body.clone());
            }
        }
        let mut children = get_reached_children(&expression, environment, evaluator);
        if is_constant
            && let ExpressionKind::Junction { .. } = &expression.kind
            && let Some(evaluator) = evaluator
            && let Some(failing) = children.iter().position(|operand| {
                !reaches_shown.expression(operand)
                    // Not a name the evaluator has no value for here, as an operator's
                    // parameter, which is no failure of TLC's.
                    && matches!(
                        evaluator.evaluate(operand, None),
                        Err(FrontError::Evaluation(message))
                            if !message.starts_with("In evaluation, the identifier")
                    )
            })
        {
            children.truncate(failing + 1);
        }
        pending.extend(children);
    }
    Some(keys)
}

/// Whether an expression reaches one of these builtins, through the definitions it applies.
pub(crate) fn reaches_in(
    expression: &Expr,
    environment: &Environment,
    builtins: &[&str],
    evaluator: Option<&crate::eval::Evaluator>,
) -> bool {
    Reach::builtins(environment, builtins, evaluator).expression(expression)
}

/// The expressions the names local to a definition stand for, where `may_write_text` reached
/// it: the parameters an application gives its arguments, and the definitions of the LETs it is
/// in that take none, each with the names its own expression reads. SANY lets no name local to
/// a definition hide another, so the innermost of a name is the one it reads.
#[derive(Clone, Default)]
struct TextScope(Option<Rc<(Name, Expr, TextScope, TextScope)>>);

impl TextScope {
    fn bind(&self, name: Name, expression: Expr, scope: TextScope) -> TextScope {
        TextScope(Some(Rc::new((name, expression, scope, self.clone()))))
    }

    fn lookup(&self, name: &str) -> Option<(Expr, TextScope)> {
        let mut current = self.0.as_ref();
        while let Some(entry) = current {
            let (bound, expression, scope, parent) = &**entry;
            if &**bound == name {
                return Some((expression.clone(), scope.clone()));
            }
            current = parent.0.as_ref();
        }
        None
    }
}

/// Whether an expression, through the definitions it names and the parts TLC may evaluate
/// (`get_reached_children`), may apply IOUtils's Serialize where `Json.textSerialize` may write
/// its file, or pass the operator on: anywhere but where the arguments as written fail, or name a
/// format other than NDJSON, before the file opens.
fn may_write_text(
    expression: &Expr,
    environment: &Environment,
    evaluator: Option<&crate::eval::Evaluator>,
    reaches_serialize: &Reach,
) -> bool {
    // Only where it may apply Serialize at all, which a walk that keeps what it learns tells.
    if !reaches_serialize.expression(expression) {
        return false;
    }
    let mut seen = FastSet::default();
    let mut pending = vec![(expression.clone(), TextScope::default())];
    while let Some((expression, scope)) = pending.pop() {
        if let Some(name) = expression.reference()
            && !expression.is_locally_resolved()
        {
            let target = environment.substitutions.get(&name).unwrap_or(&name);
            // The key of a definition names its module after an `@`.
            let operator = target.split('@').next().unwrap_or_default();
            if (operator == "Serialize" || operator.ends_with("!Serialize"))
                && !matches!(&expression.kind, ExpressionKind::Apply { args, .. }
                    if fails_before_text_write(args, &scope, environment, evaluator))
            {
                return true;
            }
            if let Some(callee) = environment.definitions.get(target) {
                // An operator's body reads its parameters as the arguments of an application,
                // which it is walked once for.
                let args = match &expression.kind {
                    ExpressionKind::Apply { args, .. } => args.as_slice(),
                    _ => &[],
                };
                let key: Vec<usize> = std::iter::once(Rc::as_ptr(callee) as usize)
                    .chain(args.iter().map(|arg| Rc::as_ptr(arg) as usize))
                    .collect();
                if seen.insert(key) {
                    let mut inner = TextScope::default();
                    if let DefinitionKind::Operator { params, .. } = &callee.kind
                        && params.len() == args.len()
                    {
                        for (param, arg) in params.iter().zip(args) {
                            if param.arity == 0 {
                                inner = inner.bind(param.name.clone(), arg.clone(), scope.clone());
                            }
                        }
                    }
                    pending.push((callee.body.clone(), inner));
                }
            }
        }
        let scope = match &expression.kind {
            ExpressionKind::Let { definitions, .. } => {
                definitions
                    .iter()
                    .fold(scope, |scope, definition| match &definition.kind {
                        DefinitionKind::Operator { params, .. } if params.is_empty() => {
                            let outer = scope.clone();
                            scope.bind(definition.name.clone(), definition.body.clone(), outer)
                        }
                        _ => scope,
                    })
            }
            _ => scope,
        };
        pending.extend(
            get_reached_children(&expression, environment, evaluator)
                .into_iter()
                .map(|child| (child, scope.clone())),
        );
    }
    false
}

/// The expression a name stands for, through the names local to a definition and the constant
/// definitions without parameters, or the expression: a name the configuration doesn't give a
/// value or substitute.
fn get_constant_body(expression: &Expr, scope: &TextScope, environment: &Environment) -> Expr {
    let mut expression = expression.clone();
    let mut scope = scope.clone();
    let mut seen = FastSet::default();
    while let ExpressionKind::Identifier { .. } = &expression.kind
        && let Some(name) = expression.reference()
        && seen.insert(Rc::as_ptr(&expression) as usize)
    {
        if expression.is_locally_resolved() {
            let Some((bound, outer)) = scope.lookup(&name) else {
                break;
            };
            expression = bound;
            scope = outer;
            continue;
        }
        if environment.constants.contains_key(&name)
            || environment.substitutions.contains_key(&name)
        {
            break;
        }
        let Some(definition) = environment.definitions.get(&name) else {
            break;
        };
        if !matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty())
        {
            break;
        }
        expression = definition.body.clone();
        scope = TextScope::default();
    }
    expression
}

/// Whether `Json.textSerialize` of these arguments as written fails, or evaluates the
/// definition, before it opens a file: options that aren't a record, or have no format, or a
/// format that isn't a string or is a string other than "NDJSON"; with NDJSON, a payload or a
/// file that is a number, an open option `StandardOpenOption` doesn't name, a charset the pinned
/// JVM doesn't know, or a file `Files.newBufferedWriter` can't open as TLC starts: in a directory
/// that isn't there (`NoSuchFileException`), or not there without CREATE or CREATE_NEW.
///
/// The options, and their format, may be a constant definition's name, which stands for its
/// body. `textSerialize` computes the options first and casts the format before anything else,
/// so options or a format the front end computes to a failure (TLC's own, or a cast's) fail
/// there too, and an empty tuple is TLC's empty record (`TupleValue.toRcd`), with no format.
fn fails_before_text_write(
    args: &[Expr],
    scope: &TextScope,
    environment: &Environment,
    evaluator: Option<&crate::eval::Evaluator>,
) -> bool {
    let [payload, path, options] = args else {
        return true;
    };
    let fails = |expression: &Expr| {
        evaluator.is_some_and(|evaluator| {
            matches!(
                evaluator.evaluate(expression, None),
                Err(FrontError::Evaluation(_))
            )
        })
    };
    let options = get_constant_body(options, scope, environment);
    let fields = match &options.kind {
        ExpressionKind::Number { .. } | ExpressionKind::String { .. } => return true,
        ExpressionKind::Tuple(elements) if elements.is_empty() => return true,
        ExpressionKind::Record {
            is_set: false,
            fields,
        } => fields,
        // Options the front end computes: a record, as TLC's function of strings is
        // (`FcnRcdValue.toRcd`), whose format isn't "NDJSON" fails at the format.
        _ => {
            return match evaluator.map(|evaluator| evaluator.evaluate(&options, None)) {
                Some(Err(FrontError::Evaluation(_))) => true,
                Some(Ok(ConfigValue::Record(fields))) => !fields.iter().any(|(name, value)| {
                    name == "format"
                        && matches!(value, ConfigValue::String(format) if format == "NDJSON")
                }),
                _ => false,
            };
        }
    };
    // TLC builds the record, each field's value, before it reads the format: a field it computes
    // at once, as arithmetic, an application of a function or a tuple, that fails fails there.
    if fields.iter().any(|field| {
        let is_eager = match &field.value.kind {
            ExpressionKind::Apply { operator, .. } => {
                !field.value.is_locally_resolved()
                    && matches!(&**operator, "+" | "-" | "*" | "\\div" | "%" | "^")
            }
            ExpressionKind::FunctionApplication { .. }
            | ExpressionKind::Tuple(_)
            | ExpressionKind::Choose { .. } => true,
            _ => false,
        };
        is_eager && fails(&field.value)
    }) {
        return true;
    }
    let field = |name: &str| {
        let mut found = fields.iter().filter(|field| &*field.name == name);
        let value = found.next().map(|field| &field.value);
        if found.next().is_some() {
            None
        } else {
            Some(value)
        }
    };
    let Some(format) = field("format") else {
        return false;
    };
    let format = format.map(|format| get_constant_body(format, scope, environment));
    match format.as_ref().map(|format| &format.kind) {
        None | Some(ExpressionKind::Number { .. }) => return true,
        Some(ExpressionKind::String { value }) if &**value != "NDJSON" => return true,
        Some(ExpressionKind::String { .. }) => {}
        _ => return format.is_some_and(|format| fails(&format)),
    }
    if matches!(payload.kind, ExpressionKind::Number { .. })
        || matches!(path.kind, ExpressionKind::Number { .. })
    {
        return true;
    }
    if let Some(Some(open_options)) = field("openOptions")
        && let ExpressionKind::Tuple(names) = &open_options.kind
        && names.iter().any(|name| {
            matches!(&name.kind, ExpressionKind::String { value }
                if !matches!(&**value, "READ" | "WRITE" | "APPEND" | "TRUNCATE_EXISTING"
                    | "CREATE" | "CREATE_NEW" | "DELETE_ON_CLOSE" | "SPARSE" | "SYNC" | "DSYNC"))
        })
    {
        return true;
    }
    if matches!(field("charset"), Some(Some(charset))
        if matches!(&charset.kind, ExpressionKind::String { value }
            if !tla_trace::is_jvm_charset(value)))
    {
        return true;
    }
    let ExpressionKind::String { value: path } = &path.kind else {
        return false;
    };
    let path = std::path::Path::new(&**path);
    if path
        .parent()
        .is_some_and(|parent| !parent.as_os_str().is_empty() && !parent.is_dir())
    {
        return true;
    }
    matches!(field("openOptions"), Some(Some(open_options))
        if matches!(&open_options.kind, ExpressionKind::Tuple(names)
            if !names.is_empty()
                && names.iter().all(|name| matches!(&name.kind,
                    ExpressionKind::String { value } if !matches!(&**value, "CREATE" | "CREATE_NEW")))
                && !path.exists()))
}

/// Whether an expression is a value written out of literals, which TLC computes without any
/// effect or failure: a number, a negated number, a string, a boolean, or a set or a tuple of
/// such values.
fn is_plain_literal(expression: &Expr, environment: &Environment) -> bool {
    match &expression.kind {
        ExpressionKind::Number { .. } | ExpressionKind::String { .. } => true,
        ExpressionKind::SetEnumeration(items) | ExpressionKind::Tuple(items) => {
            items.iter().all(|item| is_plain_literal(item, environment))
        }
        ExpressionKind::Identifier { .. } | ExpressionKind::Apply { .. }
            if !expression.is_locally_resolved() =>
        {
            let Some(name) = expression.reference() else {
                return false;
            };
            if !environment.builtins.contains_key(&name)
                || environment.definitions.contains_key(&name)
            {
                return false;
            }
            match (&*name, &expression.kind) {
                ("TRUE" | "FALSE", ExpressionKind::Identifier { .. }) => true,
                ("-.", ExpressionKind::Apply { args, .. }) => {
                    matches!(args.as_slice(), [number] if matches!(number.kind, ExpressionKind::Number { .. }))
                }
                _ => false,
            }
        }
        _ => false,
    }
}

/// A predicate the configuration names that writes TLCSet, taken branch or not, and reads no
/// variable is constant-level to TLC (TLCSet's Java method has no minimum level), which computes
/// it as it starts and then judges its value (`processConfigInvariants`, `processConfigProps`,
/// `processModelConstraints` and the rest): an invariant TRUE is its warning (2149), any other
/// value TLC_CONFIG_ID_HAS_VALUE (2230). The front end counts TLCSet state-level and checks the
/// predicate in each state, which shows TLC's output only where TLC fails to compute it as it
/// starts and keeps it as an operator, where TLCSet fails there first or the evaluator finds the
/// predicate failing before any TLCSet, and where a constraint TLC computes holds. Each other
/// such predicate declines, as does one the evaluator can't compute.
pub(crate) fn check_constant_through_tlc_set(
    config: &crate::config::ModelConfig,
    environment: &Environment,
    facts: &DefinitionFacts,
    order: ValueOrder<'_>,
    version: crate::TlcVersion,
) -> Result<()> {
    // A fresh evaluator, as the values it keeps with TLCSet computed are TLC's only as it starts.
    let mut evaluator = crate::eval::Evaluator::new(environment, order, version, false);
    evaluator.computes_tlc_set = true;
    // TLCGet's Java method has a minimum level of 1, so a predicate that reaches it isn't
    // constant to TLC either.
    let mut non_constant: Vec<&str> = environment
        .variable_index
        .keys()
        .map(|name| &**name)
        .collect();
    non_constant.push("TLCGet");
    let constraints: Vec<&String> = [&config.constraints, &config.action_constraints]
        .into_iter()
        .flatten()
        .collect();
    let is_declined = [
        &config.invariants,
        &config.properties,
        &config.constraints,
        &config.action_constraints,
        &config.postconditions,
    ]
    .into_iter()
    .flatten()
    .chain([&config.init, &config.next].into_iter().flatten())
    .filter_map(|name| Some((name, environment.definitions.get(name.as_str())?)))
    .any(|(name, definition)| {
        let is_constant_to_tlc = matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty())
            && !environment.constants.contains_key(&definition.name)
            && !environment.substitutions.contains_key(&definition.name)
            && reaches_in(&definition.body, environment, &["TLCSet"], None)
            && !reaches_in(&definition.body, environment, &non_constant, None)
            && !facts.is_constant_level(definition, environment)
            && !fails_first_at_startup(&definition.body, environment);
        is_constant_to_tlc
            && match evaluator.evaluate(&definition.body, None) {
                Err(FrontError::Evaluation(_)) => false,
                Ok(ConfigValue::Boolean(true)) => !constraints.contains(&name),
                _ => true,
            }
    });
    if is_declined {
        return Err(FrontError::NotYet(
            "a predicate the configuration names that TLC computes as it starts, constant but \
             for TLCSet"
                .into(),
        ));
    }
    Ok(())
}

/// Whether TLC's computing an expression as it starts first sets a register, which throws there
/// before any effect: `TLCSet` of a literal key that is a number (`simulator.setAllValues`, as
/// there is no checker yet) or a value TLC doesn't take for a key, such as a string it doesn't
/// know, a negative number or a boolean (`TLC_MODULE_ARGUMENT_ERROR`), and a literal value, or
/// `TLCGetAndSet` of such a key and literals, whose `Op` is a builtin of arithmetic, as the first
/// conjunct or the left side of an equality there. `processConstantDefns` swallows that, and TLC
/// computes the definition at each use instead, as the engine does.
///
/// A value with no effect TLC computes before it sets the register, which fails before any effect
/// too or else leaves TLCSet to fail; TLC evaluates the first operand of a conjunction or a
/// disjunction first; and a definition named without arguments TLC computes as written there.
fn fails_first_at_startup(expression: &Expr, environment: &Environment) -> bool {
    fails_first_evaluated(expression, environment, None, 0, &StartupWalks::default())
}

/// How deep the startup walks below go, through definitions and the parts of expressions, before
/// they give up (answering that the expression may have an effect, which declines or computes it
/// as before). Each definition a walk meets at a depth it takes once (`StartupWalks`), so the
/// bound keeps the walk off a recursion without end and bounds its stack, not its time: a chain
/// of definitions that each name the one before twice, which TLC computes once each as it starts,
/// takes two levels a definition, and one of 127 definitions or fewer is walked to its end.
const STARTUP_WALK_DEPTH: u32 = 256;

/// What the startup walks below learned of each expression they met, at each depth, for one
/// evaluator (or none): a definition that a chain of definitions names twice at each step
/// (`D2 == D1 /\ D1`) is walked once at each depth, not once for each path to it, as TLC's
/// `processConstantDefns` computes each definition once. The depth is part of the key, as each
/// walk gives up past `STARTUP_WALK_DEPTH` levels, so the walks answer as they would without it. Each entry holds
/// its expression, so no other expression takes its address while the walks last.
#[derive(Default)]
struct StartupWalks {
    sets_nothing: WalkMemo,
    fails_first: WalkMemo,
}

/// A walk's answer for each expression's address and depth, and whether a function application
/// around it keeps a function constructor lazy (`KEPT_LAZY`), with the expression it holds.
type WalkMemo = RefCell<FastMap<(usize, u32, bool), (Expr, bool)>>;

impl StartupWalks {
    /// The walk's answer for an expression at a depth, from what it learned or else computed. An
    /// application TLC evaluates with `KeepLazy` changes what fails first within it, so an answer
    /// found there isn't one found outside.
    fn get(memo: &WalkMemo, expression: &Expr, depth: u32, walk: impl FnOnce() -> bool) -> bool {
        let is_kept_lazy = KEPT_LAZY.with(|kept| kept.get() > 0);
        let key = (Rc::as_ptr(expression) as usize, depth, is_kept_lazy);
        if let Some((_, answer)) = memo.borrow().get(&key) {
            return *answer;
        }
        let answer = walk();
        memo.borrow_mut().insert(key, (expression.clone(), answer));
        answer
    }
}

/// Whether TLC's computing an expression as it starts fails before any effect or completes
/// with none. `processConstantDefns` swallows the failure and computes the definition at each
/// use, and keeps a value computed without effect, which the engine computes at each use alike.
///
/// An expression sets nothing where it fails first (`fails_first_at_startup`, with the
/// evaluator's help), has no effect at all, or is built of parts that each set nothing by an
/// operator without effect of its own: each part TLC evaluates then fails before any effect,
/// which ends the whole, or completes with none. A junction sets nothing up to an operand that
/// fails first, as `(1 \div 0 = 1) /\ TLCSet(1, 2) /\ PrintT(3)` and
/// `TRUE /\ TLCSet(1, 2) /\ PrintT(3)` do, as TLC evaluates its operands in order. An Assert
/// of arguments without effect has none either: it holds or fails. A definition's body sets
/// nothing for any arguments where it sets nothing with its parameters unknown.
fn sets_nothing_at_startup(
    expression: &Expr,
    environment: &Environment,
    evaluator: Option<&crate::eval::Evaluator>,
) -> bool {
    sets_nothing_within(
        expression,
        environment,
        evaluator,
        0,
        &StartupWalks::default(),
    )
}

fn sets_nothing_within(
    expression: &Expr,
    environment: &Environment,
    evaluator: Option<&crate::eval::Evaluator>,
    depth: u32,
    walks: &StartupWalks,
) -> bool {
    StartupWalks::get(&walks.sets_nothing, expression, depth, || {
        sets_nothing_walked(expression, environment, evaluator, depth, walks)
    })
}

fn sets_nothing_walked(
    expression: &Expr,
    environment: &Environment,
    evaluator: Option<&crate::eval::Evaluator>,
    depth: u32,
    walks: &StartupWalks,
) -> bool {
    if depth > STARTUP_WALK_DEPTH {
        return false;
    }
    let is_pure = |expression: &Expr| {
        is_plain_literal(expression, environment)
            || !reaches_in(expression, environment, &STARTUP_VALUE_EFFECTS, None)
    };
    if is_pure(expression)
        || fails_first_evaluated(expression, environment, evaluator, depth, walks)
    {
        return true;
    }
    if let Some(body) = aliased_body(expression, environment) {
        return sets_nothing_within(&body, environment, evaluator, depth + 1, walks);
    }
    let sets_nothing = |expression: &Expr| {
        sets_nothing_within(expression, environment, evaluator, depth + 1, walks)
    };
    match &expression.kind {
        ExpressionKind::Junction {
            operands, is_and, ..
        } => {
            for (position, operand) in operands.iter().enumerate() {
                // The draws written in the operands after it, which TLC never reaches where it
                // decides the junction.
                let skipped: usize = operands[position + 1..].iter().map(count_draws).sum();
                if fails_first_evaluated(operand, environment, evaluator, depth + 1, walks)
                    || decides_for_every_draw(operand, *is_and, environment, evaluator, skipped)
                {
                    return true;
                }
                if !sets_nothing(operand) {
                    return false;
                }
            }
            true
        }
        // The definitions of a LET have no effect where their names in its body have none,
        // which TLC evaluates where the body names them.
        ExpressionKind::Let {
            definitions,
            instances: None,
            body,
            ..
        } => {
            definitions.iter().all(|definition| {
                is_pure(&definition.body)
                    && match &definition.kind {
                        DefinitionKind::Function { bounds } => {
                            bounds.iter().all(|bound| is_pure(&bound.set))
                        }
                        DefinitionKind::Operator { .. } => true,
                    }
            }) && sets_nothing(body)
        }
        ExpressionKind::Let { .. } => false,
        ExpressionKind::Apply { args, .. } if !expression.is_locally_resolved() => {
            let Some(name) = expression.reference() else {
                return false;
            };
            if !args.iter().all(sets_nothing) {
                return false;
            }
            let target = environment.substitutions.get(&name).unwrap_or(&name);
            if environment.constants.contains_key(target) {
                return true;
            }
            match environment.definitions.get(target) {
                Some(definition) => match &definition.kind {
                    DefinitionKind::Operator { .. } => sets_nothing(&definition.body),
                    DefinitionKind::Function { bounds } => {
                        bounds.iter().all(|bound| sets_nothing(&bound.set))
                            && sets_nothing(&definition.body)
                    }
                },
                None => {
                    environment.builtins.contains_key(target)
                        && (!STARTUP_VALUE_EFFECTS.contains(&&**target)
                            || &**target == "Assert" && args.iter().all(is_pure))
                }
            }
        }
        // TLC evaluates an application's function with `KeepLazy` (OPCODE_fa), which keeps a
        // function constructor within it lazy (`KEPT_LAZY`).
        ExpressionKind::FunctionApplication { function, args } => {
            KEPT_LAZY.with(|kept| kept.set(kept.get() + 1));
            let sets_nothing_in_function = sets_nothing(function);
            KEPT_LAZY.with(|kept| kept.set(kept.get() - 1));
            sets_nothing_in_function && args.iter().all(sets_nothing)
        }
        // A name TLC looks up without effect of its own.
        ExpressionKind::Identifier { .. } => false,
        ExpressionKind::Apply { .. } | ExpressionKind::OperatorReference { .. } => false,
        _ => expression.children().iter().all(sets_nothing),
    }
}

/// Whether an operand of a junction whose only effects are draws written in it of RandomElement,
/// also of a power set, or of RandomSubset, where nothing else in the spec draws, decides the junction for every element each draw may
/// take: FALSE for a conjunction, TRUE for a disjunction, as `(RandomElement({0, 2}) = 1) /\
/// TLCSet(1, 2)`. TLC evaluates no operand past it as it starts, whatever it draws, and keeps the
/// value, where the engine, counting TLCSet state-level, evaluates the definition at each use,
/// drawing there too: as nothing else draws, the generator's state that leaves shows nowhere.
/// `skipped` counts the draws written in the junction's operands after it, which neither reaches
/// (`TLCSet(1, RandomElement(1..5))`).
fn decides_for_every_draw(
    operand: &Expr,
    is_and: bool,
    environment: &Environment,
    evaluator: Option<&crate::eval::Evaluator>,
    skipped: usize,
) -> bool {
    let Some(evaluator) = evaluator else {
        return false;
    };
    // The draws the evaluator follows: TLC's RandomElement, also of a power set, and
    // Randomization's RandomSubset.
    let followed = [("RandomElement", "TLC"), ("RandomSubset", "Randomization")];
    let other_effects: Vec<&str> = STARTUP_VALUE_EFFECTS
        .iter()
        .copied()
        .filter(|name| !followed.iter().any(|(followed, _)| followed == name))
        .collect();
    let is_tlc_draw = crate::eval::is_builtin_draw(environment, "RandomElement", "TLC")
        && environment.definitions.get("RandomSubset").is_none_or(|_| {
            crate::eval::is_builtin_draw(environment, "RandomSubset", "Randomization")
        });
    if !is_tlc_draw || reaches_in(operand, environment, &other_effects, None) {
        return false;
    }
    let sites = count_draws(operand);
    if sites == 0 || count_spec_draws(environment) != sites + skipped {
        return false;
    }
    crate::eval::for_every_draw(environment, evaluator, operand, |value, _| {
        value.ok() == Some(ConfigValue::Boolean(!is_and))
    })
}

/// The builtins that draw from TLC's generator.
const DRAWS: [&str; 5] = [
    "RandomElement",
    "RandomSubset",
    "RandomSetOfSubsets",
    "RandomSubsetSet",
    "TestRandomSetOfSubsets",
];

/// How many applications of a builtin that draws an expression writes.
pub(crate) fn count_draws(expression: &Expr) -> usize {
    let mut count = 0;
    let mut pending = vec![expression.clone()];
    while let Some(expression) = pending.pop() {
        if !expression.is_locally_resolved()
            && expression
                .reference()
                .is_some_and(|name| DRAWS.contains(&&*name))
        {
            count += 1;
        }
        pending.extend(expression.children());
    }
    count
}

/// How many applications of a builtin that draws the spec writes where TLC may evaluate them:
/// in its definitions without parameters, which TLC computes as it starts, read or not, in those
/// with parameters something names, and in its assumptions.
fn count_spec_draws(environment: &Environment) -> usize {
    let referred = get_referred_names(environment, None);
    let mut seen = FastSet::default();
    environment
        .definitions
        .values()
        .filter(|definition| seen.insert(Rc::as_ptr(definition) as usize))
        .filter(|definition| {
            matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty())
                || referred.contains(&definition.name)
        })
        .map(|definition| {
            count_draws(&definition.body)
                + match &definition.kind {
                    DefinitionKind::Function { bounds } => {
                        bounds.iter().map(|bound| count_draws(&bound.set)).sum()
                    }
                    DefinitionKind::Operator { .. } => 0,
                }
        })
        .chain(
            environment
                .assumptions
                .iter()
                .map(|assumption| count_draws(&assumption.expression)),
        )
        .sum()
}

// `nullary_body`, through each definition without parameters whose body only names another
// (`D2 == D1`, `D1 == D0`), up to `STARTUP_ALIAS_STEPS` of them: the body the walks above go on
// with, a level deeper, however long the chain, as each such definition has the value of the
// one it names. A longer chain, which only a recursion makes, leaves the walk at the definition
// it reached, a level deeper, which bounds the walk.
fn aliased_body(expression: &Expr, environment: &Environment) -> Option<Expr> {
    let mut body = nullary_body(expression, environment)?;
    for _ in 0..STARTUP_ALIAS_STEPS {
        match nullary_body(&body, environment) {
            Some(next) => body = next,
            None => break,
        }
    }
    Some(body)
}

/// How many definitions that each only name another `aliased_body` goes through at once.
const STARTUP_ALIAS_STEPS: usize = 4096;

// The body of the definition without parameters an expression names without arguments.
fn nullary_body(expression: &Expr, environment: &Environment) -> Option<Expr> {
    if expression.is_locally_resolved() {
        return None;
    }
    if let ExpressionKind::Apply { args, .. } = &expression.kind
        && !args.is_empty()
    {
        return None;
    }
    let name = expression.reference()?;
    if environment.substitutions.contains_key(&name)
        || environment.constants.contains_key(&name)
        || environment.builtins.contains_key(&name)
    {
        return None;
    }
    let definition = environment.definitions.get(&name)?;
    match &definition.kind {
        DefinitionKind::Operator { params, .. } if params.is_empty() => {
            Some(definition.body.clone())
        }
        _ => None,
    }
}

// The builtins a value TLCSet takes must not reach to fail or set nothing before any effect.
pub(crate) const STARTUP_VALUE_EFFECTS: [&str; 16] = [
    "Print",
    "PrintT",
    "TLCSet",
    "TLCGet",
    "JavaTime",
    "RandomElement",
    "RandomSubset",
    "RandomSetOfSubsets",
    "RandomSubsetSet",
    "TestRandomSetOfSubsets",
    "Assert",
    "AssertEq",
    "AssertError",
    "TLCGetOrDefault",
    "TLCGetAndSet",
    "PickSuccessor",
];

/// The builtins with an effect, or an evaluation of their own, that the engine's computing a
/// definition as TLC starts (`tla_ir::Startup::register_probes`) doesn't count as TLC has them
/// there: all but the prints, `Assert`, `TLCSet` and the draws, whose prints and draws the engine
/// counts, whose TLCSet it stops at, and whose failure TLC swallows. TLCGet reads a register TLC
/// hasn't made; TLCExt's builtins evaluate their arguments their own way; IOUtils's touch files.
const UNPROBED_EFFECTS: [&str; 27] = [
    "JavaTime",
    "TLCGet",
    "TLCGetOrDefault",
    "TLCGetAndSet",
    "_Track",
    "AssertEq",
    "AssertError",
    "PickSuccessor",
    "TLCDefer",
    "TLCCache",
    "TLCEvalDefinition",
    "Trace",
    "CounterExample",
    "ToTrace",
    "TLCModelValue",
    "JsonSerialize",
    "ndJsonSerialize",
    "JsonDeserialize",
    "ndJsonDeserialize",
    "Serialize",
    "Deserialize",
    "IOExec",
    "IOEnvExec",
    "IOExecTemplate",
    "IOEnvExecTemplate",
    "IOEnv",
    "atoi",
];

/// Whether an expression reaches TLCSet, through the definitions it names, where TLC may
/// evaluate it later than the expression's own evaluation reaches it, or never: in a function's
/// body, which TLC keeps lazy where an application evaluates the function (OPCODE_fa's
/// `KeepLazy`) or its domain isn't one it reduces, a filter's predicate, which it keeps lazy
/// over a set it doesn't reduce (OPCODE_sso), a LAMBDA, a LET's definition, or an argument of an
/// operator the spec defines, which it evaluates where it first reads it. The engine, computing
/// the definition as TLC starts (`tla_ir::Startup::register_probes`), may meet such a TLCSet in
/// another order than TLC, which it doesn't show as it runs.
fn reaches_deferred_tlc_set(
    expression: &Expr,
    environment: &Environment,
    is_deferred: bool,
    seen: &mut FastSet<(usize, bool)>,
    depth: u32,
) -> bool {
    if depth > 256 {
        return true;
    }
    let walk = |expression: &Expr, is_deferred: bool, seen: &mut FastSet<(usize, bool)>| {
        reaches_deferred_tlc_set(expression, environment, is_deferred, seen, depth + 1)
    };
    if let Some(name) = expression.reference()
        && !expression.is_locally_resolved()
    {
        let target = environment.substitutions.get(&name).unwrap_or(&name);
        if target.ends_with("TLCSet") && is_deferred {
            return true;
        }
        if let Some(definition) = environment.definitions.get(target) {
            if seen.insert((Rc::as_ptr(definition) as usize, is_deferred)) {
                if let DefinitionKind::Function { bounds } = &definition.kind {
                    if bounds
                        .iter()
                        .any(|bound| walk(&bound.set, is_deferred, seen))
                    {
                        return true;
                    }
                    if walk(&definition.body, true, seen) {
                        return true;
                    }
                } else if walk(&definition.body, is_deferred, seen) {
                    return true;
                }
            }
            if let ExpressionKind::Apply { args, .. } = &expression.kind {
                return args.iter().any(|arg| walk(arg, true, seen));
            }
            return false;
        }
    }
    match &expression.kind {
        // Over a set TLC can't enumerate, which neither TLC nor the engine builds at once, the
        // body runs only at an application, as the definition's evaluation reaches it.
        ExpressionKind::FunctionConstruction { bounds, body } => {
            let is_infinite = bounds.iter().any(|bound| {
                matches!(bound.set.kind, ExpressionKind::Identifier { .. })
                    && matches!(
                        get_plain_builtin(&bound.set, environment),
                        Some("Nat" | "Int" | "STRING")
                    )
            });
            bounds
                .iter()
                .any(|bound| walk(&bound.set, is_deferred, seen))
                || walk(body, is_deferred || !is_infinite, seen)
        }
        ExpressionKind::SetFilter { bound, predicate } => {
            walk(&bound.set, is_deferred, seen) || walk(predicate, true, seen)
        }
        ExpressionKind::Lambda { body, .. } => walk(body, true, seen),
        ExpressionKind::Let {
            definitions, body, ..
        } => {
            definitions.iter().any(|definition| {
                walk(&definition.body, true, seen)
                    || matches!(&definition.kind, DefinitionKind::Function { bounds }
                        if bounds.iter().any(|bound| walk(&bound.set, true, seen)))
            }) || walk(body, is_deferred, seen)
        }
        ExpressionKind::Apply { args, .. } if expression.is_locally_resolved() => {
            args.iter().any(|arg| walk(arg, true, seen))
        }
        _ => expression
            .children()
            .iter()
            .any(|child| walk(child, is_deferred, seen)),
    }
}

/// Whether a value the evaluator computed is a set with an element.
fn is_nonempty_set(value: Option<ConfigValue>) -> bool {
    matches!(value, Some(ConfigValue::Set(elements)) if !elements.is_empty())
}

/// Whether an expression is `{x \in S : p}` that TLC builds lazily, as S isn't a set it can
/// reduce (`OPCODE_sso`), and fails to enumerate before it evaluates p, as S isn't enumerable
/// either (`SetPredValue.Enumerator`): a number, a string, a boolean, `STRING`, `Nat`, `Int` or
/// such a set itself, or a tuple, a record, a function or `Seq(T)` (`UserValue`) built without
/// effect.
fn is_failing_lazy_filter(expression: &Expr, environment: &Environment, depth: u32) -> bool {
    if depth > 64 {
        return false;
    }
    let ExpressionKind::SetFilter { bound, .. } = &expression.kind else {
        return false;
    };
    let is_built_without_effect =
        || !reaches_in(&bound.set, environment, &STARTUP_VALUE_EFFECTS, None);
    match &bound.set.kind {
        ExpressionKind::Number { .. } | ExpressionKind::String { .. } => true,
        ExpressionKind::Identifier { .. } => matches!(
            get_plain_builtin(&bound.set, environment),
            Some("STRING" | "Nat" | "Int" | "TRUE" | "FALSE")
        ),
        ExpressionKind::Tuple(_)
        | ExpressionKind::Record { .. }
        | ExpressionKind::FunctionConstruction { .. } => is_built_without_effect(),
        ExpressionKind::Apply { args, .. }
            if args.len() == 1 && get_plain_builtin(&bound.set, environment) == Some("Seq") =>
        {
            is_built_without_effect()
        }
        _ => is_failing_lazy_filter(&bound.set, environment, depth + 1),
    }
}

thread_local! {
    // How many function applications deep `fails_first_evaluated` looks, within the function
    // TLC evaluates there with `EvalControl.KeepLazy`, which keeps a function constructor lazy.
    static KEPT_LAZY: std::cell::Cell<u32> = const { std::cell::Cell::new(0) };
}

/// The builtins whose arguments TLC evaluates in order before it applies them, and that have no
/// effect of their own: their OPCODEs in `Tool.evalAppl` evaluate each argument, and a Java
/// method's `OpValue.eval` evaluates them all first.
const EAGER_BUILTINS: [&str; 30] = [
    "\\cup",
    "\\cap",
    "\\",
    "\\subseteq",
    "SUBSET",
    "UNION",
    "DOMAIN",
    "<=>",
    "+",
    "-",
    "*",
    "^",
    "\\div",
    "%",
    "..",
    "<",
    ">",
    "<=",
    ">=",
    "-.",
    "Len",
    "Head",
    "Tail",
    "Append",
    "\\o",
    "SubSeq",
    "Seq",
    "IsFiniteSet",
    ":>",
    "@@",
];

/// The part of an expression TLC evaluates first, where it evaluates one part before any
/// other: a junction's first operand, a tuple's or a set enumeration's first element, an IF's
/// condition, or the first argument of a builtin that evaluates its arguments in order.
fn first_evaluated(expression: &Expr, environment: &Environment) -> Option<Expr> {
    match &expression.kind {
        ExpressionKind::Junction { operands, .. } => operands.first().cloned(),
        ExpressionKind::Tuple(elements) | ExpressionKind::SetEnumeration(elements) => {
            elements.first().cloned()
        }
        ExpressionKind::If { condition, .. } => Some(condition.clone()),
        ExpressionKind::Apply { args, .. }
            if !expression.is_locally_resolved()
                && get_plain_builtin(expression, environment).is_some_and(|name| {
                    EAGER_BUILTINS.contains(&name)
                        || matches!(
                            name,
                            "=" | "#" | "\\in" | "\\notin" | "=>" | "~" | "Cardinality" | "PrintT"
                        )
                }) =>
        {
            args.first().cloned()
        }
        _ => None,
    }
}

/// Whether an expression is a set that fails as TLC enumerates it, before any effect: a failing
/// lazy filter (`is_failing_lazy_filter`), a definition without parameters that is one, or a
/// union of sets built without effect one of which is one, which TLC keeps lazy or reduces by
/// enumerating that one (`OPCODE_cup`, `SetCupValue.convertAndCache`).
fn is_failing_lazy_union(expression: &Expr, environment: &Environment, depth: u32) -> bool {
    if depth > STARTUP_WALK_DEPTH {
        return false;
    }
    if let Some(body) = aliased_body(expression, environment) {
        return is_failing_lazy_union(&body, environment, depth + 1);
    }
    match &expression.kind {
        ExpressionKind::Apply { args, .. }
            if get_plain_builtin(expression, environment) == Some("\\cup") =>
        {
            args.iter()
                .all(|arg| !reaches_in(arg, environment, &STARTUP_VALUE_EFFECTS, None))
                && args
                    .iter()
                    .any(|arg| is_failing_lazy_union(arg, environment, depth + 1))
        }
        // Which bounds its own depth.
        _ => is_failing_lazy_filter(expression, environment, 0),
    }
}

/// Java methods of the standard modules whose arguments TLC computes in order before it calls
/// them (`Tool.evalAppl` of a `MethodValue`), in each spelling SANY gives them.
const STRICT_JAVA_METHODS: [&str; 22] = [
    "Len",
    "Head",
    "Tail",
    "Append",
    "SubSeq",
    "\\o",
    "\\circ",
    "IsFiniteSet",
    "+",
    "-",
    "*",
    "\\div",
    "%",
    "<",
    ">",
    "\\leq",
    "<=",
    "=<",
    "\\geq",
    ">=",
    "..",
    "-.",
];

/// `fails_first_at_startup`'s walk, which also takes an expression without effect the evaluator
/// fails on as TLC does (`fails_as_built`) for one that fails first, where an evaluator is given.
fn fails_first_evaluated(
    expression: &Expr,
    environment: &Environment,
    evaluator: Option<&crate::eval::Evaluator>,
    depth: u32,
    walks: &StartupWalks,
) -> bool {
    StartupWalks::get(&walks.fails_first, expression, depth, || {
        fails_first_walked(expression, environment, evaluator, depth, walks)
    })
}

fn fails_first_walked(
    expression: &Expr,
    environment: &Environment,
    evaluator: Option<&crate::eval::Evaluator>,
    depth: u32,
    walks: &StartupWalks,
) -> bool {
    if depth > STARTUP_WALK_DEPTH {
        return false;
    }
    // A definition without parameters named, which fails at startup before any effect too, so
    // TLC kept no value of it.
    if let Some(body) = aliased_body(expression, environment) {
        return fails_first_evaluated(&body, environment, evaluator, depth + 1, walks);
    }
    if let Some(evaluator) = evaluator
        && !reaches_in(expression, environment, &STARTUP_VALUE_EFFECTS, None)
        && fails_as_built(expression, evaluator, 0)
    {
        return true;
    }
    // TLCExt defines TLCGetAndSet in TLA+ too.
    let is_builtin = |name: &str| {
        environment.builtins.contains_key(name)
            && environment.definitions.get(name).is_none_or(|definition| {
                name == "TLCGetAndSet"
                    && definition
                        .location
                        .range
                        .as_ref()
                        .is_some_and(|range| &*range.module == "TLCExt")
            })
    };
    let is_literal = |expression: &Expr| is_plain_literal(expression, environment);
    let is_pure = |expression: &Expr| {
        is_literal(expression) || !reaches_in(expression, environment, &STARTUP_VALUE_EFFECTS, None)
    };
    let is_failing_key = |expression: &Expr| match &expression.kind {
        ExpressionKind::Number { .. } => true,
        ExpressionKind::String { value, .. } => {
            !matches!(&**value, "exit" | "pause")
                && !value.starts_with("s:")
                && !value.starts_with("-D")
        }
        // A value that is neither an integer nor a string, built without effect, which TLC
        // rejects for a key (`TLC_MODULE_ARGUMENT_ERROR`) or fails to build first: a set, a
        // function, a record, a tuple or a model value, or `Nat`, `Int`, `STRING` or `BOOLEAN`.
        ExpressionKind::SetEnumeration(_)
        | ExpressionKind::SetFilter { .. }
        | ExpressionKind::SetMap { .. }
        | ExpressionKind::Tuple(_)
        | ExpressionKind::FunctionConstruction { .. }
        | ExpressionKind::FunctionSet { .. }
        | ExpressionKind::Record { .. }
        | ExpressionKind::Product(_) => is_pure(expression),
        ExpressionKind::Identifier { .. }
            if matches!(
                get_plain_builtin(expression, environment),
                Some("Nat" | "Int" | "STRING" | "BOOLEAN")
            ) =>
        {
            true
        }
        ExpressionKind::Apply { .. }
            if matches!(
                get_plain_builtin(expression, environment),
                Some("SUBSET" | "UNION" | "\\cup" | "\\cap" | "\\" | "Seq" | "TLCModelValue")
            ) =>
        {
            is_pure(expression)
        }
        // A negative number, a boolean, a set or a tuple, which TLC fails on too.
        _ => is_plain_literal(expression, environment),
    };
    let enumerating_fails_first = |set: &Expr| {
        is_failing_lazy_filter(set, environment, depth)
            || fails_first_evaluated(set, environment, evaluator, depth + 1, walks)
    };
    // The value the evaluator computes of an expression without effect, which TLC computes alike.
    let evaluated = |expression: &Expr| {
        let evaluator = evaluator?;
        if !is_pure(expression) {
            return None;
        }
        evaluator.evaluate(expression, None).ok()
    };
    // Where an evaluator is given, operands TLC evaluates in order, of which one fails first
    // after those before it have no effect and evaluate as `goes_on` allows. Without `goes_on`,
    // TLC goes on after any value, so an operand without effect fails first or goes on.
    let in_order_fails_first =
        |operands: &[Expr], goes_on: Option<&dyn Fn(&ConfigValue) -> bool>| {
            for operand in operands {
                if fails_first_evaluated(operand, environment, evaluator, depth + 1, walks) {
                    return true;
                }
                let is_going_on = match goes_on {
                    Some(goes_on) => evaluated(operand).is_some_and(|value| goes_on(&value)),
                    None => evaluator.is_some() && is_pure(operand),
                };
                if !is_going_on {
                    return false;
                }
            }
            false
        };
    match &expression.kind {
        // TLC evaluates a junction's operands in order, up to one that decides it.
        ExpressionKind::Junction {
            operands, is_and, ..
        } if evaluator.is_some() => {
            let is_and = *is_and;
            in_order_fails_first(
                operands,
                Some(&|value: &ConfigValue| *value == ConfigValue::Boolean(is_and)),
            )
        }
        ExpressionKind::Junction { operands, .. } => operands.first().is_some_and(|first| {
            fails_first_evaluated(first, environment, evaluator, depth + 1, walks)
        }),
        // TLC builds a tuple's and a set enumeration's elements in order (`OPCODE_tup`,
        // `OPCODE_se`).
        ExpressionKind::Tuple(elements) | ExpressionKind::SetEnumeration(elements)
            if evaluator.is_some() =>
        {
            in_order_fails_first(elements, None)
        }
        // TLC evaluates a bound's set and enumerates it before the next bound's
        // (`Tool.contexts`), and both before the body.
        // TLC normalizes CHOOSE's set and enumerates it (`OPCODE_bc`).
        ExpressionKind::Choose {
            set: Some(set),
            body,
            ..
        } => {
            enumerating_fails_first(set)
                || is_nonempty_set(evaluated(set))
                    && fails_first_evaluated(body, environment, evaluator, depth + 1, walks)
        }
        // A quantifier whose sets TLC builds without effect and finds not empty evaluates its
        // body for their first elements, where an evaluator is given.
        ExpressionKind::Quantified { bounds, body, .. }
            if evaluator.is_some()
                && bounds
                    .iter()
                    .all(|bound| is_nonempty_set(evaluated(&bound.set)))
                && fails_first_evaluated(body, environment, evaluator, depth + 1, walks) =>
        {
            true
        }
        // A LET whose body TLC first evaluates a definition of the LET without parameters in,
        // where an evaluator is given.
        ExpressionKind::Let {
            definitions,
            instances: None,
            body,
            ..
        } if evaluator.is_some() => {
            if fails_first_evaluated(body, environment, evaluator, depth + 1, walks) {
                return true;
            }
            let mut first = body.clone();
            for _ in 0..64 {
                let Some(operand) = first_evaluated(&first, environment) else {
                    break;
                };
                first = operand;
            }
            let ExpressionKind::Identifier { name, .. } = &first.kind else {
                return false;
            };
            first.is_locally_resolved()
                && definitions.iter().any(|definition| {
                    definition.name == *name
                        && matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty())
                        && fails_first_evaluated(&definition.body, environment, evaluator, depth + 1, walks)
                })
        }
        // TLC evaluates an IF's condition first, and then the branch it takes, where an
        // evaluator is given.
        ExpressionKind::If {
            condition,
            consequent,
            alternative,
        } if evaluator.is_some() => {
            // A quantifier over sets TLC builds without effect, one of them empty, has no
            // effect either: TLC never evaluates its body.
            let decided = match &condition.kind {
                ExpressionKind::Quantified {
                    quantifier, bounds, ..
                } if {
                    let sets: Vec<Option<ConfigValue>> =
                        bounds.iter().map(|bound| evaluated(&bound.set)).collect();
                    sets.iter()
                        .all(|set| matches!(set, Some(ConfigValue::Set(_))))
                        && sets.iter().any(|set| {
                            matches!(set, Some(ConfigValue::Set(elements)) if elements.is_empty())
                        })
                } =>
                {
                    Some(ConfigValue::Boolean(matches!(
                        quantifier,
                        Quantifier::Forall
                    )))
                }
                _ => evaluated(condition),
            };
            fails_first_evaluated(condition, environment, evaluator, depth + 1, walks)
                || match decided {
                    Some(ConfigValue::Boolean(true)) => {
                        fails_first_evaluated(consequent, environment, evaluator, depth + 1, walks)
                    }
                    Some(ConfigValue::Boolean(false)) => {
                        fails_first_evaluated(alternative, environment, evaluator, depth + 1, walks)
                    }
                    _ => false,
                }
        }
        ExpressionKind::SetMap { bounds, .. } | ExpressionKind::Quantified { bounds, .. } => bounds
            .first()
            .is_some_and(|bound| enumerating_fails_first(&bound.set)),
        // TLC evaluates a filter's set first (OPCODE_sso).
        ExpressionKind::SetFilter { bound, .. } => {
            fails_first_evaluated(&bound.set, environment, evaluator, depth + 1, walks)
        }
        // TLC applies a function by evaluating it, keeping a function constructor it meets there
        // lazy (OPCODE_fa's `setKeepLazy`, which reaches all it evaluates within), and then the
        // argument.
        ExpressionKind::FunctionApplication { function, args } => {
            KEPT_LAZY.with(|kept| kept.set(kept.get() + 1));
            let fails = fails_first_evaluated(function, environment, evaluator, depth + 1, walks);
            KEPT_LAZY.with(|kept| kept.set(kept.get() - 1));
            // A value that isn't a function TLC fails to apply before it evaluates the argument:
            // also a set, which a set's constructor or operator built without effect gives.
            let is_set_built = is_pure(function)
                && match &function.kind {
                    ExpressionKind::SetEnumeration(_)
                    | ExpressionKind::SetFilter { .. }
                    | ExpressionKind::SetMap { .. }
                    | ExpressionKind::FunctionSet { .. }
                    | ExpressionKind::Product(_) => true,
                    ExpressionKind::Apply { .. } => matches!(
                        get_plain_builtin(function, environment),
                        Some("SUBSET" | "UNION" | "\\cup" | "\\cap" | "\\" | ".." | "Seq")
                    ),
                    _ => false,
                };
            // A constructor applied directly TLC keeps lazy, having evaluated its domains, and
            // then evaluates the argument and the body at it (`FcnLambdaValue.apply`), or fails
            // on an argument outside the domain.
            let is_applied_failing = || {
                matches!(&function.kind, ExpressionKind::FunctionConstruction { bounds, body }
                    if evaluator.is_some()
                        && bounds.iter().all(|bound| is_pure(&bound.set))
                        && args.iter().all(&is_pure)
                        && fails_first_evaluated(body, environment, evaluator, depth + 1, walks))
            };
            // TLCSet of a named register, "exit" or "pause" and a value without effect gives
            // TRUE as TLC starts, setting nothing, which TLC fails to apply.
            let is_unset_register = || {
                matches!(&function.kind, ExpressionKind::Apply { args: set_args, .. }
                    if !function.is_locally_resolved()
                        && function.reference().as_deref() == Some("TLCSet")
                        && is_builtin("TLCSet")
                        && matches!(set_args.as_slice(), [key, value]
                            if is_pure(value)
                                && matches!(&key.kind, ExpressionKind::String { value, .. }
                                    if matches!(&**value, "exit" | "pause")
                                        || value.starts_with("s:"))))
            };
            fails
                || is_set_built
                || is_unset_register()
                || is_applied_failing()
                || matches!(
                    evaluated(function),
                    Some(
                        ConfigValue::Number(_)
                            | ConfigValue::String(_)
                            | ConfigValue::Boolean(_)
                            | ConfigValue::Set(_)
                    )
                )
                || evaluator.is_some() && is_pure(function) && in_order_fails_first(args, None)
        }
        // TLC evaluates a function constructor's domains in order, and then, where each is a set
        // it reduces, here a set enumeration or an interval, and no application keeps it lazy,
        // builds it at once (OPCODE_fc's `toFcnRcd`): the body first at the first element of the
        // normalized domain, which a body that fails first for any element fails at.
        // Only where an evaluator is given, as the walk that tells whether TLC keeps the
        // constructor lazy is then the whole of the definition's.
        ExpressionKind::FunctionConstruction { bounds, body }
            if evaluator.is_some() && KEPT_LAZY.with(|kept| kept.get()) == 0 =>
        {
            for bound in bounds {
                if fails_first_evaluated(&bound.set, environment, evaluator, depth + 1, walks) {
                    return true;
                }
                if !is_pure(&bound.set) {
                    return false;
                }
            }
            // `TLCSet(i, v)` of the one bound name over an interval or a set enumeration of
            // numbers, and a value without effect: its key at the first element is a number, which
            // TLCSet throws on as TLC starts (`TLCGetSet.TLCSet` finds no checker), after it
            // computed the value.
            let is_number_keyed_set = || {
                let [bound] = bounds.as_slice() else {
                    return false;
                };
                let BoundPattern::Name {
                    name: bound_name, ..
                } = &bound.pattern
                else {
                    return false;
                };
                let is_numbers = match &bound.set.kind {
                    ExpressionKind::SetEnumeration(elements) => elements
                        .iter()
                        .all(|element| matches!(element.kind, ExpressionKind::Number { .. })),
                    _ => get_plain_builtin(&bound.set, environment) == Some(".."),
                };
                is_numbers
                    && matches!(&body.kind, ExpressionKind::Apply { args, .. }
                        if !body.is_locally_resolved()
                            && body.reference().as_deref() == Some("TLCSet")
                            && is_builtin("TLCSet")
                            && matches!(args.as_slice(), [key, value]
                                if is_pure(value)
                                    && key.is_locally_resolved()
                                    && matches!(&key.kind,
                                        ExpressionKind::Identifier { name, .. } if name == bound_name)))
            };
            bounds.iter().all(|bound| {
                (matches!(bound.set.kind, ExpressionKind::SetEnumeration(_))
                    || get_plain_builtin(&bound.set, environment) == Some(".."))
                    && is_nonempty_set(evaluated(&bound.set))
            }) && (is_number_keyed_set()
                || fails_first_evaluated(body, environment, evaluator, depth + 1, walks))
        }
        ExpressionKind::Apply { args, .. } if !expression.is_locally_resolved() => {
            let Some(name) = expression.reference() else {
                return false;
            };
            if !is_builtin(&name) {
                return false;
            }
            match (&*name, args.as_slice()) {
                // TLC evaluates an equality's left side first, and then compares a set it built
                // lazily by enumerating it.
                ("=" | "#", [left, right]) => {
                    in_order_fails_first(args, None)
                        || fails_first_evaluated(left, environment, evaluator, depth + 1, walks)
                        || is_failing_lazy_filter(left, environment, depth)
                            && (is_literal(right)
                                || is_failing_lazy_filter(right, environment, depth))
                }
                // TLC evaluates an element before the set it looks it up in, and fails to look
                // up a value that is neither an integer nor a model value in an interval that
                // isn't empty (`IntervalValue.member`).
                ("\\in" | "\\notin", [element, set]) if evaluator.is_some() => {
                    in_order_fails_first(args, None)
                        || get_plain_builtin(set, environment) == Some("..")
                            && is_nonempty_set(evaluated(set))
                            && (matches!(
                                evaluated(element),
                                Some(
                                    ConfigValue::String(_)
                                        | ConfigValue::Boolean(_)
                                        | ConfigValue::Set(_)
                                        | ConfigValue::Record(_)
                                )
                            ) || is_pure(element)
                                && matches!(
                                    element.kind,
                                    ExpressionKind::Tuple(_)
                                        | ExpressionKind::Record { .. }
                                        | ExpressionKind::SetEnumeration(_)
                                        | ExpressionKind::String { .. }
                                ))
                }
                // TLC evaluates an implication's and an equivalence's left side first, and a
                // negation's operand before it negates it.
                ("=>" | "<=>", [left, _]) | ("~", [left]) => {
                    fails_first_evaluated(left, environment, evaluator, depth + 1, walks)
                }
                // TLC evaluates a Java method's arguments before it calls it, and Cardinality
                // enumerates a set it built lazily, as PrintT does to print it, also within a
                // tuple whose other elements it builds without effect.
                ("Cardinality", [argument]) => {
                    fails_first_evaluated(argument, environment, evaluator, depth + 1, walks)
                        || is_failing_lazy_union(argument, environment, depth)
                }
                // TLC.Assert, a Java method, fails on a first argument that isn't TRUE, after
                // computing both.
                ("Assert", [condition, message]) => {
                    in_order_fails_first(args, None)
                        || is_pure(message)
                            && evaluated(condition)
                                .is_some_and(|value| value != ConfigValue::Boolean(true))
                }
                // A Java method of the standard modules, whose arguments TLC computes in order
                // before it calls it.
                (name, _) if STRICT_JAVA_METHODS.contains(&name) => {
                    in_order_fails_first(args, None)
                }
                ("PrintT", [argument]) => {
                    fails_first_evaluated(argument, environment, evaluator, depth + 1, walks)
                        || is_failing_lazy_filter(argument, environment, depth)
                        || matches!(&argument.kind, ExpressionKind::Tuple(elements)
                        if elements.iter().all(|element| {
                            is_pure(element) || is_failing_lazy_filter(element, environment, depth)
                        }) && elements.iter().any(|element| {
                            is_failing_lazy_filter(element, environment, depth)
                        }))
                }
                // TLC evaluates the key, then the value, before it sets the register: a value
                // that fails first after a key built without effect fails before any effect too
                // (`TLCSet(Nat, TLCSet(1, 2))`).
                ("TLCSet", [key, value]) => {
                    fails_first_evaluated(key, environment, evaluator, depth + 1, walks)
                        || is_failing_key(key) && is_pure(value)
                        || is_pure(key)
                            && fails_first_evaluated(
                                value,
                                environment,
                                evaluator,
                                depth + 1,
                                walks,
                            )
                }
                ("TLCGetAndSet", [key, operator, value, default]) => {
                    is_failing_key(key)
                        && is_literal(value)
                        && is_literal(default)
                        && matches!(operator.kind, ExpressionKind::OperatorReference { .. })
                        && !operator.is_locally_resolved()
                        && operator.reference().is_some_and(|operator| {
                            matches!(&*operator, "+" | "-" | "*") && is_builtin(&operator)
                        })
                }
                // TLC evaluates the arguments of these in order before it applies them (their
                // OPCODEs in `Tool.evalAppl`, and `OpValue.eval` of a Java method's).
                (name, _) if EAGER_BUILTINS.contains(&name) => in_order_fails_first(args, None),
                _ => false,
            }
        }
        _ => false,
    }
}

/// Whether an expression is `TLCSet(k, v)`, or a definition without parameters it names or the
/// first operand of a junction that is, whose key `k` has no effect and fails as TLC builds it, as `<<1 \div 0>>`: TLC evaluates the
/// key before the value, so the value's effects never run as it starts, and
/// `processConstantDefns` swallows the failure and computes the definition at each use, as the
/// engine does.
fn is_key_failing_as_built(
    expression: &Expr,
    environment: &Environment,
    evaluator: Option<&crate::eval::Evaluator>,
) -> bool {
    // TLC evaluates the first operand of a conjunction or a disjunction first.
    let mut expression = expression.clone();
    for _ in 0..64 {
        let next = match &expression.kind {
            ExpressionKind::Junction { operands, .. } => operands.first().cloned(),
            _ => nullary_body(&expression, environment),
        };
        let Some(next) = next else {
            break;
        };
        expression = next;
    }
    let ExpressionKind::Apply { args, .. } = &expression.kind else {
        return false;
    };
    let [key, _] = args.as_slice() else {
        return false;
    };
    let Some(evaluator) = evaluator else {
        return false;
    };
    !expression.is_locally_resolved()
        && expression.reference().as_deref() == Some("TLCSet")
        && environment.builtins.contains_key("TLCSet")
        && !environment.definitions.contains_key("TLCSet")
        && !reaches_in(key, environment, &STARTUP_VALUE_EFFECTS, None)
        && fails_as_built(key, evaluator, 0)
}

// Whether the evaluator finds an expression fails as TLC builds it: a tuple or a set enumeration
// TLC builds element by element, in order (`OPCODE_tup`, `OPCODE_se`), one of whose elements
// fails after those before it are built, or an expression the evaluator fails on as TLC does.
fn fails_as_built(expression: &Expr, evaluator: &crate::eval::Evaluator, depth: u32) -> bool {
    if depth > 64 {
        return false;
    }
    match &expression.kind {
        ExpressionKind::Tuple(elements) | ExpressionKind::SetEnumeration(elements) => {
            for element in elements {
                if fails_as_built(element, evaluator, depth + 1) {
                    return true;
                }
                if evaluator.evaluate(element, None).is_err() {
                    return false;
                }
            }
            false
        }
        // Not a name the evaluator has no value for here, which is no failure of TLC's.
        _ => matches!(
            evaluator.evaluate(expression, None),
            Err(FrontError::Evaluation(message))
                if !message.starts_with("In evaluation, the identifier")
        ),
    }
}

/// The walk for whether TLC's computing an expression as it starts may have an effect but in
/// definitions it names without arguments that fail there first, before any effect. A
/// definition it doesn't reach fails there before any effect or keeps a value it computed
/// without any, which the engine computes at each use alike.
fn reaches_effect_past_failing_first(environment: &Environment) -> Reach<'_> {
    Reach::new(environment, None, move |expression| {
        if let Some(body) = nullary_body(expression, environment)
            && fails_first_at_startup(&body, environment)
        {
            return Visit::Skip;
        }
        if let Some(name) = expression.reference()
            && !expression.is_locally_resolved()
            && STARTUP_VALUE_EFFECTS.contains(&&*name)
        {
            return Visit::Found;
        }
        Visit::Follow(expression.children())
    })
}

/// Whether a constant definition is `PrintT(AssertError(s, e))` of a string written out, which
/// never fails, or a conjunction of such prints and of `AssertError(s, e)` compared with TRUE or
/// FALSE, a comparison of two booleans, which never fails either, that only the first assumption
/// reads, as that assumption itself, where no other constant definition TLC computes as it starts
/// has an effect: TLC computes it once as it starts, with its effects, stopping where the
/// conjunction does, and keeps the boolean the assumption reads, and the engine computes it once
/// there, which shows the same in the same order.
fn is_assumed_print_once(
    definition: &Rc<Definition>,
    config: &crate::config::ModelConfig,
    environment: &Environment,
    startup_effects: &[&str],
) -> bool {
    let is_builtin = |expression: &Expr, builtin: &str| {
        !expression.is_locally_resolved()
            && expression.reference().is_some_and(|name| &*name == builtin)
            && environment.builtins.contains_key(builtin)
            && !environment.definitions.contains_key(builtin)
    };
    // `AssertError(s, e)` of a string written out, which catches e's failure (`TLCExt.assertError`).
    let is_assert_error = |expression: &Expr| {
        matches!(&expression.kind, ExpressionKind::Apply { args, .. }
            if is_builtin(expression, "AssertError")
                && matches!(args.as_slice(), [message, _]
                    if matches!(message.kind, ExpressionKind::String { .. })))
    };
    let is_boolean_literal = |expression: &Expr| {
        matches!(expression.kind, ExpressionKind::Identifier { .. })
            && (is_builtin(expression, "TRUE") || is_builtin(expression, "FALSE"))
    };
    let is_part = |expression: &Expr| match &expression.kind {
        ExpressionKind::Apply { args, .. } if is_builtin(expression, "PrintT") => {
            matches!(args.as_slice(), [asserted] if is_assert_error(asserted))
        }
        ExpressionKind::Apply { args, .. } if is_builtin(expression, "=") => {
            matches!(args.as_slice(), [left, right]
                if (is_assert_error(left) && is_boolean_literal(right))
                    || (is_boolean_literal(left) && is_assert_error(right)))
        }
        _ => false,
    };
    let is_print = |expression: &Expr| {
        matches!(&expression.kind, ExpressionKind::Apply { .. }) && is_builtin(expression, "PrintT")
    };
    let parts: Vec<&Expr> = match &definition.body.kind {
        ExpressionKind::Junction {
            is_and: true,
            operands,
            ..
        } => operands.iter().collect(),
        ExpressionKind::Apply { args, .. }
            if args.len() == 2
                && (is_builtin(&definition.body, "\\land")
                    || is_builtin(&definition.body, "/\\")) =>
        {
            args.iter().collect()
        }
        _ => vec![&definition.body],
    };
    if !parts.iter().all(|part| is_part(part)) || !parts.iter().any(|part| is_print(part)) {
        return false;
    }
    let is_named = |expression: &Expr| {
        !expression.is_locally_resolved()
            && expression
                .reference()
                .is_some_and(|name| name == definition.name)
    };
    let Some(first) = environment.assumptions.first() else {
        return false;
    };
    if !is_named(&first.expression)
        || !matches!(first.expression.kind, ExpressionKind::Identifier { .. })
        || is_read_by_config(config, &|named| named == &*definition.name)
    {
        return false;
    }
    // No other reference to it, anywhere.
    let mut pending: Vec<Expr> = environment
        .definitions
        .values()
        .map(|definition| definition.body.clone())
        .chain(
            environment
                .assumptions
                .iter()
                .skip(1)
                .map(|assumption| assumption.expression.clone()),
        )
        .collect();
    while let Some(expression) = pending.pop() {
        if is_named(&expression) {
            return false;
        }
        pending.extend(expression.children());
    }
    let mut effects: Vec<&str> = startup_effects.to_vec();
    effects.extend(["TLCSet", "AssertError"]);
    !environment.startup_definitions.iter().any(|other| {
        !Rc::ptr_eq(other, definition) && reaches_in(&other.body, environment, &effects, None)
    })
}

/// The definitions the first assumption reads once, where it is a definition's name alone that
/// nothing else names (no definition, no other assumption, no configuration entry), followed
/// through bodies that are only the name of another definition without parameters named nowhere
/// else: TLC computes each as it starts, with its effects, and keeps the value the assumption
/// reads, and the engine computes them once at the assumption, after a startup with no other
/// effect, which shows the same in the same order. Empty where it isn't so.
fn get_assumed_once(
    config: &crate::config::ModelConfig,
    environment: &Environment,
) -> Vec<Rc<Definition>> {
    let Some(first) = environment.assumptions.first() else {
        return Vec::new();
    };
    // How many times each name is written outside the first assumption.
    let mut written: FastMap<Name, usize> = FastMap::default();
    let mut pending: Vec<Expr> = environment
        .definitions
        .values()
        .flat_map(|definition| {
            let bounds = match &definition.kind {
                DefinitionKind::Function { bounds } => bounds.as_slice(),
                DefinitionKind::Operator { .. } => &[],
            };
            bounds
                .iter()
                .map(|bound| bound.set.clone())
                .chain([definition.body.clone()])
                .collect::<Vec<Expr>>()
        })
        .chain(
            environment
                .assumptions
                .iter()
                .skip(1)
                .map(|assumption| assumption.expression.clone()),
        )
        .collect();
    while let Some(expression) = pending.pop() {
        if let Some(name) = expression.reference() {
            *written.entry(name).or_default() += 1;
        }
        pending.extend(expression.children());
    }
    let mut chain = Vec::new();
    let mut expression = first.expression.clone();
    let mut is_first = true;
    loop {
        if !matches!(expression.kind, ExpressionKind::Identifier { .. })
            || expression.is_locally_resolved()
        {
            break;
        }
        let Some(name) = expression.reference() else {
            break;
        };
        let Some(definition) = environment.definitions.get(&name).cloned() else {
            break;
        };
        let reads = written.get(&name).copied().unwrap_or(0);
        if !matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty())
            || environment.constants.contains_key(&name)
            || environment.substitutions.contains_key(&name)
            || environment
                .substitutions
                .values()
                .any(|target| *target == name)
            || is_read_by_config(config, &|named| named == &*name)
            || reads != usize::from(!is_first)
            || chain.iter().any(|other| Rc::ptr_eq(other, &definition))
        {
            break;
        }
        is_first = false;
        expression = definition.body.clone();
        chain.push(definition);
    }
    chain
}

/// Whether an assumption passes an operator with parameters an argument that reaches one of
/// these builtins: the engine evaluates the argument where the operator reads it, which TLC
/// evaluates once.
fn passes_effect(expression: &Expr, environment: &Environment, builtins: &[&str]) -> bool {
    // Every path explored below consists of the supplied expression and definition bodies.
    // If none writes a target name, no argument can reach it through those paths.
    let mut candidates: Vec<Expr> = environment
        .definitions
        .values()
        .map(|definition| definition.body.clone())
        .chain(std::iter::once(expression.clone()))
        .collect();
    let mut is_written = false;
    while let Some(candidate) = candidates.pop() {
        if !candidate.is_locally_resolved()
            && candidate
                .reference()
                .is_some_and(|name| builtins.contains(&&*name))
        {
            is_written = true;
            break;
        }
        candidates.extend(candidate.children());
    }
    if !is_written {
        return false;
    }
    let mut seen = FastSet::default();
    let mut pending = vec![expression.clone()];
    while let Some(expression) = pending.pop() {
        if let ExpressionKind::Apply { args, .. } = &expression.kind
            && let Some(name) = expression.reference()
            && !expression.is_locally_resolved()
        {
            let target = environment.substitutions.get(&name).unwrap_or(&name);
            if let Some(callee) = environment.definitions.get(target) {
                if args
                    .iter()
                    .any(|argument| reaches_in(argument, environment, builtins, None))
                {
                    return true;
                }
                if seen.insert(Rc::as_ptr(callee) as usize) {
                    pending.push(callee.body.clone());
                }
            }
        } else if let Some(name) = expression.reference()
            && !expression.is_locally_resolved()
        {
            let target = environment.substitutions.get(&name).unwrap_or(&name);
            if let Some(callee) = environment.definitions.get(target)
                && seen.insert(Rc::as_ptr(callee) as usize)
            {
                pending.push(callee.body.clone());
            }
        }
        pending.extend(expression.children());
    }
    false
}

#[cfg(test)]
fn old_passes_effect(expression: &Expr, environment: &Environment, builtins: &[&str]) -> bool {
    let mut seen = FastSet::default();
    let mut pending = vec![expression.clone()];
    while let Some(expression) = pending.pop() {
        if let ExpressionKind::Apply { args, .. } = &expression.kind
            && let Some(name) = expression.reference()
            && !expression.is_locally_resolved()
        {
            let target = environment.substitutions.get(&name).unwrap_or(&name);
            if let Some(callee) = environment.definitions.get(target) {
                if args
                    .iter()
                    .any(|argument| reaches_in(argument, environment, builtins, None))
                {
                    return true;
                }
                if seen.insert(Rc::as_ptr(callee) as usize) {
                    pending.push(callee.body.clone());
                }
            }
        } else if let Some(name) = expression.reference()
            && !expression.is_locally_resolved()
        {
            let target = environment.substitutions.get(&name).unwrap_or(&name);
            if let Some(callee) = environment.definitions.get(target)
                && seen.insert(Rc::as_ptr(callee) as usize)
            {
                pending.push(callee.body.clone());
            }
        }
        pending.extend(expression.children());
    }
    false
}

pub struct Lowering<'a> {
    environment: &'a Environment,
    /// How many branches TLC's liveness checker has, once the model is written with one.
    pub branches: Option<usize>,
    /// The seed TLC seeds its generator with.
    pub random_seed: u64,
    /// Whether the engine declines the TLCExt builtins it checks where it computes them
    /// (`Builtin::DECLINED`), and leaves out of its startup the constant definitions that apply
    /// them.
    pub is_tlcext_declined: bool,
    /// The evaluator of the constant parts of the liveness formula, without which they stay
    /// `NotYet`.
    pub evaluator: Option<&'a crate::eval::Evaluator<'a>>,
    /// Why a trace printed through the ALIAS declines: the ALIAS reads a name a configuration
    /// substitute with effects replaces, which TLC computes again as it prints each state.
    pub alias_decline: Option<String>,
    /// The constant definitions TLC computes and deep-normalizes at startup, by address.
    normalized: FastSet<usize>,
    /// The copies INSTANCEs with substitutions make, by their bodies' addresses.
    substituted_bodies: Option<FastMap<usize, Rc<Definition>>>,
    /// For each of those that a configuration substitutes for a name, by its address, the copy
    /// that name reads (`IrDefinition::CONFIGURED_SUBSTITUTE`).
    substitute_copies: FastMap<usize, Rc<Definition>>,
    facts: DefinitionFacts,
    ranked: RankedTexts<'a>,
    extra_texts: Vec<Name>,
    extra_ids: FastMap<Name, TextId>,
    arena: Vec<Node>,
    top: Vec<NodeId>,
    junctions: HashMap<NodeId, Junction>,
    numerals: HashMap<NodeId, TextId>,
    /// The id of each node written, by address, with the node kept so no other takes it.
    node_ids: FastMap<usize, (Expr, NodeId)>,
    definition_ids: FastMap<usize, Index>,
    definition_queue: Vec<Rc<Definition>>,
    builtins: Vec<IrBuiltin>,
    builtin_ids: FastMap<Name, Index>,
    /// Where the specification reaches the next-state relation through an INSTANCE with
    /// substitutions, which `finish` writes after the definitions, as `lowerToIr` does.
    next_substitution: Option<Location>,
    constants: Vec<Constant>,
    constant_ids: FastMap<Name, Index>,
    values: Vec<Value>,
    scope_ids: FastMap<usize, Index>,
    tlc_order: Vec<i32>,
    scope_queue: Vec<Rc<crate::spec::Scope>>,
    scopes: Vec<IrScope>,
    value_strings: Vec<Name>,
    value_string_ids: FastMap<Name, u32>,
    names: FastMap<Name, (TextId, Resolution)>,
    operators: FastMap<Name, (TextId, Resolution)>,
    /// What TLCEvalDefinition finds for each name it is written with (`Model::evaluated_definitions`).
    evaluated_definitions: Vec<(TextId, EvaluatedDefinition)>,
}

/// The definition of the jar's own Naturals or Integers that a Java method overrides, Nat or
/// Int, whose TLA+ body is `{ }`, parsed from the module's text for its source; none where a
/// file of the user's replaces either module.
fn get_overridden_stub(name: &str, environment: &Environment) -> Option<Rc<Definition>> {
    let module = match name {
        "Nat" => "Naturals",
        "Int" => "Integers",
        _ => return None,
    };
    if ["Naturals", "Integers"]
        .iter()
        .any(|replaced| environment.module_texts.contains_key(*replaced))
    {
        return None;
    }
    let text = crate::get_standard_module(module, crate::TlcVersion::Master)?;
    let parsed = crate::parser::parse_module(text).ok()?;
    parsed
        .definitions
        .iter()
        .find(|definition| &*definition.name == name)
        .filter(|definition| {
            matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty())
                && matches!(&definition.body.kind, ExpressionKind::SetEnumeration(elements) if elements.is_empty())
        })
        .cloned()
}

impl<'a> Lowering<'a> {
    /// `getHumanReadableImage` of a set SYMMETRY permutes, where the module's text shows it is
    /// the image `get_expression_image` gives: the AST keeps neither parentheses nor the token an
    /// operator is written with, so the text between the node's first and last tokens, without
    /// whitespace, must be that image but for parentheses, with no comment. Parentheses around
    /// the node aren't its tokens: SANY gives a parenthesized expression the node of what it
    /// encloses.
    fn get_written_image(&self, expression: &Expression) -> Option<String> {
        let image = get_expression_image(expression)?;
        let range = expression.location.range.as_ref()?;
        let text = self.environment.module_texts.get(&range.module)?.clone()?;
        let start = get_text_offset(&text, range.start.line, range.start.column)?;
        let end = get_text_offset(&text, range.end.line, range.end.column)?;
        let written = text.get(start..=end)?;
        if written.contains("\\*") || written.contains("(*") || written.contains("*)") {
            return None;
        }
        let mut compact = String::with_capacity(written.len());
        let mut in_string = false;
        for character in written.chars() {
            if character == '"' {
                in_string = !in_string;
            }
            if in_string || !character.is_whitespace() {
                compact.push(character);
            }
        }
        // The parentheses within the node are its tokens, which the AST drops: the text then
        // differs from the image only by them, balanced, as a range that starts or ends within
        // them couldn't be.
        (remove_parentheses(&compact)? == remove_parentheses(&image)?).then_some(compact)
    }

    pub fn new(environment: &'a Environment, ranked: RankedTexts<'a>) -> Lowering<'a> {
        let facts = create_definition_facts(environment);
        Lowering {
            branches: None,
            random_seed: 0,
            is_tlcext_declined: false,
            alias_decline: None,
            normalized: environment
                .startup_definitions
                .iter()
                .filter(|definition| is_startup_definition(definition, environment, &facts))
                .map(|definition| Rc::as_ptr(definition) as usize)
                .collect(),
            substitute_copies: FastMap::default(),
            substituted_bodies: None,
            facts,
            environment,
            evaluator: None,
            ranked,
            extra_texts: Vec::new(),
            extra_ids: FastMap::default(),
            arena: Vec::new(),
            top: Vec::new(),
            junctions: HashMap::new(),
            numerals: HashMap::new(),
            node_ids: FastMap::default(),
            definition_ids: FastMap::default(),
            definition_queue: Vec::new(),
            builtins: Vec::new(),
            builtin_ids: FastMap::default(),
            constants: Vec::new(),
            constant_ids: FastMap::default(),
            values: Vec::new(),
            scope_ids: FastMap::default(),
            tlc_order: Vec::new(),
            next_substitution: None,
            scope_queue: Vec::new(),
            scopes: Vec::new(),
            value_strings: Vec::new(),
            value_string_ids: FastMap::default(),
            names: FastMap::default(),
            operators: FastMap::default(),
            evaluated_definitions: Vec::new(),
        }
    }

    pub fn get_text(&mut self, text: &str) -> TextId {
        if let Some(rank) = self.ranked.ranks.get(text) {
            return *rank;
        }
        if let Some(id) = self.extra_ids.get(text) {
            return *id;
        }
        let id = (self.ranked.texts.len() + self.extra_texts.len()) as TextId;
        let text: Name = Rc::from(text);
        self.extra_texts.push(text.clone());
        self.extra_ids.insert(text, id);
        id
    }

    /// What `TLCExt.tlcDefByName` finds for a name written as TLCEvalDefinition's argument:
    /// `ModuleNode.getOpDef` of the root module, whose definitions are those the root module
    /// defines, extends or instantiates (`getOpDefs`), and then the body as written, or the
    /// signature of one with parameters. A name that a configuration substitutes for or assigns,
    /// that a Java method overrides, that a standard module defines, of a function, or whose body
    /// has effects or warns the IR doesn't list, as the front end doesn't know what TLC finds or
    /// computes for it then.
    fn look_up_evaluated_definition(&mut self, name: &str) {
        let text = self.get_text(name);
        if self
            .evaluated_definitions
            .iter()
            .any(|(known, _)| *known == text)
        {
            return;
        }
        let environment = self.environment;
        let found = match environment.root_symbols.get(name) {
            None => Some(EvaluatedDefinition::Missing),
            Some(symbol) if symbol.kind != SymbolKind::Definition => {
                // A constant, a variable, an instance or a theorem is no OpDefNode; a builtin of
                // a standard module is one whose TLA+ body the IR doesn't hold.
                matches!(
                    symbol.kind,
                    SymbolKind::Constant | SymbolKind::Variable | SymbolKind::Theorem
                )
                .then_some(EvaluatedDefinition::Missing)
            }
            // Nat and Int of the jar's own Naturals and Integers, which a Java method overrides:
            // `opDef.getBody()` is the `{ }` their modules write, which TLC evaluates as written.
            Some(symbol)
                if symbol.arity == 0
                    && !environment.definitions.contains_key(&symbol.key)
                    && !environment.substitutions.contains_key(&symbol.key)
                    && !environment.constants.contains_key(&symbol.key)
                    && environment
                        .builtins
                        .get(&symbol.key)
                        .is_some_and(|builtin| &*builtin.name == name) =>
            {
                get_overridden_stub(name, environment).map(|definition| {
                    EvaluatedDefinition::Body(self.get_definition_index(&definition))
                })
            }
            Some(symbol) => environment
                .definitions
                .get(&symbol.key)
                .filter(|_| {
                    !environment.substitutions.contains_key(&symbol.key)
                        && !environment.constants.contains_key(&symbol.key)
                        && !environment.operator_constants.contains_key(&symbol.key)
                        && !environment
                            .operator_objects
                            .method_aliases
                            .contains_key(&symbol.key)
                        && !environment.builtins.contains_key(&symbol.key)
                })
                .cloned()
                .and_then(|definition| match &definition.kind {
                    DefinitionKind::Operator { params, .. } if !params.is_empty() => {
                        // `getSignature`: the name, then each parameter as written, which is
                        // `Op(_,_)` for an operator's.
                        let params = params
                            .iter()
                            .map(|param| {
                                let is_written = param.location.is_some()
                                    && param.name.chars().all(|character| {
                                        character.is_ascii_alphanumeric() || character == '_'
                                    });
                                is_written.then(|| match param.arity {
                                    0 => param.name.to_string(),
                                    arity => {
                                        format!("{}({})", param.name, vec!["_"; arity].join(","))
                                    }
                                })
                            })
                            .collect::<Option<Vec<String>>>()?;
                        let signature = self.get_text(&format!("{name}({})", params.join(", ")));
                        Some(EvaluatedDefinition::Signature(signature))
                    }
                    // A function's body is its constructor, which the IR holds as the
                    // definition's bounds and body apart.
                    DefinitionKind::Function { .. } => None,
                    _ if self.facts.is_impure_definition(&definition, environment)
                        || self.facts.may_warn_definition(&definition, environment) =>
                    {
                        None
                    }
                    _ => Some(EvaluatedDefinition::Body(
                        self.get_definition_index(&definition),
                    )),
                }),
        };
        if let Some(found) = found {
            self.evaluated_definitions.push((text, found));
        }
    }

    pub fn get_definition_index(&mut self, definition: &Rc<Definition>) -> Index {
        let address = Rc::as_ptr(definition) as usize;
        if let Some(index) = self.definition_ids.get(&address) {
            return *index;
        }
        let index = self.definition_queue.len() as Index;
        self.definition_ids.insert(address, index);
        self.definition_queue.push(definition.clone());
        index
    }

    fn get_constant_index(&mut self, name: &Name, value: &ConfigValue) -> Result<Index> {
        if let Some(index) = self.constant_ids.get(name) {
            return Ok(*index);
        }
        let index = self.constant_ids.len() as Index;
        self.constant_ids.insert(name.clone(), index);
        let text = self.get_text(name);
        let value = self.normalize(value)?;
        let encoded = self.encode_value(&value);
        self.constants.push(Constant {
            name: text,
            value: Some(encoded),
        });
        Ok(index)
    }

    /// TLC's order of the configuration's values, by the texts' ranks.
    fn order(&self) -> ValueOrder<'_> {
        ValueOrder {
            ranks: &self.ranked.ranks,
        }
    }

    fn normalize(&self, value: &ConfigValue) -> Result<ConfigValue> {
        self.order().normalize(value)
    }

    /// `createStateEncoder`'s `encode` of one value, whose strings and model values name their
    /// texts by their position among the encoder's strings.
    fn encode_value(&mut self, value: &ConfigValue) -> u32 {
        let encoded = self.write_value(value);
        self.push_value(encoded)
    }

    fn push_value(&mut self, value: Value) -> u32 {
        self.values.push(value);
        self.values.len() as u32 - 1
    }

    fn get_value_string(&mut self, text: &str) -> u32 {
        if let Some(index) = self.value_string_ids.get(text) {
            return *index;
        }
        let index = self.value_strings.len() as u32;
        let text: Name = Rc::from(text);
        self.value_string_ids.insert(text.clone(), index);
        self.value_strings.push(text);
        index
    }

    fn write_value(&mut self, value: &ConfigValue) -> Value {
        match value {
            ConfigValue::Boolean(value) => Value::Bool(*value),
            ConfigValue::Number(value) => Value::Int(*value as i32),
            ConfigValue::String(text) => Value::String(self.get_value_string(text)),
            ConfigValue::ModelValue(name) => Value::ModelValue(self.get_value_string(name)),
            ConfigValue::Set(elements) => Value::Set(
                elements
                    .iter()
                    .map(|element| self.write_value(element))
                    .collect(),
            ),
            // A record is TLC's RecordValue, class 3, its names before its values.
            ConfigValue::Record(fields) => {
                let domain = fields
                    .iter()
                    .map(|(name, _)| Value::String(self.get_value_string(name)))
                    .collect();
                Value::Function {
                    class: 3,
                    domain,
                    range: fields
                        .iter()
                        .map(|(_, value)| self.write_value(value))
                        .collect(),
                }
            }
        }
    }

    fn get_builtin_index(&mut self, name: &Name) -> Option<Index> {
        if let Some(index) = self.builtin_ids.get(name) {
            return Some(*index);
        }
        let builtin = self.environment.builtins.get(name)?.clone();
        let index = self.builtin_ids.len() as Index;
        self.builtin_ids.insert(name.clone(), index);
        let builtin_name = (match builtin.intrinsic {
            Some(crate::environment::Intrinsic::Any) => "Any",
            Some(
                crate::environment::Intrinsic::DefnsBuiltin
                | crate::environment::Intrinsic::StandardMethod,
            ) => &builtin.name,
            None => self
                .environment
                .operator_objects
                .method_aliases
                .get(name)
                .filter(|_| self.environment.operator_objects.is_admitted)
                .map_or(name, |method| &method.builtin.name),
        })
        .to_owned();
        let text = self.get_text(&builtin_name);
        // `getValue` of each row's arguments as a tuple, and of its value.
        let table = builtin.table.as_ref().map(|rows| {
            rows.iter()
                .map(|(args, value)| {
                    let args: Option<Vec<ConfigValue>> =
                        args.iter().map(|arg| self.normalize(arg).ok()).collect();
                    let tuple = args.map(|args| {
                        let range = args.iter().map(|arg| self.write_value(arg)).collect();
                        self.push_value(Value::IntervalFunction {
                            class: 2,
                            low: 1,
                            range,
                        })
                    });
                    let value = self
                        .normalize(value)
                        .ok()
                        .map(|value| self.encode_value(&value));
                    (tuple, value)
                })
                .collect::<Vec<_>>()
        });
        let mut flags = builtin.flags as i32
            | (if self.environment.pinned_standard_sources
                && self.environment.operator_objects.is_complete
                && self
                    .environment
                    .modules
                    .iter()
                    .all(|module| !crate::model::has_unlinked_instances(module))
                && builtin.flags & !(IrBuiltin::STATE_LEVEL as u32) == 0
                && builtin.arity == 1
                && table.is_none()
                && self.environment.has_json_source_opcode(name, &builtin_name)
            {
                IrBuiltin::PINNED_STANDARD_SOURCES
            } else {
                0
            })
            | table.as_ref().map_or(0, |_| IrBuiltin::TABLE)
            | builtin
                .table
                .as_ref()
                .filter(|rows| {
                    builtin.flags == 0
                        && builtin.arity > 0
                        && !rows.is_empty()
                        && rows.iter().all(|(arguments, _)| !arguments.is_empty())
                        && self.environment.operator_objects.knows_table(rows)
                })
                .map_or(0, |_| IrBuiltin::TABLE_PHASE_KNOWN);
        if name.as_ref() != "TLCDefer"
            || builtin.arity != 1
            || flags & (IrBuiltin::TABLE | IrBuiltin::DECLINED | IrBuiltin::EXTERNAL_CLASS) != 0
        {
            flags &= !IrBuiltin::PACKAGED_TLC_DEFER;
        }
        self.builtins.push(IrBuiltin {
            name: text,
            arity: builtin.arity as i32,
            flags,
            table: table.unwrap_or_default(),
        });
        Some(index)
    }

    /// What `compileIdentifier` finds for a name nothing binds: a variable, a constant, a
    /// definition, or a builtin, through the model's substitutions.
    fn resolve_name(&mut self, name: &Name) -> Result<Resolution> {
        if let Some(variable) = self.environment.variable_index.get(name) {
            return Ok(Resolution::Variable(*variable as u32));
        }
        // `processConstants` applies the configuration's substitutions after its values, so a
        // root constant it substitutes a name for (`c <- m`) holds what `defns` holds for that
        // name, whatever value it also assigns the constant: another root constant's value, a
        // definition's value (`defns` holds the value it assigns a root definition, but where a
        // Java method replaces that definition), or a definition.
        let is_root_constant = |name: &Name| {
            self.environment
                .root_constants
                .iter()
                .any(|declaration| declaration.name == *name && declaration.arity == 0)
        };
        if is_root_constant(name)
            && let Some(target) = self.environment.substitutions.get(name)
        {
            let is_valued = is_root_constant(target)
                || (self.environment.configured_value_bindings.contains(target)
                    && !self.environment.has_java_override_index);
            if is_valued && let Some(value) = self.environment.constants.get(target) {
                let value = value.clone();
                return Ok(Resolution::Constant(self.get_constant_index(name, &value)?));
            }
            return Ok(self.resolve_operator(name));
        }
        if let Some(value) = self.environment.constants.get(name) {
            let value = value.clone();
            return Ok(Resolution::Constant(self.get_constant_index(name, &value)?));
        }
        Ok(self.resolve_operator(name))
    }

    /// What `compileApply` finds for an operator nothing binds: a definition, else a builtin.
    fn resolve_operator(&mut self, name: &Name) -> Resolution {
        let target = self
            .environment
            .substitutions
            .get(name)
            .cloned()
            .unwrap_or_else(|| name.clone());
        if let Some(definition) = self.environment.definitions.get(&target).cloned() {
            let address = Rc::as_ptr(&definition) as usize;
            // Only where the body is pure, whose value a read computes again alike but for how
            // TLC holds it: the engine keeps a body with effects, draws or TLC's registers to the
            // startup value it follows otherwise.
            let definition = if target != *name
                && self.normalized.contains(&address)
                && !self
                    .facts
                    .is_impure_definition(&definition, self.environment)
                && !self
                    .facts
                    .may_warn_definition(&definition, self.environment)
                && !reaches_in(
                    &definition.body,
                    self.environment,
                    &["TLCEval", "TLCGet", "TLCSet", "TLCCache", "TLCGetOrDefault"],
                    None,
                ) {
                self.substitute_copies
                    .entry(address)
                    .or_insert_with(|| Rc::new((*definition).clone()))
                    .clone()
            } else {
                definition
            };
            return Resolution::Definition(self.get_definition_index(&definition));
        }
        self.get_builtin_index(&target)
            .map_or(Resolution::None, Resolution::Builtin)
    }

    fn write_name(&mut self, name: &Name, is_operator: bool, is_local: bool) -> Result<IrName> {
        let cache = if is_operator {
            &self.operators
        } else {
            &self.names
        };
        let (text, resolution) = match cache.get(name) {
            Some(entry) => *entry,
            None => {
                let text = self.get_text(name);
                let resolution = if is_operator {
                    self.resolve_operator(name)
                } else {
                    self.resolve_name(name)?
                };
                let cache = if is_operator {
                    &mut self.operators
                } else {
                    &mut self.names
                };
                cache.insert(name.clone(), (text, resolution));
                (text, resolution)
            }
        };
        Ok(IrName {
            text,
            resolution,
            is_local,
        })
    }

    /// A name nothing global resolves is one a scope binds, as a definition an INSTANCE in a LET
    /// copies in under a key the resolver leaves alone, so `ir.ts` writes it as local.
    fn write_bound_name(
        &mut self,
        name: &Name,
        is_operator: bool,
        is_local: bool,
    ) -> Result<IrName> {
        let name = self.write_name(name, is_operator, is_local)?;
        Ok(IrName {
            is_local: name.is_local || name.resolution == Resolution::None,
            ..name
        })
    }

    fn write_texts(&mut self, texts: &[Name]) -> Vec<TextId> {
        texts.iter().map(|text| self.get_text(text)).collect()
    }

    fn write_nodes(&mut self, expressions: &[Expr]) -> Result<Vec<NodeId>> {
        expressions
            .iter()
            .map(|expression| self.write_node(expression))
            .collect()
    }

    fn write_pattern(&mut self, pattern: &BoundPattern) -> Pattern {
        match pattern {
            BoundPattern::Name { name, .. } => Pattern::Name(self.get_text(name)),
            BoundPattern::Tuple { names, .. } => Pattern::Tuple(self.write_texts(names)),
        }
    }

    fn write_bounds(&mut self, bounds: &[Bound]) -> Result<Vec<IrBound>> {
        bounds
            .iter()
            .map(|bound| {
                let pattern = self.write_pattern(&bound.pattern);
                Ok(IrBound {
                    pattern,
                    set: self.write_node(&bound.set)?,
                })
            })
            .collect()
    }

    fn write_range(&mut self, range: Option<&SourceRange>) -> Option<IrRange> {
        let range = range?;
        Some(IrRange {
            module: self.get_text(&range.module),
            start_line: range.start.line as i32,
            start_column: range.start.column as i32,
            end_line: range.end.line as i32,
            end_column: range.end.column as i32,
        })
    }

    /// Adds a node to the arena before its children, as the blob holds it, and returns its id.
    fn open(&mut self, location: &Location) -> NodeId {
        let id = self.arena.len() as NodeId;
        self.arena.push(Node {
            line: location.line as i32,
            column: location.column as i32,
            range: None,
            kind: NodeKind::ExceptAt,
        });
        let range = self.write_range(location.range.as_ref());
        self.arena[id as usize].range = range;
        id
    }

    fn write_definition(&mut self, definition: &Rc<Definition>) -> Result<NodeId> {
        let is_repeated = self
            .facts
            .has_repeated_definition_effect(definition, self.environment);
        let flags = if definition.is_recursive {
            IrDefinition::RECURSIVE
        } else {
            0
        } | if definition.is_local {
            IrDefinition::LOCAL
        } else {
            0
        } | if definition.is_self_referential.get() == Some(true) {
            IrDefinition::SELF_REFERENTIAL
        } else {
            0
        } | if is_repeated {
            IrDefinition::REPEATED_EFFECT
        } else {
            0
        } | if self.facts.may_warn_definition(definition, self.environment)
            && !self
                .facts
                .is_impure_definition(definition, self.environment)
        {
            IrDefinition::STARTUP_WARNING_ONLY
        } else {
            0
        } | if self.environment.is_substituted(definition) {
            IrDefinition::SUBSTITUTED
        } else {
            0
        } | if self.environment.is_nested_substitution(definition) {
            IrDefinition::NESTED_SUBSTITUTION
        } else {
            0
        } | if self.environment.is_recomputed_substitute(definition) {
            IrDefinition::NAMED_AT_STARTUP
        } else {
            0
        } | if self.normalized.contains(&(Rc::as_ptr(definition) as usize)) {
            IrDefinition::NORMALIZED
        } else {
            0
        } | if is_held_literal(definition, self.environment) {
            IrDefinition::LITERAL
        } else {
            0
        } | if self
            .substitute_copies
            .values()
            .any(|copy| Rc::ptr_eq(copy, definition))
        {
            IrDefinition::CONFIGURED_SUBSTITUTE
        } else {
            0
        };
        let id = self.open(&definition.location);
        let name = self.get_text(&definition.name);
        let form = match &definition.kind {
            DefinitionKind::Operator { params, .. } => DefinitionForm::Operator(
                params
                    .iter()
                    .map(|param| Param {
                        name: self.get_text(&param.name),
                        arity: param.arity as i32,
                    })
                    .collect(),
            ),
            DefinitionKind::Function { bounds } => {
                DefinitionForm::Function(self.write_bounds(bounds)?)
            }
        };
        let body = self.write_node(&definition.body)?;
        self.arena[id as usize].kind = NodeKind::Definition(IrDefinition {
            name,
            flags,
            form,
            body,
        });
        Ok(id)
    }

    fn write_configured_operator(
        &mut self,
        name: &Name,
        location: &Location,
        is_local: bool,
    ) -> Result<Option<NodeKind>> {
        if is_local {
            return Ok(None);
        }
        let target = self.environment.substitutions.get(name).unwrap_or(name);
        let Some(value) = self.environment.operator_constants.get(target).cloned() else {
            return Ok(None);
        };
        let target = target.clone();
        let arity = self
            .environment
            .builtins
            .get(&target)
            .map_or(0, |builtin| builtin.arity);
        let value = self.get_constant_index(&target, &value)?;
        let body = self.open(location);
        let text = self.get_text(name);
        self.arena[body as usize].kind = NodeKind::Identifier(IrName {
            text,
            resolution: Resolution::Constant(value),
            is_local: false,
        });
        let params = (0..arity)
            .map(|index| self.get_text(&format!("\0configuration-argument:{index}")))
            .collect();
        Ok(Some(NodeKind::Lambda { params, body }))
    }

    pub fn write_node(&mut self, expression: &Expr) -> Result<NodeId> {
        let address = Rc::as_ptr(expression) as usize;
        if let Some((_, known)) = self.node_ids.get(&address) {
            let known = *known;
            let id = self.arena.len() as NodeId;
            self.arena.push(Node {
                line: 0,
                column: 0,
                range: None,
                kind: NodeKind::Reference(known),
            });
            return Ok(id);
        }
        if let Some((location, substitute)) = self.environment.tables.substitute_use(expression)
            && location.range.is_some()
        {
            // The substitute is written once, outside the nodes that use it, which refer to it.
            let mut target = self.write_root(&substitute)?;
            while let NodeKind::Reference(known) = self.arena[target as usize].kind {
                target = known;
            }
            let id = self.open(&location);
            self.arena[id as usize].kind = NodeKind::Reference(target);
            self.node_ids.insert(address, (expression.clone(), id));
            return Ok(id);
        }
        let selection = self.environment.tables.selection_location(expression);
        let id = self.open(selection.as_ref().unwrap_or(&expression.location));
        self.node_ids.insert(address, (expression.clone(), id));
        let is_local = expression.resolved.is_local.get();
        let kind = match &expression.kind {
            ExpressionKind::Number { .. } | ExpressionKind::String { .. }
                if self.environment.uninitialized_literals.contains(&address) =>
            {
                let marker: Name = Rc::from("$UninitializedLiteral");
                let index = if let Some(&index) = self.builtin_ids.get(&marker) {
                    index
                } else {
                    let index = self.builtins.len() as Index;
                    let name = self.get_text(&marker);
                    self.builtin_ids.insert(marker, index);
                    self.builtins.push(IrBuiltin {
                        name,
                        arity: 0,
                        flags: IrBuiltin::DECLINED | IrBuiltin::UNINITIALIZED_LITERAL,
                        table: Vec::new(),
                    });
                    index
                };
                NodeKind::Identifier(IrName {
                    text: self.builtins[index as usize].name,
                    resolution: Resolution::Builtin(index),
                    is_local: false,
                })
            }
            ExpressionKind::Number { value, text } => {
                if value.fract() == 0.0
                    && *value >= f64::from(i32::MIN)
                    && *value <= f64::from(i32::MAX)
                {
                    // SANY's `NumeralNode` keeps its image, which TLC prints where it prints the
                    // node (`<expression 007>`).
                    if **text != *(*value as i32).to_string() {
                        let image = self.get_text(text);
                        self.numerals.insert(id, image);
                    }
                    NodeKind::Number(*value as i32)
                } else {
                    NodeKind::WideNumber(self.get_text(text))
                }
            }
            ExpressionKind::Decimal { text } => NodeKind::Decimal(self.get_text(text)),
            ExpressionKind::String { value } => NodeKind::String(self.get_text(value)),
            ExpressionKind::Identifier { .. } => {
                let name = expression.reference().unwrap_or_default();
                match self.write_configured_operator(&name, &expression.location, is_local)? {
                    Some(operator) => operator,
                    None => NodeKind::Identifier(self.write_bound_name(&name, false, is_local)?),
                }
            }
            ExpressionKind::Apply { args, .. } => {
                let reference = expression.reference().unwrap_or_default();
                let name = self.write_bound_name(&reference, true, is_local)?;
                let target = self
                    .environment
                    .substitutions
                    .get(&reference)
                    .unwrap_or(&reference);
                match self.environment.operator_constants.get(target) {
                    // `Tool.evalAppl` gives an operator the configuration assigns a value that
                    // value, without evaluating its arguments.
                    Some(value) if matches!(name.resolution, Resolution::Builtin(_)) => {
                        let (target, value) = (target.clone(), value.clone());
                        NodeKind::Identifier(IrName {
                            resolution: Resolution::Constant(
                                self.get_constant_index(&target, &value)?,
                            ),
                            ..name
                        })
                    }
                    _ => {
                        if let [argument] = args.as_slice()
                            && let ExpressionKind::String { value } = &argument.kind
                            && get_plain_builtin(expression, self.environment)
                                == Some("TLCEvalDefinition")
                        {
                            self.look_up_evaluated_definition(value);
                        }
                        NodeKind::Apply {
                            name,
                            args: self.write_nodes(args)?,
                        }
                    }
                }
            }
            ExpressionKind::OperatorReference { .. } => {
                let name = expression.reference().unwrap_or_default();
                match self.write_configured_operator(&name, &expression.location, is_local)? {
                    Some(operator) => operator,
                    None => NodeKind::OperatorReference(self.write_name(&name, true, false)?),
                }
            }
            ExpressionKind::Lambda { params, body, .. } => {
                let params = self.write_texts(params);
                NodeKind::Lambda {
                    params,
                    body: self.write_node(body)?,
                }
            }
            ExpressionKind::Junction {
                is_and,
                operands,
                is_bulleted,
                prefix_ends,
            } => {
                self.junctions.insert(
                    id,
                    Junction {
                        is_bulleted: *is_bulleted,
                        prefix_ends: prefix_ends
                            .iter()
                            .flatten()
                            .map(|end| (end.line as i32, end.column as i32))
                            .collect(),
                    },
                );
                let operands = self.write_nodes(operands)?;
                if *is_and {
                    NodeKind::And(operands)
                } else {
                    NodeKind::Or(operands)
                }
            }
            ExpressionKind::Prime(inner) => NodeKind::Prime(self.write_node(inner)?),
            ExpressionKind::Unchanged(inner) => NodeKind::Unchanged(self.write_node(inner)?),
            ExpressionKind::Enabled(inner) => NodeKind::Enabled(self.write_node(inner)?),
            ExpressionKind::Always(inner) => NodeKind::Always(self.write_node(inner)?),
            ExpressionKind::Eventually(inner) => NodeKind::Eventually(self.write_node(inner)?),
            ExpressionKind::If {
                condition,
                consequent,
                alternative,
            } => NodeKind::If {
                condition: self.write_node(condition)?,
                consequent: self.write_node(consequent)?,
                alternative: self.write_node(alternative)?,
            },
            ExpressionKind::Case { arms, other } => {
                let arms = arms
                    .iter()
                    .map(|arm| {
                        Ok((
                            self.write_node(&arm.condition)?,
                            self.write_node(&arm.body)?,
                        ))
                    })
                    .collect::<Result<Vec<_>>>()?;
                let other = other
                    .as_ref()
                    .map(|other| self.write_node(other))
                    .transpose()?;
                NodeKind::Case { arms, other }
            }
            ExpressionKind::Let {
                definitions,
                instances,
                body,
                ..
            } => {
                // The compiler refuses an INSTANCE in a LET, so only how many there are is kept.
                let definitions = definitions
                    .iter()
                    .map(|definition| self.write_definition(definition))
                    .collect::<Result<Vec<_>>>()?;
                NodeKind::Let {
                    instances: instances.as_ref().map_or(0, Vec::len) as u32,
                    definitions,
                    body: self.write_node(body)?,
                }
            }
            ExpressionKind::Quantified {
                quantifier,
                bounds,
                body,
            } => {
                let bounds = self.write_bounds(bounds)?;
                let body = self.write_node(body)?;
                match quantifier {
                    Quantifier::Forall => NodeKind::Forall { bounds, body },
                    Quantifier::Exists => NodeKind::Exists { bounds, body },
                }
            }
            ExpressionKind::UnboundedQuantifier {
                quantifier,
                names,
                is_temporal,
                body,
                ..
            } => {
                let names = self.write_texts(names);
                NodeKind::UnboundedQuantifier {
                    is_forall: *quantifier == Quantifier::Forall,
                    is_temporal: *is_temporal,
                    names,
                    body: self.write_node(body)?,
                }
            }
            ExpressionKind::Choose { pattern, set, body } => {
                let pattern = self.write_pattern(pattern);
                let set = set.as_ref().map(|set| self.write_node(set)).transpose()?;
                NodeKind::Choose {
                    pattern,
                    set,
                    body: self.write_node(body)?,
                }
            }
            ExpressionKind::SetEnumeration(elements) => {
                NodeKind::SetEnumeration(self.write_nodes(elements)?)
            }
            ExpressionKind::Tuple(elements) => NodeKind::Tuple(self.write_nodes(elements)?),
            ExpressionKind::SetFilter { bound, predicate } => {
                let bound = self
                    .write_bounds(std::slice::from_ref(bound))?
                    .pop()
                    .expect("one bound");
                NodeKind::SetFilter {
                    bound,
                    predicate: self.write_node(predicate)?,
                }
            }
            ExpressionKind::SetMap {
                expression: mapped,
                bounds,
            } => {
                let expression = self.write_node(mapped)?;
                NodeKind::SetMap {
                    expression,
                    bounds: self.write_bounds(bounds)?,
                }
            }
            ExpressionKind::FunctionConstruction { bounds, body } => {
                let bounds = self.write_bounds(bounds)?;
                NodeKind::FunctionConstruction {
                    is_recursive: expression.resolved.is_recursive.get(),
                    bounds,
                    body: self.write_node(body)?,
                }
            }
            ExpressionKind::FunctionSet { domain, range } => NodeKind::FunctionSet {
                domain: self.write_node(domain)?,
                range: self.write_node(range)?,
            },
            ExpressionKind::Record { is_set, fields } => {
                let fields = fields
                    .iter()
                    .map(|field| {
                        let name = self.get_text(&field.name);
                        Ok((name, self.write_node(&field.value)?))
                    })
                    .collect::<Result<Vec<_>>>()?;
                if *is_set {
                    NodeKind::RecordSet(fields)
                } else {
                    NodeKind::Record(fields)
                }
            }
            ExpressionKind::Except { function, updates } => {
                let function = self.write_node(function)?;
                let updates = updates
                    .iter()
                    .map(|update| {
                        let path = update
                            .path
                            .iter()
                            .map(|step| {
                                Ok(match step {
                                    ExceptPathStep::Field(name) => {
                                        PathStep::Field(self.get_text(name))
                                    }
                                    ExceptPathStep::Index(args) => {
                                        PathStep::Index(self.write_nodes(args)?)
                                    }
                                })
                            })
                            .collect::<Result<Vec<_>>>()?;
                        Ok(Update {
                            path,
                            value: self.write_node(&update.value)?,
                        })
                    })
                    .collect::<Result<Vec<_>>>()?;
                NodeKind::Except { function, updates }
            }
            ExpressionKind::ExceptAt => NodeKind::ExceptAt,
            ExpressionKind::FunctionApplication { function, args } => {
                NodeKind::FunctionApplication {
                    function: self.write_node(function)?,
                    args: self.write_nodes(args)?,
                }
            }
            ExpressionKind::Bracket(args) => NodeKind::Bracket(self.write_nodes(args)?),
            ExpressionKind::FieldAccess { record, field } => {
                let record = self.write_node(record)?;
                NodeKind::FieldAccess {
                    record,
                    field: self.get_text(field),
                }
            }
            ExpressionKind::Product(factors) => NodeKind::Product(self.write_nodes(factors)?),
            ExpressionKind::Action {
                is_box,
                action,
                subscript,
            } => {
                let action = self.write_node(action)?;
                let subscript = self.write_node(subscript)?;
                if *is_box {
                    NodeKind::BoxAction { action, subscript }
                } else {
                    NodeKind::AngleAction { action, subscript }
                }
            }
            ExpressionKind::Fairness {
                is_strong,
                subscript,
                action,
                enabled,
            } => {
                let subscript = self.write_node(subscript)?;
                let action = self.write_node(action)?;
                let enabled = enabled
                    .as_ref()
                    .map(|enabled| self.write_node(enabled))
                    .transpose()?;
                if *is_strong {
                    NodeKind::StrongFairness {
                        subscript,
                        action,
                        enabled,
                    }
                } else {
                    NodeKind::WeakFairness {
                        subscript,
                        action,
                        enabled,
                    }
                }
            }
            ExpressionKind::Label {
                name, params, body, ..
            } => {
                let name = self.get_text(name);
                let params = self.write_texts(params);
                NodeKind::Label {
                    name,
                    params,
                    body: self.write_node(body)?,
                }
            }
            ExpressionKind::Subexpression { selectors, .. }
                if let Some(clause) = self.get_goal_clause(expression, selectors) =>
            {
                let body = self.write_node(&clause)?;
                self.get_nop(body)
            }
            ExpressionKind::Subexpression { selectors, .. } => NodeKind::Subexpression(
                selectors
                    .iter()
                    .map(|selector| {
                        Ok(match selector {
                            Selector::Name { name, args } => {
                                let name = self.get_text(name);
                                IrSelector::Name {
                                    name,
                                    args: self.write_nodes(args)?,
                                }
                            }
                            Selector::Operand(Operand::Index(index)) => {
                                IrSelector::Operand(*index as i32)
                            }
                            Selector::Operand(Operand::First) => IrSelector::Operand(-1),
                            Selector::Operand(Operand::Last) => IrSelector::Operand(-2),
                            Selector::Bound(args) => IrSelector::Bound(self.write_nodes(args)?),
                            Selector::At => IrSelector::At,
                            Selector::Colon => IrSelector::Colon,
                        })
                    })
                    .collect::<Result<Vec<_>>>()?,
            ),
        };
        let substitution = self.get_selection_substitution(expression);
        let kind = match (kind, substitution) {
            // The LAMBDA's application: its body is under the `SubstInNode`.
            (
                NodeKind::Let {
                    instances,
                    definitions,
                    body,
                },
                Some(location),
            ) if selection.is_none() && definitions.len() == 1 => {
                let node = definitions[0] as usize;
                if let NodeKind::Definition(definition) = &self.arena[node].kind {
                    let inner = definition.body;
                    let wrapped = self.wrap_substitution(inner, &location);
                    if let NodeKind::Definition(definition) = &mut self.arena[node].kind {
                        definition.body = wrapped;
                    }
                }
                NodeKind::Let {
                    instances,
                    definitions,
                    body,
                }
            }
            (kind, _) => kind,
        };
        self.arena[id as usize].kind = if selection.is_some() {
            let body = self.open(&expression.location);
            self.arena[body as usize].kind = kind;
            let body = match self.get_selection_substitution(expression) {
                Some(location) => self.wrap_substitution(body, &location),
                None => body,
            };
            self.get_nop(body)
        } else {
            kind
        };
        Ok(id)
    }

    /// Where a selection passes through the copy an INSTANCE with substitutions makes of a
    /// definition, as `I!Op(1)!lab` does: SANY's node of the selected part is within the copy's
    /// `SubstInNode` (`Generator.selectorToNode`), which `CallStackTool` pushes as a frame at the
    /// INSTANCE right after the selection's own. The INSTANCE, for a selection through one such
    /// copy that isn't itself a copy's copy.
    fn get_selection_substitution(&self, expression: &Expr) -> Option<Location> {
        let tables = &self.environment.tables;
        if !tables.is_selection(expression) {
            return None;
        }
        let origins: Vec<Rc<Definition>> = tables
            .selection_origins(expression)
            .iter()
            .map(|origin| tables.alias_source(origin))
            .collect();
        let mut substituted = origins
            .iter()
            .filter(|origin| self.environment.is_substituted(origin));
        let origin = substituted.next()?;
        if substituted.next().is_some() || self.environment.is_nested_substitution(origin) {
            return None;
        }
        let (key, _) = (self.environment.definitions.iter())
            .find(|(_, definition)| Rc::ptr_eq(definition, origin))?;
        let action = self.environment.instance_actions.get(key)?;
        action.location.range.as_ref()?;
        Some(action.location.clone())
    }

    /// SANY's `SubstInNode` over a node: a `$Nop` at the INSTANCE.
    fn wrap_substitution(&mut self, node: NodeId, location: &Location) -> NodeId {
        let wrapper = self.open(location);
        self.arena[wrapper as usize].kind = self.get_nop(node);
        wrapper
    }

    /// SANY's `$Nop` application a selection makes of what it selects.
    fn get_nop(&mut self, body: NodeId) -> NodeKind {
        {
            let marker: Name = Rc::from("$Nop");
            let index = if let Some(&index) = self.builtin_ids.get(&marker) {
                index
            } else {
                let index = self.builtins.len() as Index;
                let name = self.get_text(&marker);
                self.builtin_ids.insert(marker, index);
                self.builtins.push(IrBuiltin {
                    name,
                    arity: 1,
                    flags: 0,
                    table: Vec::new(),
                });
                index
            };
            NodeKind::Apply {
                name: IrName {
                    text: self.builtins[index as usize].name,
                    resolution: Resolution::Builtin(index),
                    is_local: false,
                },
                args: vec![body],
            }
        }
    }

    /// `Generator.selectorToNode` of `T!i` for a theorem `T` whose statement is an ASSUME/PROVE
    /// of expressions: its `i`th assumption, or its goal after them, which it selects as it
    /// selects an operand of an expression.
    fn get_goal_clause(&self, expression: &Expression, selectors: &[Selector]) -> Option<Expr> {
        let [
            Selector::Name { name, args },
            Selector::Operand(Operand::Index(index)),
        ] = selectors
        else {
            return None;
        };
        if !args.is_empty() {
            return None;
        }
        let module = &expression.location.range.as_ref()?.module;
        // The modules as linking resolved them, an inner one among them.
        let mut found = self
            .environment
            .modules
            .iter()
            .filter(|candidate| candidate.name == *module);
        let (Some(found), None) = (found.next(), found.next()) else {
            return None;
        };
        let theorem = found
            .theorems
            .iter()
            .find(|theorem| theorem.name.as_ref() == Some(name))?;
        let Statement::AssumeProve(assume_prove) = &theorem.statement else {
            return None;
        };
        let assumptions = assume_prove
            .assumptions
            .iter()
            .map(|assumed| match assumed {
                Assumed::Expression(expression) => Some(expression.clone()),
                _ => None,
            })
            .collect::<Option<Vec<_>>>()?;
        if index.fract() != 0.0 || *index < 1.0 || *index > 1e9 {
            return None;
        }
        let position = *index as usize - 1;
        match position.cmp(&assumptions.len()) {
            std::cmp::Ordering::Less => Some(assumptions[position].clone()),
            std::cmp::Ordering::Equal => Some(assume_prove.conclusion.clone()),
            std::cmp::Ordering::Greater => None,
        }
    }

    /// Writes an expression something outside the nodes refers to, unless it is written already,
    /// and returns its id.
    pub fn write_root(&mut self, expression: &Expr) -> Result<NodeId> {
        if let Some((_, known)) = self.node_ids.get(&(Rc::as_ptr(expression) as usize)) {
            return Ok(*known);
        }
        let id = self.write_node(expression)?;
        self.top.push(id);
        // The copy an INSTANCE with substitutions makes whose body the root is, which TLC places
        // at the INSTANCE as it reports the root.
        let copies = self.substituted_bodies.get_or_insert_with(|| {
            (self.environment.definitions.values())
                .filter(|definition| self.environment.is_substituted(definition))
                .map(|definition| (Rc::as_ptr(&definition.body) as usize, definition.clone()))
                .collect()
        });
        if let Some(copy) = copies.get(&(Rc::as_ptr(expression) as usize)).cloned() {
            self.get_definition_index(&copy);
        }
        Ok(id)
    }

    /// A name the configuration gives, and the definition it names, as `writeConfigNames` writes
    /// it, with whether evaluating it again can show.
    pub fn config_name(&mut self, name: &str) -> Printed<ConfigName> {
        let key: Name = Rc::from(name);
        let definition = self
            .environment
            .definitions
            .get(self.environment.substitutions.get(&key).unwrap_or(&key))
            .cloned();
        let text = self.get_text(name);
        let definition = definition.map(|definition| self.get_definition_index(&definition));
        let identifier = Rc::new(Expression::new(
            ExpressionKind::Identifier {
                name: key,
                spelling: None,
                selector_ranges: None,
            },
            Location {
                line: 0,
                column: 0,
                range: None,
            },
        ));
        Printed {
            root: ConfigName {
                name: text,
                definition,
            },
            has_repeated_effect: self
                .facts
                .has_repeated_effect(&identifier, self.environment),
        }
    }

    /// Writes the definitions the model reaches, each reaching more in the order first met, and
    /// returns the IR with the model.
    /// The model section, as `lowerToIr` writes it in its order, for a model whose next-state
    /// relation the engine splits itself, so with no actions of TLC's.
    pub fn write_model(
        &mut self,
        config: &crate::config::ModelConfig,
        specification: &crate::spec::Specification,
        properties: &crate::spec::Properties,
        is_warning_enabled: bool,
        version: Option<&str>,
        tlc_order: Vec<i32>,
    ) -> Result<Model> {
        self.tlc_order = tlc_order;
        if !self.environment.missing_operator_bodies.is_empty() {
            let mut preceding_effect = false;
            for definition in &self.environment.startup_definitions {
                if !matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty())
                {
                    continue;
                }
                if reaches_missing_operator_body(definition, self.environment) {
                    if preceding_effect || version.is_some() {
                        return Err(FrontError::NotYet("effects or version-specific startup inspection before an INSTANCE built-in operator body".into()));
                    }
                    return Err(FrontError::Evaluation(format!(
                        "{}java.lang.NullPointerException\n: Cannot invoke \"tla2sany.semantic.SemanticNode.getKind()\" because \"expr\" is null",
                        crate::errors::UNEXPECTED_HEAD
                    )));
                }
                preceding_effect |= startup_receiver_body(definition, self.environment)
                    .is_some_and(|actual| reaches_shown_effect(&actual, self.environment, None));
            }
        }
        self.next_substitution =
            crate::spec::get_next_substitution(config, self.environment, &self.facts)?;
        let not_yet = |reason: &str| FrontError::NotYet(reason.to_owned());
        let Some(init) = &specification.init else {
            return Err(not_yet("a model without Init"));
        };
        let liveness = crate::live::get_liveness(
            &specification.temporals,
            &properties.liveness,
            self.environment,
            &self.facts,
            self.evaluator,
            if version == Some("1.7.4") {
                crate::TlcVersion::V1_7_4
            } else {
                crate::TlcVersion::Master
            },
        )
        // Where a property's \A was unrolled with substitutions TLC leaves unbound, its constant
        // parts may differ from TLC's; and TLC computes the constant definitions as it starts,
        // printing before it fails here, which the front end doesn't follow.
        .map_err(|error| match error {
            FrontError::Evaluation(message)
                if message.starts_with("TLC expected a boolean value")
                    && (properties.is_unrolled || self.has_impure_constant_definition()) =>
            {
                not_yet("a constant part of a temporal formula that isn't a boolean")
            }
            error => error,
        })
        // `createLivenessChecker` runs inside `withUnexpectedException`.
        .map_err(crate::tlc_messages::with_unexpected_exception)
        // TLC computes the symmetry before it starts the liveness checker, which warns that the
        // symmetry is dangerous for liveness before it fails here.
        .map_err(|error| match (error, &config.symmetry) {
            (error @ FrontError::NotYet(_), _) => error,
            (_, Some(name)) if !self.is_symmetry_quiet(config, name, is_warning_enabled) => not_yet(
                "a temporal property TLC rejects after it computes a symmetry it may report on",
            ),
            // TLC computes the constant definitions as it starts, which may print before the
            // warnings, which the front end doesn't follow: it declines a definition without
            // parameters that may print.
            (_, Some(_)) if is_warning_enabled && self.has_impure_constant_definition() => {
                not_yet(
                    "a temporal property TLC rejects after it warns about the symmetry, with a definition TLC may print as it starts",
                )
            }
            (error, symmetry) => FrontError::Warned(
                (symmetry.is_some() && is_warning_enabled)
                    .then(crate::model::get_liveness_symmetry_warning)
                    .into_iter()
                    .collect(),
                Box::new(error),
            ),
        })?;
        let init = self.write_root(init)?;
        let next = match &specification.next {
            Some(next) => Some(self.write_root(next)?),
            None => None,
        };
        let scope = self.get_scope_index(specification.scope.as_ref());
        let invariants = config
            .invariants
            .iter()
            .map(|name| self.config_name(name))
            .collect();
        let mut property_invariants = Vec::new();
        let mut property_invariant_names = Vec::new();
        let mut property_invariant_scopes = Vec::new();
        for invariant in &properties.invariants {
            let root = self.write_root(&invariant.expression)?;
            property_invariant_scopes.push(self.get_scope_index(invariant.scope.as_ref()));
            property_invariants.push(Printed {
                root,
                has_repeated_effect: self
                    .facts
                    .has_repeated_effect(&invariant.expression, self.environment),
            });
            property_invariant_names.push(self.get_text(&invariant.name));
        }
        let constraints = config
            .constraints
            .iter()
            .map(|name| self.config_name(name).root)
            .collect();
        let action_constraints = config
            .action_constraints
            .iter()
            .map(|name| self.config_name(name).root)
            .collect();
        let possible = config
            .possible
            .iter()
            .map(|name| Possible {
                name: self.config_name(name).root,
                is_action: crate::spec::get_level(
                    &crate::spec::create_identifier(name),
                    None,
                    self.environment,
                    &self.facts,
                    &[],
                ) >= crate::dependencies::Level::Action,
            })
            .collect();
        let mut action_properties = Vec::new();
        for property in &properties.action_properties {
            // Keep the box-action node's source range for TLC's DFID call stack.
            self.write_root(&property.wrapper)?;
            let action = self.write_root(&property.action)?;
            let subscript = self.write_root(&property.subscript)?;
            action_properties.push(IrActionProperty {
                action,
                subscript,
                scope: self.get_scope_index(property.scope.as_ref()),
                name: self.get_text(&property.name),
            });
        }
        let mut initial_predicates = Vec::new();
        let mut initial_predicate_scopes = Vec::new();
        let mut initial_predicate_names = Vec::new();
        for predicate in &properties.initial_predicates {
            initial_predicates.push(self.write_root(&predicate.expression)?);
            initial_predicate_names.push(self.get_text(&predicate.name));
            initial_predicate_scopes.push(self.get_scope_index(predicate.scope.as_ref()));
        }
        let view = config
            .view
            .as_deref()
            .map(|name| self.config_name(name).root);
        // TLC holds a name the configuration assigns as its value, which it rejects as the ALIAS
        // (`Spec.getAliasSpec`), unless the configuration also substitutes for it, which TLC applies
        // after (`SpecProcessor.processSpec`): the IR keeps it as a constant, which the trace
        // printer finds, where the front end normalizes the value. An assignment scoped to a
        // module (`= [N] v`) reaches only that module's definitions, which the front end doesn't
        // tell apart, so only an unscoped one counts.
        if let Some(name) = config.alias.as_deref()
            && (config.constants.iter())
                .any(|constant| constant.name == name && constant.module.is_none())
            && !self.environment.substitutions.contains_key(name)
            && (self.environment.definitions.get(name)).is_some_and(|definition| {
                !matches!(
                    definition.kind,
                    DefinitionKind::Operator {
                        body_range: None,
                        ..
                    }
                )
            })
            && let Some(value) = self.environment.constants.get(name).cloned()
            && self.normalize(&value).is_ok()
        {
            self.get_constant_index(&Rc::from(name), &value)?;
        }
        let alias = config
            .alias
            .as_deref()
            .map(|name| self.config_name(name).root);
        // `TLCGet("stats").duration` and `TLCGet("duration")` count the seconds since TLC
        // started (`TLCGetSet.startTime`), which the JVM's own start makes longer than the
        // checker's run, so a postcondition that may read them declines. One TLC doesn't find
        // it reads nothing of, failing as it looks them up (`Spec.getPostConditionSpecs`).
        if config.postconditions.iter().any(|name| {
            let name = self
                .environment
                .substitutions
                .get(name.as_str())
                .map_or(name.as_str(), |target| &**target);
            self.environment
                .definitions
                .get(name)
                .is_some_and(|definition| {
                    may_read_duration(
                        &definition.body,
                        self.environment,
                        true,
                        &mut Vec::new(),
                        &mut Vec::new(),
                        &mut Vec::new(),
                        &mut Vec::new(),
                        &mut FastSet::default(),
                    )
                })
        }) {
            return Err(FrontError::NotYet(
                "a postcondition that may read how long TLC ran".to_owned(),
            ));
        }
        let postconditions = config
            .postconditions
            .iter()
            .map(|name| self.config_name(name).root)
            .collect();
        let version = version.map(|version| self.get_text(version));
        self.branches = liveness.as_ref().map(|liveness| liveness.branches);
        let (atoms, live_formula, live_properties) = match &liveness {
            Some(liveness) => self.write_liveness(liveness)?,
            None => (Vec::new(), Vec::new(), Vec::new()),
        };
        let definition = config
            .specification
            .as_deref()
            .and_then(|name| crate::spec::get_definition(name, self.environment))
            .cloned();
        let is_next_constant_cast = specification.has_action_constant_cast;
        let specification =
            definition.and_then(|definition| self.write_range(definition.location.range.as_ref()));
        let mut startup = self.write_startup(config, is_warning_enabled)?;
        startup.is_next_constant_cast = is_next_constant_cast;
        Ok(Model {
            init,
            next,
            scope,
            actions: Vec::new(),
            is_labelled: false,
            invariants,
            property_invariants,
            property_invariant_names,
            property_invariant_scopes,
            constraints,
            action_constraints,
            possible,
            action_properties,
            initial_predicates,
            initial_predicate_scopes,
            initial_predicate_names,
            view,
            alias,
            postconditions,
            check_deadlock: config.check_deadlock,
            is_warning_enabled,
            is_recording_graph: liveness.is_some(),
            version,
            // TLC's default seed.
            random_seed: self.random_seed,
            fingerprint_index: 0,
            root_module_name: None,
            atoms,
            live_formula,
            live_properties,
            specification,
            startup,
            next_substitution: None,
            instance_actions: Vec::new(),
            instance_names: Vec::new(),
            tlc_spec: None,
            evaluated_definitions: Vec::new(),
        })
    }

    /// `getIrStartup`: what TLC evaluates when it starts. The substitutes it checks, the constant
    /// definitions with effects (one without computes the same wherever it is first used), and
    /// the assumptions that aren't axioms. SYMMETRY is `NotYet` before this.
    fn write_startup(
        &mut self,
        config: &crate::config::ModelConfig,
        is_warning_enabled: bool,
    ) -> Result<Startup> {
        let environment = self.environment;
        // `getLevelBound` takes a name spelled as a variable of the spec for one (`getVarLoc`),
        // a bound name, a LET definition's or a parameter's too, so that TLC computes no
        // definition that names one as it starts and takes no predicate that does for a
        // constant (`processConstantDefns`, `processConfigInvariants`). The front end's levels
        // don't follow that: it declines where TLC would show it, at a definition with effects
        // or warnings, and at a predicate the configuration names.
        let is_spelled_as_variable = |definition: &Rc<Definition>| {
            !environment.variables.is_empty()
                && crate::startup::get_definition_level_bound(environment, definition) > 0
        };
        // An invariant, a property or a constraint TLC doesn't compute reads as one it computed
        // where that computation fails, which TLC swallows and keeps the definition it checks in
        // each state either way (`processConstantDefns`, `processConfigInvariants`,
        // `processConfigProps`, `processModelConstraints`), and, but for an invariant, which TLC
        // warns of as a TRUE constant, where it is TRUE, which holds in each state. The engine
        // computes it as a constant and stops at any other value or at an effect
        // (`StartupPredicate::is_state_level`); a predicate that may warn declines here.
        //
        // TLC evaluates such a definition named elsewhere, as by the next-state relation, at each
        // use, where it may read the name as the variable's (`getVarLoc`), which the engine,
        // binding it, doesn't follow: one the spec names declines.
        let is_read_alike = |kind: &str| matches!(kind, "invariant" | "property" | "constraint");
        let is_named_only_by_configuration = |definition: &Rc<Definition>| {
            // Whether an expression names the definition, through the definitions it names.
            let reaches_definition = Reach::new(environment, None, |expression| {
                if let Some(name) = expression.reference()
                    && !expression.is_locally_resolved()
                {
                    let resolved = environment.substitutions.get(&name).unwrap_or(&name);
                    if environment
                        .definitions
                        .get(resolved)
                        .is_some_and(|callee| Rc::ptr_eq(callee, definition))
                    {
                        return Visit::Found;
                    }
                }
                Visit::Follow(expression.children())
            });
            environment
                .definitions
                .values()
                .filter(|other| !Rc::ptr_eq(other, definition))
                .all(|other| !reaches_definition.expression(&other.body))
                && environment
                    .assumptions
                    .iter()
                    .all(|assumption| !reaches_definition.expression(&assumption.expression))
        };
        let predicates = crate::spec::get_constant_predicates(
            config,
            environment,
            &self.facts,
            &self
                .evaluator
                .map(crate::eval::Evaluator::deferred_conjuncts)
                .unwrap_or_default(),
        );
        if predicates.iter().any(|(_, kind, _, definition)| {
            is_spelled_as_variable(definition)
                && (!is_read_alike(kind)
                    || self.facts.may_warn_definition(definition, environment)
                    || !is_named_only_by_configuration(definition))
        }) {
            return Err(FrontError::NotYet(VARIABLE_SPELLING.to_owned()));
        }
        // Of those the engine computes as it starts, a predicate whose effects, such as an
        // Assert's, may not run: the engine stops where one does, as TLC has it only in a state.
        let is_read_alike_predicate = |definition: &Rc<Definition>| {
            predicates.iter().any(|(_, kind, _, predicate)| {
                Rc::ptr_eq(predicate, definition) && is_read_alike(kind)
            })
        };
        for definition in &environment.startup_definitions {
            if is_startup_definition(definition, environment, &self.facts)
                && (self.facts.is_impure_definition(definition, environment)
                    || self.facts.may_warn_definition(definition, environment))
                && is_spelled_as_variable(definition)
                && (self.facts.may_warn_definition(definition, environment)
                    || !is_read_alike_predicate(definition))
            {
                return Err(FrontError::NotYet(VARIABLE_SPELLING.to_owned()));
            }
        }
        // TLC computes a constant definition or an assumption that reads or sets TLCExt's
        // registers once as it starts (`TLCGetOrDefault` has no minimum level), and warns of a
        // constant invariant that does; the engine computes them where the model reads them.
        let registers = ["TLCGetOrDefault", "TLCGetAndSet"];
        let variables: Vec<&str> = environment
            .variable_index
            .keys()
            .map(|name| &**name)
            .collect();
        // TLCGet's Java method has a minimum level of 1, so TLC never computes a definition that
        // reaches it as it starts, but at each use, as the engine does.
        let mut non_constant = variables.clone();
        if !environment.definitions.contains_key("TLCGet")
            && environment.builtins.get("TLCGet").is_some_and(|builtin| {
                builtin.flags & (IrBuiltin::STATE_LEVEL | IrBuiltin::LEVEL_CONSTANT) as u32
                    == IrBuiltin::STATE_LEVEL as u32
            })
        {
            non_constant.push("TLCGet");
        }
        // A constant definition TLC computes as it starts the engine computes there too where it
        // has effects, in TLC's order, which reads the registers as TLC does then, and else where
        // it is first used, which reads them only through those it computed there.
        let startup_addresses: FastSet<usize> = environment
            .startup_definitions
            .iter()
            .map(|definition| Rc::as_ptr(definition) as usize)
            .collect();
        let is_computed_at_startup = |definition: &Rc<Definition>| {
            is_startup_definition(definition, environment, &self.facts)
                && startup_addresses.contains(&(Rc::as_ptr(definition) as usize))
        };
        // The walks over every definition below each keep what they learn of the definitions
        // they meet, so a long chain of definitions takes each once.
        let reaches_non_constant = Reach::builtins(environment, &non_constant, None);
        let reaches_value_effects = Reach::builtins(environment, &STARTUP_VALUE_EFFECTS, None);
        let reaches_registers = Reach::builtins(environment, &registers, self.evaluator);
        // `is_read` of each definition, from one walk of the spec.
        let referred = std::cell::OnceCell::new();
        let is_read_here = |name: &str| {
            is_read_by_config(config, &|named| named == name)
                || referred
                    .get_or_init(|| get_referred_names(environment, self.evaluator))
                    .contains(name)
        };
        let mut is_register_constant = false;
        for definition in environment.definitions.values() {
            is_register_constant |= matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty())
                && !is_computed_at_startup(definition)
                && !fails_first_at_startup(&definition.body, environment)
                && reaches_registers.definition(definition)
                && (is_read_here(&definition.name)
                    || environment
                        .substitutions
                        .iter()
                        .any(|(name, target)| *target == definition.name && is_read_here(name)))
                && !reaches_non_constant.definition(definition);
        }
        // An assumption TLC checks with its checker made (`AbstractChecker.checkAssumptions`), as
        // the engine checks it, with registers set from it on: TLCSet of a number sets every
        // worker's register (`setAllValues`), which the search reads from then on.
        // TLC tells a predicate the configuration names is constant by where the registers'
        // builtins are written, taken branch or not, and computes and warns of one as it starts;
        // the front end's level counts them as state-level.
        is_register_constant |= [
            &config.invariants,
            &config.properties,
            &config.constraints,
            &config.action_constraints,
            &config.postconditions,
            &config.possible,
        ]
        .into_iter()
        .flatten()
        .chain(
            [
                &config.init,
                &config.next,
                &config.specification,
                &config.view,
                &config.alias,
            ]
            .into_iter()
            .flatten(),
        )
        .filter_map(|name| environment.definitions.get(name.as_str()))
        .any(|definition| {
            let mut seen = FastSet::default();
            let mut pending = vec![definition.body.clone()];
            let mut is_written = false;
            while let Some(expression) = pending.pop() {
                if let Some(name) = expression.reference()
                    && !expression.is_locally_resolved()
                {
                    is_written |= registers.contains(&&*name);
                    let target = environment.substitutions.get(&name).unwrap_or(&name);
                    if let Some(callee) = environment.definitions.get(target)
                        && seen.insert(Rc::as_ptr(callee) as usize)
                    {
                        pending.push(callee.body.clone());
                    }
                }
                pending.extend(expression.children());
            }
            is_written && !reaches_in(&definition.body, environment, &variables, None)
        });
        self.is_tlcext_declined |= is_register_constant;
        // TLCSet's Java method has no minimum level, so `processConstantDefns` computes a
        // constant definition that reaches it as TLC starts, before `TLC.java` makes the
        // checker: TLCSet of a number then throws (there is no checker or simulator to set),
        // as does a key TLC doesn't know, and `processConstantDefns` swallows that and computes
        // the definition again at each use, after showing the effects that ran before it; a key
        // that names a register, "exit" or "pause" sets nothing, and TLC keeps the definition's
        // value. The front end counts TLCSet state-level and computes the definition at each
        // use, which shows TLC's output only where TLCSet fails there first, before any effect.
        let startup_effects = [
            "Print",
            "PrintT",
            "AssertEq",
            "JavaTime",
            "RandomElement",
            "RandomSubset",
            "RandomSetOfSubsets",
            "RandomSubsetSet",
            "TestRandomSetOfSubsets",
            "TLCGetOrDefault",
            "TLCGetAndSet",
            "_Track",
        ];
        let reaches_tlc_set = Reach::builtins(environment, &["TLCSet", "_Track"], self.evaluator);
        let reaches_any_tlc_set = Reach::builtins(environment, &["TLCSet", "_Track"], None);
        let reaches_startup_effects = Reach::builtins(environment, &startup_effects, None);
        // The effects TLC reaches, not those past a part that decides the whole first.
        let reaches_taken_startup_effects =
            Reach::builtins(environment, &startup_effects, self.evaluator);
        let reaches_effect_past_failing_first = reaches_effect_past_failing_first(environment);
        let reaches_register_write = reaches_register_write(environment, self.evaluator);
        let referred_unpruned = std::cell::OnceCell::new();
        let is_read_anywhere = |name: &str| {
            is_read_by_config(config, &|named| named == name)
                || referred_unpruned
                    .get_or_init(|| get_referred_names(environment, None))
                    .contains(name)
        };
        // The constant evaluator computing TLCSet as TLC does as it starts (`computes_tlc_set`).
        let probe = self.evaluator.map(|evaluator| {
            let mut probe = crate::eval::Evaluator::new(
                environment,
                ValueOrder {
                    ranks: evaluator.order.ranks,
                },
                evaluator.version,
                false,
            );
            probe.computes_tlc_set = true;
            probe
        });
        // A root definition without other effects that the constant evaluator, computing it as
        // TLC does as it starts, computes without reaching TLCSet or fails on: TLC swallows the failure, before which nothing was
        // set (TLCSet of a numbered register fails there, as `TLCSet(Len(<<1>>), 2)` or
        // `S(1)` with `S(k) == TLCSet(k, 2)`, and "exit", "pause" and a named register set
        // nothing), and computes the definition at each use, as the engine does.
        let fails_without_effect = |definition: &Rc<Definition>| {
            let Some(evaluator) = self.evaluator else {
                return false;
            };
            // A fresh one, which has computed no argument TLCSet is in before.
            let mut probe = crate::eval::Evaluator::new(
                environment,
                ValueOrder {
                    ranks: evaluator.order.ranks,
                },
                evaluator.version,
                false,
            );
            probe.computes_tlc_set = true;
            !reaches_in(&definition.body, environment, &startup_effects, None)
                && environment
                    .definitions
                    .get(&definition.name)
                    .is_some_and(|root| Rc::ptr_eq(root, definition))
                && {
                    match probe.evaluate(&definition.body, None) {
                        // A value computed without reaching TLCSet, as where a junction's
                        // operand decides it first, which the engine computes alike at each use.
                        Ok(_) => probe.tlc_sets.get() == 0,
                        Err(FrontError::Evaluation(message)) => {
                            !message.starts_with("In evaluation, the identifier")
                        }
                        Err(_) => false,
                    }
                }
        };
        let mut seen = FastSet::default();
        // A TLCSet that sets nothing anywhere leaves the value the same, but TLC still computes
        // the definition once, which shows its other effects once.
        let mut sets_register_at_startup = |definition: &Rc<Definition>| {
            seen.insert(Rc::as_ptr(definition) as usize)
                && matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty())
                && !environment.constants.contains_key(&definition.name)
                && !environment.substitutions.contains_key(&definition.name)
                // A branch TLC doesn't take, of a condition the evaluator computes, as
                // `IF FALSE THEN TLCSet(1, 2) ELSE e`, sets nothing (`get_reached_children`).
                // But a definition nothing reads that has other effects TLC shows as it starts,
                // as `PrintT(0) /\ FALSE /\ TLCSet("-Dbar", 3)`, which the engine, counting
                // TLCSet state-level, computes nowhere: one whose effect TLC reaches, not one
                // after a part that decides the whole first, as in `FALSE /\ PrintT(0)`,
                // `TRUE \/ PrintT(0)` or `\E x \in {} : PrintT(x)`.
                && (reaches_tlc_set.definition(definition)
                    || reaches_any_tlc_set.definition(definition)
                        && reaches_taken_startup_effects.definition(definition)
                        && !is_read(&definition.name, config, environment, None)
                        && !environment.substitutions.values().any(|target| *target == definition.name))
                // An expression that reaches none of these is one that sets nothing, without
                // walking it again (`sets_nothing_at_startup`'s first test).
                && reaches_value_effects.definition(definition)
                && !sets_nothing_at_startup(&definition.body, environment, self.evaluator)
                && !fails_without_effect(definition)
                && !is_key_failing_as_built(&definition.body, environment, self.evaluator)
                && reaches_effect_past_failing_first.definition(definition)
                && !reaches_non_constant.definition(definition)
                && (reaches_startup_effects.definition(definition)
                    || reaches_register_write.definition(definition)
                        && (is_read_anywhere(&definition.name)
                            || environment.substitutions.iter().any(|(name, target)| {
                                *target == definition.name && is_read_anywhere(name)
                            })))
        };
        // Where the front end can't tell whether TLC, computing such a definition as it starts,
        // fails or completes before any effect, the engine tells as it starts
        // (`tla_ir::Startup::register_probes`), but for one that reaches an effect the engine
        // doesn't count there (`UNPROBED_EFFECTS`).
        let mut register_probes = Vec::new();
        for definition in &environment.startup_definitions {
            if !sets_register_at_startup(definition) {
                continue;
            }
            if reaches_in(&definition.body, environment, &UNPROBED_EFFECTS, None)
                || reaches_deferred_tlc_set(
                    &definition.body,
                    environment,
                    false,
                    &mut FastSet::default(),
                    0,
                )
            {
                return Err(FrontError::NotYet(
                    "a constant definition TLC computes as it starts that sets a register".into(),
                ));
            }
            register_probes.push(Rc::clone(definition));
        }
        // TLC tells a definition's level by where TLCSet is written, taken branch or not, so it
        // computes once as it starts a constant definition whose TLCSet is only in a branch it
        // doesn't take (`IF FALSE THEN TLCSet(1, 2) ELSE e`, `FALSE /\ TLCSet(1, 2)`), and one
        // that names it, with their effects, read or not, and keeps the value. The front end
        // counts TLCSet state-level wherever it is written, so the engine computes such a
        // definition at each use, or never: `D2 == D1 /\ PrintT(3)` unread, over `D1 == IF FALSE
        // THEN TLCSet(1, 2) ELSE TRUE`, prints nothing where TLC prints `3`, and read twice prints
        // it twice. A clock read the model doesn't print shows nowhere.
        let taken_effects: Vec<&str> = startup_effects
            .iter()
            .copied()
            .filter(|name| *name != "JavaTime")
            .collect();
        let reaches_written_tlc_set = Reach::builtins(environment, &["TLCSet"], None);
        let reaches_taken_effects = Reach::builtins(environment, &taken_effects, self.evaluator);
        // But where the first assumption reads it once, by name, and no other definition TLC
        // computes as it starts has a taken effect, TLC shows its effects once, as it starts,
        // and the engine once, at the assumption, as nothing comes between (`get_assumed_once`):
        // `D == [y \in {} |-> TLCSet(1, y)]` and `Test == PrintT(D)` print `<<>>` once either way.
        // Not where it reads TLC's registers or a clock, which differ there.
        let assumed_once = get_assumed_once(config, environment);
        let is_assumed_once = |definition: &Rc<Definition>| {
            assumed_once.iter().any(|once| Rc::ptr_eq(once, definition))
                && !reaches_in(&definition.body, environment, &UNPROBED_EFFECTS, None)
                && !environment.startup_definitions.iter().any(|other| {
                    !assumed_once.iter().any(|once| Rc::ptr_eq(once, other))
                        && matches!(&other.kind, DefinitionKind::Operator { params, .. } if params.is_empty())
                        && !reaches_non_constant.definition(other)
                        && (reaches_taken_effects.definition(other)
                            || reaches_tlc_set.definition(other))
                })
        };
        let mut seen = FastSet::default();
        if environment.startup_definitions.iter().any(|definition| {
            seen.insert(Rc::as_ptr(definition) as usize)
                && matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty())
                && !environment.constants.contains_key(&definition.name)
                && !environment.substitutions.contains_key(&definition.name)
                && !is_computed_at_startup(definition)
                && reaches_written_tlc_set.definition(definition)
                && !reaches_tlc_set.definition(definition)
                && !reaches_non_constant.definition(definition)
                && reaches_taken_effects.definition(definition)
                && !is_assumed_once(definition)
        }) {
            return Err(FrontError::NotYet(
                "a constant definition TLC computes as it starts with effects and TLCSet only in a branch it doesn't take"
                    .into(),
            ));
        }
        // `processConstantDefns` computes every constant definition as TLC starts, read or not,
        // so a TLCSet("-D<name>", v) there sets the system property, which TLCGet("-D<name>")
        // then reads, where the engine computes a definition only where it is used.
        // A root definition without other effects that the constant evaluator computes as TLC
        // does as it starts, with TLCSet (`computes_tlc_set`), to a value or a failure, never
        // reached a TLCSet of a system property, which the evaluator leaves uncomputed: TLC evaluates it no further
        // either, as where `S(k) == (k \div 1 = 1) /\ TLCSet("-Dbar", k)` and `D == S(4)`.
        let sets_no_property = |definition: &Rc<Definition>| {
            let Some(probe) = &probe else {
                return false;
            };
            // Not one whose other effects TLC shows as it starts, which the engine may not.
            !reaches_in(&definition.body, environment, &startup_effects, None)
                && environment
                    .definitions
                    .get(&definition.name)
                    .is_some_and(|root| Rc::ptr_eq(root, definition))
                && match probe.evaluate(&definition.body, None) {
                    Ok(_) => true,
                    Err(FrontError::Evaluation(message)) => {
                        !message.starts_with("In evaluation, the identifier")
                    }
                    Err(_) => false,
                }
        };
        let reaches_written_tlc_set_anywhere = Reach::builtins(environment, &["TLCSet"], None);
        let mut seen = FastSet::default();
        let startup_setters: Vec<Expr> = environment
            .startup_definitions
            .iter()
            .chain(&environment.instanced_definitions)
            .filter(|definition| {
                seen.insert(Rc::as_ptr(definition) as usize)
                    && matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty())
                    && !environment.constants.contains_key(&definition.name)
                    && !environment.substitutions.contains_key(&definition.name)
                    && !reaches_non_constant.definition(definition)
                    && !(reaches_written_tlc_set_anywhere.definition(definition)
                        // An expression that reaches none of these sets nothing, without walking
                        // it again (`sets_nothing_at_startup`'s first test).
                        && (!reaches_value_effects.definition(definition)
                            || sets_nothing_at_startup(&definition.body, environment, self.evaluator)
                            || sets_no_property(definition)))
            })
            .map(|definition| definition.body.clone())
            .collect();
        let set_at_startup =
            reached_property_keys(startup_setters, environment, "TLCSet", self.evaluator, true);
        if set_at_startup.as_ref().is_none_or(|keys| !keys.is_empty()) {
            let readers: Vec<Expr> = environment
                .assumptions
                .iter()
                .map(|assumption| assumption.expression.clone())
                .chain(
                    environment
                        .definitions
                        .values()
                        .filter(|definition| {
                            is_read_by_config(config, &|named| named == &*definition.name)
                        })
                        .map(|definition| definition.body.clone()),
                )
                .collect();
            let read = reached_property_keys(readers, environment, "TLCGet", self.evaluator, false);
            let is_shared = match (&set_at_startup, &read) {
                (Some(set), Some(read)) => set.iter().any(|name| read.contains(name)),
                (_, Some(read)) => !read.is_empty(),
                (Some(set), None) => !set.is_empty(),
                (None, None) => true,
            };
            if is_shared {
                return Err(FrontError::NotYet(
                    "a constant definition TLC computes as it starts that sets a system property TLCGet reads"
                        .into(),
                ));
            }
        }
        // TLCExt's AssertError has no minimum level either, so TLC computes a constant definition
        // that reaches it once as it starts, with its effects, where the front end counts it
        // state-level and the engine computes it, with them, at each use.
        let reaches_assert_error = Reach::builtins(environment, &["AssertError"], None);
        let mut seen = FastSet::default();
        let asserts_at_startup = environment.startup_definitions.iter().any(|definition| {
            seen.insert(Rc::as_ptr(definition) as usize)
                && matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty())
                && !environment.constants.contains_key(&definition.name)
                && !environment.substitutions.contains_key(&definition.name)
                && reaches_assert_error.definition(definition)
                && !reaches_non_constant.definition(definition)
                && reaches_startup_effects.definition(definition)
                && !is_assumed_print_once(definition, config, environment, &startup_effects)
        });
        if asserts_at_startup {
            return Err(FrontError::NotYet(
                "a constant definition TLC computes as it starts with AssertError and effects"
                    .into(),
            ));
        }
        // IOUtils's Serialize, which `Json.textSerialize` overrides, writes its file where TLC
        // computes a constant definition that reaches it as it starts (`processConstantDefns`):
        // once, there, whether or not the model uses the definition, where the engine would write
        // it at each use, or never.
        let reaches_serialize = Reach::serialize(environment, self.evaluator);
        let mut seen = FastSet::default();
        if environment
            .startup_definitions
            .iter()
            .chain(&environment.instanced_definitions)
            .any(|definition| {
                seen.insert(Rc::as_ptr(definition) as usize)
                    && matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty())
                    && !environment.constants.contains_key(&definition.name)
                    && !environment.substitutions.contains_key(&definition.name)
                    && self.facts.is_constant_level(definition, environment)
                    && may_write_text(
                        &definition.body,
                        environment,
                        self.evaluator,
                        &reaches_serialize,
                    )
            })
        {
            return Err(FrontError::NotYet(
                "a constant definition TLC computes as it starts with IOUtils's Serialize".into(),
            ));
        }
        // TLC computes the definitions of a module's inner modules in the order of its Hashtable
        // (`Context.getModDefs`), where the front end takes them in the source's order, and the
        // copies an INSTANCE of an inner module, or in a LET, makes in an order the front end
        // doesn't follow (`instanced_definitions`).
        let is_shown_at_startup = |definition: &Rc<Definition>| {
            matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty())
                && self.facts.is_constant_level(definition, environment)
                && self.facts.is_impure_definition(definition, environment)
        };
        if environment.startup_inner_siblings.iter().any(|groups| {
            groups
                .iter()
                .filter(|group| group.iter().any(is_shown_at_startup))
                .count()
                > 1
        }) {
            return Err(FrontError::NotYet(
                "effects at startup in two inner modules of a module".into(),
            ));
        }
        if environment
            .instanced_definitions
            .iter()
            .any(is_shown_at_startup)
        {
            return Err(FrontError::NotYet(
                "an INSTANCE of a module with a definition TLC computes as it starts with effects"
                    .into(),
            ));
        }
        if environment
            .assumptions
            .iter()
            .any(|assumption| passes_effect(&assumption.expression, environment, &["AssertEq"]))
        {
            return Err(FrontError::NotYet(
                "an assumption that passes an operator an argument with AssertEq".into(),
            ));
        }
        let mut substitutes = Vec::new();
        let mut recursive_substitutes = Vec::new();
        for (name, target) in environment.substitutions.iter() {
            let Some(definition) = environment.definitions.get(target) else {
                continue;
            };
            // TLC evaluates a substitute before the constant definitions and again wherever the
            // name it replaces is read, which repeats its effects; the IR evaluates it once, in
            // definition order. TLC keeps the value of a constant TLCEval in the semantic graph
            // (`tlcEvalConst`), which then shows its effects once, in TLC's order where no other
            // constant definition shows any.
            let is_constant = environment
                .root_constants
                .iter()
                .any(|constant| constant.name == *name);
            let is_cached = || {
                matches!(
                    &definition.body.kind,
                    ExpressionKind::Apply { operator, args, .. } if &**operator == "TLCEval" && args.len() == 1
                ) && self.facts.is_constant_level(definition, environment)
                    && !environment.startup_definitions.iter().any(|other| {
                        !Rc::ptr_eq(other, definition)
                            && is_startup_definition(other, environment, &self.facts)
                            && reaches_shown_effect(other, environment, Some(definition))
                    })
            };
            // A definition the configuration replaces reads the OpDefNode of its substitute
            // (`SpecProcessor.processSpec`), so it too prints again at every read of a substitute
            // of constant level, beside the read that computes its value as TLC starts: where
            // TLC may evaluate one, past the branches its constant conditions leave out.
            // An ALIAS nothing else names TLC evaluates only as it prints a trace, where X's reads
            // print again, which the engine doesn't follow: such a trace declines
            // (`alias_decline`).
            let others = crate::config::ModelConfig {
                alias: None,
                ..config.clone()
            };
            let alias = config
                .alias
                .as_deref()
                .filter(|alias| !is_read(alias, &others, environment, None));
            let is_printed = |is_alias_read: bool| {
                !is_constant
                    && self.facts.is_constant_level(definition, environment)
                    && is_read_but(name, config, environment, self.evaluator, &|read| {
                        !is_alias_read && alias.is_some_and(|alias| *read.name == *alias)
                    })
                    && reaches_effect(definition, environment, None, &["Print", "PrintT"], false)
            };
            if ((is_constant && reaches_shown_effect(definition, environment, None))
                || is_printed(false))
                && !is_cached()
            {
                return Err(FrontError::NotYet(format!(
                    "a configuration substitute with effects, which TLC evaluates at every use: \
                     {name} <- {target}"
                )));
            }
            // A definition the configuration replaces makes `processConstantDefns` compute its
            // substitute again where it reaches it, whatever came of computing it before: a
            // draw draws again, where the engine computes it once, and the value of the last
            // computation is the one the substitute keeps. That shows nowhere only where the
            // draws decide whether it fails and not what it gives, and nothing else draws
            // (`is_drawn_alike`).
            if !is_constant
                && self.facts.is_constant_level(definition, environment)
                && environment.is_recomputed_substitute(definition)
                && !is_cached()
                && reaches_effect(
                    definition,
                    environment,
                    None,
                    &crate::environment::DRAWS,
                    false,
                )
                && !self.evaluator.is_some_and(|evaluator| {
                    crate::environment::is_drawn_alike(environment, evaluator, definition)
                })
            {
                return Err(FrontError::NotYet(format!(
                    "a configuration substitute with effects, which TLC computes again where it \
                     reaches the definition it replaces: {name} <- {target}"
                )));
            }
            if is_printed(true) && !is_cached() {
                self.alias_decline.get_or_insert_with(|| {
                    format!(
                        "a trace printed through an ALIAS that reads a configuration substitute \
                         with effects, which TLC evaluates at every use: {name} <- {target}"
                    )
                });
            }
            // TLC computes a substitute again at each read, which the engine computes once: the
            // engine declines the TLCExt builtins it checks where it computes them, as it did
            // before it checked them.
            self.is_tlcext_declined |=
                reaches_effect(definition, environment, None, &NEW_BUILTINS, false);
            let is_checked = is_constant
                && matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty())
                && !self.facts.is_constant_level(definition, environment);
            if is_checked {
                let text = self.get_text(name);
                substitutes.push((text, self.get_definition_index(definition)));
            } else if is_constant
                && matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty())
                && reaches_recursion(definition, environment)
            {
                recursive_substitutes.push(self.get_definition_index(definition));
            }
        }
        // TLCEvalDefinition's Java method has no minimum level, so `processConstantDefns`
        // computes a constant definition that applies it as TLC starts, where it fails, as
        // `tool.getSpecProcessor()` is still null, and TLC computes the definition again wherever
        // it is read. The engine computes it only where it is read, as for a definition of a
        // level above constant, which shows where the definition prints, draws or reaches TLC's
        // registers before.
        let reaches_eval_definition =
            Reach::effects(environment, None, &["TLCEvalDefinition"], false);
        let reaches_shown = Reach::effects(environment, None, &SHOWN_EFFECTS, false);
        for definition in environment.startup_definitions.iter() {
            if matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty())
                && reaches_eval_definition.definition(definition)
                && reaches_shown.definition(definition)
            {
                return Err(FrontError::NotYet(
                    "a constant definition with effects that TLC computes again after TLCEvalDefinition fails as it starts"
                        .to_owned(),
                ));
            }
        }
        // `processConstantDefns` computes a definition whose body `getLevelBound` finds of
        // constant level, a Json operator's Java method having no minimum level (`Json.toJson`),
        // and keeps its value, or swallows its failure and evaluates it again, with its effects,
        // at each use. The front end takes the Json operators as of state level, so the engine
        // computes such a definition only where it is used, each time: where it prints, draws or
        // sets a register, those show other than TLC's, before a conversion that fails as TLC
        // starts or where it is used more than once. A definition that only reads or writes a
        // JSON file the engine evaluates at each use, as it did before, which matches where it
        // is used once (fallback.md, "Known wrong outputs").
        let reaches_json = Reach::effects(
            environment,
            None,
            &["ToJson", "ToJsonArray", "ToJsonObject"],
            false,
        );
        for definition in environment.startup_definitions.iter() {
            if matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty())
                && reaches_json.definition(definition)
                && !environment.constants.contains_key(&definition.name)
                && !environment.substitutions.contains_key(&definition.name)
                && !self.facts.is_constant_level(definition, environment)
                && reaches_shown.definition(definition)
                && crate::startup::get_definition_level_bound(environment, definition) == 0
            {
                return Err(FrontError::NotYet(
                    "a constant definition with effects applying a Json operator, which TLC computes as it starts"
                        .to_owned(),
                ));
            }
        }
        let mut seen = FastSet::default();
        let startup_definitions: Vec<Rc<Definition>> = environment
            .startup_definitions
            .iter()
            .filter(|definition| {
                is_startup_definition(definition, environment, &self.facts)
                    && (self.facts.is_impure_definition(definition, environment)
                        || is_warning_enabled
                            && self.facts.may_warn_definition(definition, environment))
                    && seen.insert(Rc::as_ptr(definition) as usize)
            })
            .cloned()
            .collect();
        // A definition only a TLCExt builtin the engine checks, but AssertEq, makes impure stays
        // where the engine computes it, which declines those builtins, as before it checked them.
        let reaches_earlier_impure =
            Reach::effects(environment, None, &EARLIER_IMPURE_BUILTINS, false);
        let reaches_startup_declined =
            Reach::effects(environment, None, &STARTUP_DECLINED_BUILTINS, false);
        let (startup_definitions, checked): (Vec<_>, Vec<_>) =
            startup_definitions.into_iter().partition(|definition| {
                reaches_earlier_impure.definition(definition)
                    || !reaches_startup_declined.definition(definition)
            });
        self.is_tlcext_declined |= !checked.is_empty();
        // `processConstantDefns` computes every constant definition of no argument, used or not,
        // and one that names a definition that failed there evaluates it again, with its prints
        // and draws; the engine computes only those with effects there, and evaluates such a
        // definition without effects of its own where TLC computes it, where one it names failed.
        let listed: FastSet<usize> = startup_definitions
            .iter()
            .map(|definition| Rc::as_ptr(definition) as usize)
            .collect();
        // Whether a definition names one of them, through the definitions it names.
        let reaches_listed = Reach::new(environment, None, |expression| {
            if let Some(name) = expression.reference()
                && !expression.is_locally_resolved()
            {
                let resolved = environment.substitutions.get(&name).unwrap_or(&name);
                if environment
                    .definitions
                    .get(resolved)
                    .is_some_and(|callee| listed.contains(&(Rc::as_ptr(callee) as usize)))
                {
                    return Visit::Found;
                }
            }
            Visit::Follow(expression.children())
        });
        // A listed definition TLC looks up again for a later module, which holds it from a module
        // it extends or an INSTANCE without parameters, is a dependent of itself: TLC evaluates
        // it again there where it failed (`Startup::dependents`).
        let mut computed_before = 0;
        let mut dependents = Vec::new();
        let mut seen_dependents = FastSet::default();
        let mut computed = FastSet::default();
        let mut repeats = environment.startup_repeats.iter().peekable();
        for (at, other) in environment.startup_definitions.iter().enumerate() {
            while let Some((_, repeated)) = repeats.next_if(|(position, _)| *position <= at) {
                if computed.contains(&(Rc::as_ptr(repeated) as usize)) {
                    dependents.push((computed_before, Rc::clone(repeated)));
                }
            }
            let address = Rc::as_ptr(other) as usize;
            if listed.contains(&address) {
                if computed.insert(address) {
                    computed_before += 1;
                } else {
                    dependents.push((computed_before, Rc::clone(other)));
                }
                continue;
            }
            if is_startup_definition(other, environment, &self.facts)
                && seen_dependents.insert(address)
                && reaches_listed.definition(other)
            {
                dependents.push((computed_before, Rc::clone(other)));
            }
        }
        for (_, repeated) in repeats {
            if computed.contains(&(Rc::as_ptr(repeated) as usize)) {
                dependents.push((computed_before, Rc::clone(repeated)));
            }
        }
        let definitions: Vec<_> = startup_definitions
            .iter()
            .map(|definition| self.get_definition_index(definition))
            .collect();
        // A probe reads no definition the engine computes as it starts with effects that TLC
        // computes after the probed definition: TLC computes that one with its effects inside the
        // probed one, where the engine reads the value it kept. One TLC computes before it, TLC
        // keeps, and the probed definition reads that value, as the engine's does (`D ==
        // RandomElement({0, 2})` before `Test == (D = 1) /\ TLCSet(1, 2)`): where computing it
        // failed, the engine computes it again inside the probe, with its effects, which declines.
        // TLC processes a module's definitions in order, and the modules it extends first.
        let position_of = |definition: &Rc<Definition>| {
            environment
                .startup_definitions
                .iter()
                .position(|other| Rc::ptr_eq(other, definition))
        };
        if register_probes.iter().any(|definition| {
            if listed.contains(&(Rc::as_ptr(definition) as usize)) {
                return true;
            }
            if !reaches_listed.definition(definition) {
                return false;
            }
            let Some(at) = position_of(definition) else {
                return true;
            };
            let later: FastSet<usize> = startup_definitions
                .iter()
                .filter(|listed| position_of(listed).is_none_or(|position| position >= at))
                .map(|listed| Rc::as_ptr(listed) as usize)
                .collect();
            Reach::new(environment, None, |expression| {
                if let Some(name) = expression.reference()
                    && !expression.is_locally_resolved()
                {
                    let resolved = environment.substitutions.get(&name).unwrap_or(&name);
                    if environment
                        .definitions
                        .get(resolved)
                        .is_some_and(|callee| later.contains(&(Rc::as_ptr(callee) as usize)))
                    {
                        return Visit::Found;
                    }
                }
                Visit::Follow(expression.children())
            })
            .definition(definition)
        }) {
            return Err(FrontError::NotYet(
                "a constant definition TLC computes as it starts that sets a register".into(),
            ));
        }
        // The one probe the first assumption reads once by its name (`get_assumed_once`), where
        // nothing else TLC computes as it starts has an effect, checked below.
        let is_probe_read_once = matches!(register_probes.as_slice(), [probe]
            if environment.assumptions.first().is_some_and(|first| !first.is_axiom)
                && get_assumed_once(config, environment)
                    .first()
                    .is_some_and(|read| Rc::ptr_eq(read, probe)));
        let register_probes = register_probes
            .iter()
            .map(|definition| self.get_definition_index(definition))
            .collect();
        let dependents: Vec<_> = dependents
            .iter()
            .map(|(position, definition)| (*position, self.get_definition_index(definition)))
            .collect();
        let mut predicates = Vec::new();
        for (form, kind, name, definition) in crate::spec::get_constant_predicates(
            config,
            environment,
            &self.facts,
            &self
                .evaluator
                .map(crate::eval::Evaluator::deferred_conjuncts)
                .unwrap_or_default(),
        ) {
            let is_state_level = !environment.variables.is_empty()
                && crate::startup::get_definition_level_bound(environment, &definition) > 0;
            predicates.push(tla_ir::StartupPredicate {
                form,
                kind: self.get_text(kind),
                name: self.get_text(&name),
                definition: self.get_definition_index(&definition),
                is_state_level,
            });
        }
        let symmetry = match &config.symmetry {
            None => None,
            Some(name) => Some(self.write_symmetry(config, name)?),
        };
        let mut assumptions = Vec::new();
        for assumption in &environment.assumptions {
            if assumption.is_axiom {
                continue;
            }
            let root = self.write_root(&assumption.expression)?;
            // SANY's `toString` of the assumption, which TLC's messages print: a numeral's text,
            // else where the assumption is written.
            let name = match &assumption.expression.kind {
                ExpressionKind::Number { text, .. } => self.get_text(text),
                _ => self.get_text(&describe_range(&assumption.expression)),
            };
            assumptions.push((root, name));
        }
        let is_probe_assumed_once = is_probe_read_once
            && definitions.is_empty()
            && dependents.is_empty()
            && predicates.is_empty()
            && symmetry.is_none();
        Ok(Startup {
            substitutes,
            recursive_substitutes,
            definitions,
            dependents,
            register_probes,
            is_probe_assumed_once,
            predicates,
            symmetry,
            // `write_model` sets it from the specification.
            is_next_constant_cast: false,
            assumptions,
        })
    }

    /// The SYMMETRY definition and `getPermutedSets`: the sets its body permutes, each by the
    /// name the configuration substitutes for it or the text of its expression, and, for
    /// `Permutations(S)` of a name the configuration doesn't replace with `<-`, S.
    fn write_symmetry(
        &mut self,
        config: &crate::config::ModelConfig,
        name: &str,
    ) -> Result<Symmetry> {
        // A configuration that substitutes for the SYMMETRY definition gives TLC the definition
        // it substitutes, whose body TLC evaluates and takes the arguments of (`unprocessedDefns`
        // holds the overriding `OpDefNode`).
        let name = get_symmetry_name(config, name);
        let Some(definition) = self.environment.definitions.get(name).cloned() else {
            return Err(FrontError::NotYet(
                "a SYMMETRY the spec doesn't define".to_owned(),
            ));
        };
        let DefinitionKind::Operator { params, .. } = &definition.kind else {
            return Err(FrontError::NotYet("a SYMMETRY function".to_owned()));
        };
        if !params.is_empty() {
            return Err(FrontError::NotYet(
                "a SYMMETRY operator with parameters".to_owned(),
            ));
        }
        let index = self.get_definition_index(&definition);
        let config_names: FastMap<&str, &str> = config
            .substitutions
            .iter()
            .filter(|substitution| substitution.module.is_none())
            .map(|substitution| (substitution.target.as_str(), substitution.name.as_str()))
            .collect();
        let is_substituted = |name: &str| {
            config
                .substitutions
                .iter()
                .any(|substitution| substitution.name == name)
        };
        // TLC takes the arguments of the body's node, whatever operator SANY made of it, and
        // fails on a body that is no application, such as a LET (`Tool.getSymmetryPerms`). It
        // evaluates the body first, and fails on a number's or a string's value, which isn't a set,
        // before it looks at the node. A set enumeration's arguments are its elements, and a
        // filter's (`$SubsetOf`) and a set map's (`$SetOfAll`) their one expression, the bounds
        // being apart from the arguments.
        let permuted = match &definition.body.kind {
            ExpressionKind::Apply { args, .. } => args.clone(),
            ExpressionKind::Identifier { .. }
            | ExpressionKind::Number { .. }
            | ExpressionKind::String { .. } => Vec::new(),
            ExpressionKind::SetEnumeration(elements) => elements.clone(),
            ExpressionKind::SetFilter { predicate, .. } => vec![predicate.clone()],
            ExpressionKind::SetMap { expression, .. } => vec![expression.clone()],
            _ => {
                return Err(FrontError::NotYet(
                    "a SYMMETRY definition that isn't an operator applied to its sets".to_owned(),
                ));
            }
        };
        let mut permuted_sets = Vec::new();
        for set in permuted {
            let operand = match &set.kind {
                ExpressionKind::Apply { args, .. }
                    if args.len() == 1 && set.reference().as_deref() == Some("Permutations") =>
                {
                    Some(args[0].clone())
                }
                _ => None,
            };
            // An empty name stands for an image the AST can't give, which the checker declines
            // to warn of.
            // `addToSubTwoSizedSymmetrySetList` takes the image of the argument, without the
            // first 13 characters and the last where it starts with `Permutations`.
            let image = self
                .get_written_image(&set)
                .and_then(|image| match image.strip_prefix("Permutations") {
                    Some(_) if image.len() < 14 => None,
                    Some(_) => Some(image[13..image.len() - 1].to_owned()),
                    None => Some(image),
                })
                .unwrap_or_default();
            let name = config_names
                .get(image.as_str())
                .map_or(image.clone(), |name| (*name).to_owned());
            let name = self.get_text(&name);
            let operand = match operand {
                Some(operand)
                    if matches!(operand.kind, ExpressionKind::Identifier { .. })
                        && !is_substituted(&operand.reference().unwrap_or_default()) =>
                {
                    Some(self.write_root(&operand)?)
                }
                _ => None,
            };
            permuted_sets.push(PermutedSet { name, operand });
        }
        Ok(Symmetry {
            definition: index,
            permuted_sets,
        })
    }

    /// Whether a definition without parameters, which TLC may compute as it starts
    /// (`processConstantDefns`), can print, assert, read the clock or choose at random.
    fn has_impure_constant_definition(&self) -> bool {
        self.environment.definitions.values().any(|definition| {
            matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty())
                && self
                    .facts
                    .is_impure_definition(definition, self.environment)
        })
    }

    /// Whether TLC computes the symmetry without an error or a warning of its own
    /// (`getSymmetryPerms`), as it does the permutations of a set of model values, or the union
    /// of two such, which it warns about unless the sets are disjoint and hold two or more each.
    fn is_symmetry_quiet(
        &self,
        config: &crate::config::ModelConfig,
        name: &str,
        is_warning_enabled: bool,
    ) -> bool {
        let Some(evaluator) = self.evaluator else {
            return false;
        };
        let name = get_symmetry_name(config, name);
        let Some(definition) = self.environment.definitions.get(name) else {
            return false;
        };
        if !matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty())
        {
            return false;
        }
        // TLC computes the symmetry with the operators the names resolve to: one the model
        // substitutes or the spec defines may compute anything.
        let is_builtin = |name: &str| {
            !self.environment.substitutions.contains_key(name)
                && !self.environment.definitions.contains_key(name)
        };
        if !is_builtin("Permutations") || !is_builtin("\\cup") {
            return false;
        }
        let get_permuted = |expression: &Expr| match &expression.kind {
            ExpressionKind::Apply { args, .. }
                if args.len() == 1 && expression.reference().as_deref() == Some("Permutations") =>
            {
                Some(args[0].clone())
            }
            _ => None,
        };
        let permuted = match (&definition.body.kind, get_permuted(&definition.body)) {
            (_, Some(set)) => vec![set],
            (ExpressionKind::Apply { args, .. }, None)
                if definition.body.reference().as_deref() == Some("\\cup") =>
            {
                match args.iter().map(get_permuted).collect::<Option<Vec<_>>>() {
                    Some(sets) => sets,
                    None => return false,
                }
            }
            _ => return false,
        };
        let mut elements = Vec::new();
        for set in &permuted {
            match evaluator.evaluate(set, None) {
                Ok(ConfigValue::Set(set))
                    if set
                        .iter()
                        .all(|element| matches!(element, ConfigValue::ModelValue(_)))
                        && (!is_warning_enabled || set.len() > 1) =>
                {
                    elements.extend(set);
                }
                _ => return false,
            }
        }
        !is_warning_enabled
            || elements
                .iter()
                .enumerate()
                .all(|(index, element)| !elements[..index].contains(element))
    }

    /// The liveness checker's atoms, formula and properties, as `lowerToIr` writes them: each atom
    /// in the checker's order, then the terms, which take a position past them for an atom the
    /// checker asks nothing of. TLC's actions aren't split here, so ENABLED's are unknown until
    /// `tla_trace::add_actions` splits them.
    fn write_liveness(
        &mut self,
        liveness: &Liveness,
    ) -> Result<(Vec<IrAtom>, Vec<LiveTerm>, Vec<LiveProperty>)> {
        let mut positions: HashMap<*const Live, Index> = liveness
            .atoms
            .iter()
            .enumerate()
            .map(|(position, atom)| (Rc::as_ptr(atom), position as Index))
            .collect();
        let mut atoms = Vec::with_capacity(liveness.atoms.len());
        for atom in &liveness.atoms {
            let (expression, kind, scope) = match &**atom {
                Live::State { expression, scope } => {
                    (self.write_root(expression)?, AtomKind::State, scope)
                }
                Live::Action {
                    expression,
                    unchanged,
                    scope,
                    enabled,
                } => {
                    let expression = self.write_root(expression)?;
                    let unchanged = match unchanged {
                        Some(unchanged) => Some(self.write_root(unchanged)?),
                        None => None,
                    };
                    let enabled = enabled
                        .as_ref()
                        .and_then(|enabled| positions.get(&Rc::as_ptr(enabled)).copied());
                    (expression, AtomKind::Action { unchanged, enabled }, scope)
                }
                Live::Enabled { step, scope } => (
                    self.write_root(step)?,
                    AtomKind::Enabled {
                        actions: EnabledActions::Unknown,
                    },
                    scope,
                ),
                _ => return Err(FrontError::NotYet("a liveness atom that isn't one".into())),
            };
            let scope = self.get_scope_index(scope.as_ref());
            atoms.push(IrAtom {
                kind,
                expression,
                scope,
            });
        }
        let live_formula = write_live(&liveness.formula, &mut positions);
        let mut live_properties = Vec::with_capacity(liveness.properties.len());
        for (name, formula) in &liveness.properties {
            let name = self.get_text(name);
            live_properties.push(LiveProperty {
                name,
                formula: write_live(formula, &mut positions),
            });
        }
        Ok((atoms, live_formula, live_properties))
    }

    /// `getScopeIndex`: a scope's place in the scopes, which come after the model in the order
    /// they are first met.
    pub fn get_scope_index(&mut self, scope: Option<&Rc<crate::spec::Scope>>) -> Option<Index> {
        let scope = scope?;
        let address = Rc::as_ptr(scope) as usize;
        if let Some(index) = self.scope_ids.get(&address) {
            return Some(*index);
        }
        let index = self.scope_queue.len() as Index;
        self.scope_ids.insert(address, index);
        self.scope_queue.push(scope.clone());
        Some(index)
    }

    /// `writeScope`.
    fn write_scope(&mut self, scope: &Rc<crate::spec::Scope>) -> Result<IrScope> {
        use crate::spec::Binding;
        let parent = self.get_scope_index(scope.parent.as_ref());
        let name = self.get_text(&scope.name);
        let binding = match &scope.binding {
            Binding::Value(value) | Binding::Literal { value, .. } => {
                let value = self.normalize(value)?;
                ScopeBinding::Value(Some(self.encode_value(&value)))
            }
            Binding::Thunk {
                expression,
                scope: of,
            } => {
                let expression = self.write_root(expression)?;
                let of = of.resolve(scope);
                ScopeBinding::Thunk {
                    expression,
                    scope: self.get_scope_index(of.as_ref()),
                }
            }
            Binding::Closure {
                name,
                params,
                body,
                scope: of,
                ..
            } => {
                let name = self.get_text(name);
                let params = params
                    .iter()
                    .map(|param| Param {
                        name: self.get_text(&param.name),
                        arity: param.arity as i32,
                    })
                    .collect();
                let body = self.write_root(body)?;
                let of = of.resolve(scope);
                ScopeBinding::Closure {
                    name,
                    params,
                    body,
                    scope: self.get_scope_index(of.as_ref()),
                }
            }
        };
        Ok(IrScope {
            parent,
            name,
            binding,
        })
    }

    pub fn finish(self, model: Model) -> Result<Ir> {
        self.finish_indexing(model).map(|(ir, _)| ir)
    }

    /// The IR, and the indexes of the definitions it holds that TLC computes as it starts
    /// (`processConstantDefns`), in TLC's order.
    pub fn finish_indexing(mut self, mut model: Model) -> Result<(Ir, Vec<Index>)> {
        let mut definitions = Vec::new();
        let (mut next, mut next_scope) = (0, 0);
        loop {
            if next_scope < self.scope_queue.len() {
                let scope = self.scope_queue[next_scope].clone();
                next_scope += 1;
                let written = self.write_scope(&scope)?;
                self.scopes.push(written);
            } else if next < self.definition_queue.len() {
                let definition = self.definition_queue[next].clone();
                next += 1;
                let id = self.write_definition(&definition)?;
                self.top.push(id);
                definitions.push(id);
            } else {
                break;
            }
        }
        // Where the specification reaches the next-state relation through an INSTANCE, and what TLC
        // names the actions of the definitions INSTANCEs copy, of the definitions the IR holds, by
        // index.
        if let Some(index) = self.builtin_ids.get("TLCGet")
            && are_run_unknowns_unread(self.environment)
        {
            self.builtins[*index as usize].flags |= IrBuiltin::RUN_UNKNOWNS_UNREAD;
        }
        if self.is_tlcext_declined {
            for name in NEW_BUILTINS {
                if let Some(index) = self.builtin_ids.get(name) {
                    self.builtins[*index as usize].flags |= IrBuiltin::DECLINED;
                }
            }
        }
        model.evaluated_definitions = std::mem::take(&mut self.evaluated_definitions);
        let next_substitution = self.next_substitution.take();
        model.next_substitution = self.write_range(
            next_substitution
                .as_ref()
                .and_then(|location| location.range.as_ref()),
        );
        let environment = self.environment;
        let indexed = |keys: &mut dyn Iterator<Item = &Name>, ids: &FastMap<usize, Index>| {
            let mut indexed: Vec<(Index, Name)> = keys
                .filter_map(|key| {
                    let definition = environment.definitions.get(key)?;
                    let index = ids.get(&(Rc::as_ptr(definition) as usize))?;
                    Some((*index, key.clone()))
                })
                .collect();
            // As a JavaScript Map of them, the last key of a definition named by several.
            indexed.sort_by_key(|(index, _)| *index);
            indexed.reverse();
            indexed.dedup_by_key(|(index, _)| *index);
            indexed.reverse();
            indexed
        };
        for (index, key) in indexed(
            &mut environment.instance_actions.keys(),
            &self.definition_ids,
        ) {
            let Some(action) = environment.instance_actions.get(&key) else {
                continue;
            };
            let name = self.get_text(&action.name);
            let location = self.write_range(action.location.range.as_ref());
            model.instance_actions.push(tla_ir::InstanceAction {
                definition: index,
                name,
                location,
            });
        }
        for (index, key) in indexed(&mut environment.instance_names.keys(), &self.definition_ids) {
            if let Some(name) = environment.instance_names.get(&key) {
                let name = self.get_text(name);
                model.instance_names.push((index, name));
            }
        }
        let value_strings = std::mem::take(&mut self.value_strings)
            .iter()
            .map(|text| self.get_text(text))
            .collect();
        let variables = self
            .environment
            .variables
            .iter()
            .map(|variable| self.get_text(variable))
            .collect();
        let texts = self
            .ranked
            .texts
            .iter()
            .chain(&self.extra_texts)
            .map(|text| Box::from(&**text))
            .collect();
        let mut seen = FastSet::default();
        let startup: Vec<Index> = environment
            .startup_definitions
            .iter()
            .filter(|definition| {
                is_startup_definition(definition, environment, &self.facts)
                    && seen.insert(Rc::as_ptr(definition) as usize)
            })
            .filter_map(|definition| {
                self.definition_ids
                    .get(&(Rc::as_ptr(definition) as usize))
                    .copied()
            })
            .collect();
        // TLC binds a substitute to a cached `LazyValue` in each evaluation of a copy's
        // definition (`Tool.evalImplSubstInKind`), so a substitute that prints or sets a register
        // has that effect once there, where the engine has it at each read: written in the
        // substitute, or through an operator with arguments or a definition TLC doesn't compute
        // as it starts, which it evaluates at each application. One only through a definition
        // TLC computes as it starts is left to how the engine evaluates that definition, as TLC
        // keeps its value, or evaluates it again where that failed (`constant_once`).
        let effecting: FastSet<Index> = EFFECTS_OTHER_THAN_DRAWS
            .iter()
            .filter_map(|name| self.builtin_ids.get(*name).copied())
            .collect();
        if !effecting.is_empty()
            && reads_drawing_substitute_twice(
                &self.arena,
                &definitions,
                &effecting,
                &startup
                    .iter()
                    .filter_map(|&index| definitions.get(index as usize).copied())
                    .collect(),
                &FastSet::default(),
                &mut FastSet::default(),
            )
        {
            return Err(FrontError::NotYet(
                "an INSTANCE substitute that prints or sets a register, read more than once in one evaluation of a definition"
                    .into(),
            ));
        }
        let drawing: FastSet<Index> = crate::environment::DRAWS
            .iter()
            .filter_map(|name| self.builtin_ids.get(*name).copied())
            .collect();
        if !drawing.is_empty() {
            let kept: FastSet<NodeId> = startup
                .iter()
                .filter_map(|&index| definitions.get(index as usize).copied())
                .collect();
            let reading: FastSet<Index> = ["TLCGet", "JavaTime"]
                .iter()
                .filter_map(|name| self.builtin_ids.get(*name).copied())
                .collect();
            let mut recomputed = FastSet::default();
            if reads_drawing_substitute_twice(
                &self.arena,
                &definitions,
                &drawing,
                &kept,
                &reading,
                &mut recomputed,
            ) {
                return Err(FrontError::NotYet(
                    "an INSTANCE substitute that draws, read more than once in one evaluation of a definition"
                        .into(),
                ));
            }
            for target in recomputed {
                if let NodeKind::Definition(definition) = &mut self.arena[target as usize].kind {
                    definition.flags |= IrDefinition::NAMED_AT_STARTUP;
                }
            }
        }
        let ir = Ir {
            ranked_count: self.ranked.texts.len() as u32,
            texts,
            wide_texts: self
                .ranked
                .texts
                .iter()
                .enumerate()
                .filter_map(|(id, text)| {
                    let units = self.ranked.wide.get(text)?;
                    Some((id as TextId, units.clone()))
                })
                .collect(),
            variables,
            tlc_order: self.tlc_order,
            builtins: self.builtins,
            constants: self.constants,
            scopes: self.scopes,
            values: Values {
                strings: value_strings,
                list: self.values,
            },
            model,
            definitions,
            nodes: Nodes {
                arena: self.arena,
                top: self.top,
                junctions: self.junctions,
                numerals: self.numerals,
            },
        };
        Ok((ir, startup))
    }
}

/// The builtins whose evaluation has an effect a second evaluation repeats, other than a draw:
/// they print, set a register or record a value.
const EFFECTS_OTHER_THAN_DRAWS: [&str; 6] = [
    "Print",
    "PrintT",
    "TLCSet",
    "TLCGetAndSet",
    "AssertEq",
    "_Track",
];

/// A formula's terms in prefix order, each atom by its position, a new one past the others.
fn write_live(formula: &Rc<Live>, positions: &mut HashMap<*const Live, Index>) -> Vec<LiveTerm> {
    fn write(
        live: &Rc<Live>,
        positions: &mut HashMap<*const Live, Index>,
        terms: &mut Vec<LiveTerm>,
    ) {
        let mut position = |atom: &Rc<Live>| {
            let next = positions.len() as Index;
            *positions.entry(Rc::as_ptr(atom)).or_insert(next)
        };
        match &**live {
            Live::Boolean(value) => terms.push(LiveTerm::Boolean(*value)),
            Live::State { .. } => terms.push(LiveTerm::State(position(live))),
            Live::Enabled { .. } => terms.push(LiveTerm::Enabled(position(live))),
            Live::Action { enabled, .. } => {
                let atom = position(live);
                let enabled = enabled.as_ref().map(&mut position);
                terms.push(LiveTerm::Action { atom, enabled });
            }
            Live::Not(body) | Live::Always(body) | Live::Eventually(body) => {
                terms.push(match &**live {
                    Live::Not(_) => LiveTerm::Not,
                    Live::Always(_) => LiveTerm::Always,
                    _ => LiveTerm::Eventually,
                });
                write(body, positions, terms);
            }
            Live::Junction { is_and, operands } => {
                let count = operands.len() as u32;
                terms.push(if *is_and {
                    LiveTerm::And(count)
                } else {
                    LiveTerm::Or(count)
                });
                for operand in operands {
                    write(operand, positions, terms);
                }
            }
        }
    }
    let mut terms = Vec::new();
    write(formula, positions, &mut terms);
    terms
}

#[cfg(test)]
mod effect_precheck_tests {
    use super::*;
    use crate::TlcVersion;
    use crate::config::parse_config;
    use crate::environment::{EnvironmentOptions, create_environment};

    #[test]
    fn agrees_with_original_effect_walk() {
        let bodies = [
            "Use(1)",
            "Use(Print(1, 2))",
            "Use(Wrapper(1))",
            "Use(Local(1))",
        ];
        for body in bodies {
            let source = format!(
                "---- MODULE M ----\nEXTENDS TLC\nUse(x) == x\nWrapper(x) == Print(x, x)\nLocal(y) == y\nRoot == {body}\n===="
            );
            let config = parse_config("", TlcVersion::Master).unwrap();
            let environment = create_environment(&EnvironmentOptions {
                linked_extendees: &[],
                origin: None,
                source: &source,
                load_module: &|_| None,
                config: &config,
                is_unconfigured: true,
                version: TlcVersion::Master,
                is_level_checked: false,
                load_class: None,
            })
            .unwrap();
            let expression = &environment.definitions.get("Root").unwrap().body;
            assert_eq!(
                passes_effect(expression, &environment, &["Print"]),
                old_passes_effect(expression, &environment, &["Print"]),
                "{body}"
            );
        }
    }
}

#[cfg(test)]
mod configuration_table_phase_producer_tests {
    use super::*;
    use crate::TlcVersion;
    use crate::config::parse_config;
    use crate::environment::{EnvironmentOptions, link_environment};
    use crate::model::{
        ClassOrigin, JavaProfile, ModelOptions, ModelOrigin, ModelSources, ParentRuntime,
        lower_front_ranking_with_origin,
    };
    #[test]
    fn existing_flags_do_not_gain_table_phase_authority() {
        for flags in [0, 1, 2, 4, 64, 256, 4096, 8192, 1 << 29] {
            let config = parse_config("CONSTANT G(1) = TRUE", TlcVersion::Master).unwrap();
            let origin = ModelOrigin::new(JavaProfile::Default, &|_| ClassOrigin::Absent);
            let mut environment = link_environment(&EnvironmentOptions {
                linked_extendees: &[],
                origin: Some(&origin),
                source: "---- MODULE M ----\nG(x) == x\n====\n",
                load_module: &|_| None,
                config: &config,
                is_unconfigured: false,
                version: TlcVersion::Master,
                is_level_checked: false,
                load_class: Some(&|_| None),
            })
            .unwrap();
            environment
                .operator_objects
                .admit(
                    &ValueOrder {
                        ranks: &FastMap::default(),
                    },
                    true,
                )
                .unwrap();
            environment.builtins.get_mut("G").unwrap().flags = flags;
            let wide = FastMap::default();
            let mut lower = Lowering::new(
                &environment,
                RankedTexts {
                    texts: &[],
                    ranks: FastMap::default(),
                    wide: &wide,
                },
            );
            let index = lower.get_builtin_index(&Rc::from("G")).unwrap();
            assert_eq!(
                lower.builtins[index as usize].flags & IrBuiltin::TABLE_PHASE_KNOWN != 0,
                flags == 0,
                "{flags}"
            );
        }
    }
    #[test]
    fn only_explicit_master_parent_closed_profile_emits_table_phase_marker() {
        let source = "---- MODULE M ----\nG(x) == x\nASSUME G(1)\n====\n";
        let reads = crate::source_reads::ModuleSourceReads::default();
        let modules = |name: &str| {
            reads.record(name, Ok(None));
            None
        };
        let report = crate::report::get_sany_text_of(
            "M",
            source,
            &crate::report::ReportOptions {
                version: TlcVersion::Master,
                file_name: None,
                load_module: &modules,
                describe_file: &|name, _| Ok(name.to_owned()),
                root_extendees: &[],
                is_xml_export: false,
                lint_codes: Default::default(),
            },
        )
        .unwrap();
        assert!(!report.is_failed);
        let classes = |_: &str| None;
        let sources = ModelSources {
            source,
            load_module: &modules,
            load_class: &classes,
        };
        for (version, parent, profile, closed, expected) in [
            (
                TlcVersion::Master,
                ParentRuntime::ModeledTlcMasterJdk21,
                JavaProfile::Default,
                true,
                true,
            ),
            (
                TlcVersion::Master,
                ParentRuntime::Unknown,
                JavaProfile::Default,
                true,
                false,
            ),
            (
                TlcVersion::Master,
                ParentRuntime::ModeledTlcMasterJdk21,
                JavaProfile::Opaque,
                true,
                false,
            ),
            (
                TlcVersion::Master,
                ParentRuntime::ModeledTlcMasterJdk21,
                JavaProfile::Default,
                false,
                false,
            ),
            (
                TlcVersion::V1_7_4,
                ParentRuntime::ModeledTlcMasterJdk21,
                JavaProfile::Default,
                true,
                false,
            ),
        ] {
            let presence = |_: &str| {
                if closed {
                    ClassOrigin::Absent
                } else {
                    ClassOrigin::Unknown
                }
            };
            let mut origin = ModelOrigin::new(profile, &presence);
            origin.parent_runtime = parent;
            origin.module_source_reads = Some(&reads);
            let options = ModelOptions {
                libraries: &[],
                version: Some(version),
                is_warning_enabled: false,
                is_spec_described: false,
                random_seed: 0,
                root_extendees: &[],
            };
            match lower_front_ranking_with_origin(
                &sources,
                "CONSTANT G(1) = TRUE",
                &options,
                &|_, _, _| vec![],
                Some(&origin),
            ) {
                Ok(lowered) => {
                    let ir = tla_ir::decode(&lowered.ir).unwrap();
                    let marked = ir
                        .builtins
                        .iter()
                        .any(|b| b.flags & IrBuiltin::TABLE_PHASE_KNOWN != 0);
                    assert_eq!(marked, expected, "{version:?} {parent:?} {profile:?}");
                }
                Err(error) => assert!(!expected, "{error:?}"),
            }
        }
    }
}

/// What a walk of `reads_drawing_substitute_twice` reads: the definitions it takes as given,
/// which it doesn't follow, and what it found of each node before.
struct CallReach<'a> {
    arena: &'a [Node],
    definitions: &'a [NodeId],
    builtins: &'a FastSet<Index>,
    given: FastSet<NodeId>,
    known: FastMap<NodeId, bool>,
    // The nodes the walk is inside, with their depth, and those it finished as `false` only
    // because they reach one of those, whose answer isn't known until it is finished, with
    // the least depth of an open node they rest on.
    open: FastMap<NodeId, usize>,
    pending: Vec<NodeId>,
    waiting: FastMap<NodeId, usize>,
}
impl<'a> CallReach<'a> {
    fn new(
        arena: &'a [Node],
        definitions: &'a [NodeId],
        builtins: &'a FastSet<Index>,
        given: FastSet<NodeId>,
    ) -> Self {
        CallReach {
            arena,
            definitions,
            builtins,
            given,
            known: FastMap::default(),
            open: FastMap::default(),
            pending: Vec::new(),
            waiting: FastMap::default(),
        }
    }

    // Whether evaluating a node may call one of `builtins`, through the definitions and
    // substitutes it names but those given.
    fn calls(&mut self, node: NodeId) -> bool {
        self.visit(node).0
    }
    // `calls`, with the least depth of an open node the answer rests on (`usize::MAX` for
    // none). A node on a cycle reads `false` for the open node it comes back to; that
    // `false` is final only once every node it rests on is finished `false`, so a node is
    // remembered as `false` only then, with the others of its cycle, and forgotten where
    // a node it rests on turns out `true`.
    fn visit(&mut self, node: NodeId) -> (bool, usize) {
        if let Some(&known) = self.known.get(&node) {
            return (known, usize::MAX);
        }
        if let Some(&depth) = self.open.get(&node).or_else(|| self.waiting.get(&node)) {
            return (false, depth);
        }
        let depth = self.open.len();
        self.open.insert(node, depth);
        let mark = self.pending.len();
        let mut low = usize::MAX;
        let mut follow = |reach: &mut Self, child: NodeId| {
            let (calls, rests_on) = reach.visit(child);
            low = low.min(rests_on);
            calls
        };
        let kind = &self.arena[node as usize].kind;
        let named = match kind {
            NodeKind::Identifier(name)
            | NodeKind::OperatorReference(name)
            | NodeKind::Apply { name, .. }
                if !name.is_local =>
            {
                match name.resolution {
                    Resolution::Builtin(index) => self.builtins.contains(&index),
                    Resolution::Definition(index) => self
                        .definitions
                        .get(index as usize)
                        .is_some_and(|&definition| {
                            !self.given.contains(&definition) && follow(self, definition)
                        }),
                    _ => false,
                }
            }
            NodeKind::Reference(target) => follow(self, *target),
            NodeKind::Definition(definition) => follow(self, definition.body),
            _ => false,
        };
        let filtered = match kind {
            NodeKind::SetFilter { bound, .. } => Some(bound.set),
            _ => None,
        };
        let result = named
            || kind
                .children()
                .into_iter()
                .chain(filtered)
                .any(|child| follow(self, child));
        self.open.remove(&node);
        if result {
            // Final: those finished below that rest on an open node may now be `true`, and
            // are walked again where they are read.
            for unknown in self.pending.drain(mark..) {
                self.waiting.remove(&unknown);
            }
            self.known.insert(node, true);
            (true, usize::MAX)
        } else if low >= depth {
            // Every node this rests on is finished `false`, this one last.
            for finished in self.pending.drain(mark..) {
                self.waiting.remove(&finished);
                self.known.insert(finished, false);
            }
            self.known.insert(node, false);
            (false, usize::MAX)
        } else {
            // Those finished below rest on this one or on what it rests on, so they now wait
            // on the open node `low` names, as it does.
            self.pending.push(node);
            for &waiting in &self.pending[mark..] {
                self.waiting.insert(waiting, low);
            }
            (false, low)
        }
    }
    // The given definitions a node names, as written or through the definitions it names.
    fn given_named(&self, node: NodeId, seen: &mut FastSet<NodeId>, found: &mut FastSet<NodeId>) {
        if !seen.insert(node) {
            return;
        }
        let kind = &self.arena[node as usize].kind;
        match kind {
            NodeKind::Identifier(name)
            | NodeKind::OperatorReference(name)
            | NodeKind::Apply { name, .. }
                if !name.is_local =>
            {
                if let Resolution::Definition(index) = name.resolution
                    && let Some(&definition) = self.definitions.get(index as usize)
                {
                    if self.given.contains(&definition) {
                        found.insert(definition);
                    }
                    self.given_named(definition, seen, found);
                }
            }
            NodeKind::Reference(target) => self.given_named(*target, seen, found),
            NodeKind::Definition(definition) => self.given_named(definition.body, seen, found),
            _ => {}
        }
        let filtered = match kind {
            NodeKind::SetFilter { bound, .. } => Some(bound.set),
            _ => None,
        };
        for child in kind.children().into_iter().chain(filtered) {
            self.given_named(child, seen, found);
        }
    }
}

/// Whether a definition's body reads an INSTANCE's substitute that may draw (a node the IR
/// writes once and refers to with a range from each use) more than once in one evaluation, or
/// under a binder, which may evaluate it more than once. TLC binds the substitute to a cachable
/// `LazyValue` at each evaluation of the copy's `SubstInNode` (`Tool.evalImplSubstInKind`,
/// `getVal(sub.getExpr(), c, true, ...)`), which draws at its first read only and keeps that
/// value for the others, where the engine and the trace evaluator evaluate the substitute at
/// each use, drawing again.
///
/// A constant definition TLC computes as it starts (`kept`) gives the value
/// `processConstantDefns` kept wherever it is read, as the engine gives the value it computed
/// there, so a substitute that draws only through such definitions draws alike however often it
/// is read; only where that computation failed does TLC evaluate the definition again, at the
/// substitute's first read. Those a substitute read more than once reaches go to `recomputed`,
/// which the engine declines where their computation as TLC starts fails after a print or a draw
/// (`Definition::NAMED_AT_STARTUP`). One that reads TLC's registers or the clock (`reading`),
/// which may fail as TLC starts without an effect and draw where it is read later, isn't taken so.
fn reads_drawing_substitute_twice(
    arena: &[Node],
    definitions: &[NodeId],
    drawing: &FastSet<Index>,
    kept: &FastSet<NodeId>,
    reading: &FastSet<Index>,
    recomputed: &mut FastSet<NodeId>,
) -> bool {
    // The walk of the definitions' bodies: which draws it follows, those it follows through kept
    // definitions too, and how many reads of each substitute it counted.
    struct Count<'a> {
        arena: &'a [Node],
        definitions: &'a [NodeId],
        live: CallReach<'a>,
        all: CallReach<'a>,
        recomputed: &'a mut FastSet<NodeId>,
        budget: u32,
    }
    impl Count<'_> {
        // A read of a substitute, `target` its expression or the definition it names: a
        // draw this side of the kept definitions read twice declines; one only through them
        // read twice puts those in `recomputed`.
        fn read(
            &mut self,
            target: NodeId,
            is_kept: bool,
            repeated: bool,
            reads: &mut FastMap<NodeId, u32>,
        ) -> bool {
            let read = reads.entry(target).or_default();
            *read += if repeated { 2 } else { 1 };
            if *read < 2 {
                return false;
            }
            if !is_kept && self.live.calls(target) {
                return true;
            }
            let mut found = FastSet::default();
            if is_kept {
                found.insert(target);
            }
            self.live
                .given_named(target, &mut FastSet::default(), &mut found);
            self.recomputed.extend(found);
            false
        }
        // Counts the reads of each drawing substitute in a node, each read under a binder twice.
        fn count(
            &mut self,
            node: NodeId,
            repeated: bool,
            in_copy: bool,
            reads: &mut FastMap<NodeId, u32>,
        ) -> bool {
            let Some(left) = self.budget.checked_sub(1) else {
                return true;
            };
            self.budget = left;
            let arena = self.arena;
            let written = &arena[node as usize];
            // In a copy an INSTANCE with substitutions makes, a substitute that names a
            // definition of the instantiating module is that definition's name: TLC binds the
            // substitute to a `LazyValue` of it there too, which evaluates it again where it
            // failed as TLC started.
            let substituted = match &written.kind {
                NodeKind::Identifier(name) | NodeKind::Apply { name, .. }
                    if in_copy && !name.is_local =>
                {
                    match name.resolution {
                        Resolution::Definition(index) => {
                            self.definitions.get(index as usize).copied().filter(|&target| {
                                matches!(&arena[target as usize].kind,
                                    NodeKind::Definition(definition)
                                        if definition.flags & IrDefinition::SUBSTITUTED == 0
                                            && matches!(&definition.form,
                                                DefinitionForm::Operator(params) if params.is_empty()))
                            })
                        }
                        _ => None,
                    }
                }
                _ => None,
            };
            if let Some(target) = substituted
                && self.all.calls(target)
            {
                let is_kept = self.live.given.contains(&target);
                return self.read(target, is_kept, repeated, reads);
            }
            if let NodeKind::Reference(target) = &written.kind
                && written.range.is_some()
            {
                if !self.all.calls(*target) {
                    return false;
                }
                return self.read(*target, false, repeated, reads);
            }
            match &written.kind {
                NodeKind::Reference(target) => self.count(*target, repeated, in_copy, reads),
                NodeKind::Definition(definition) => {
                    let is_value = matches!(&definition.form,
                        DefinitionForm::Operator(params) if params.is_empty());
                    self.count(definition.body, repeated || !is_value, in_copy, reads)
                }
                NodeKind::Forall { bounds, body }
                | NodeKind::Exists { bounds, body }
                | NodeKind::FunctionConstruction { bounds, body, .. } => {
                    bounds
                        .iter()
                        .any(|bound| self.count(bound.set, repeated, in_copy, reads))
                        || self.count(*body, true, in_copy, reads)
                }
                NodeKind::SetMap { expression, bounds } => {
                    bounds
                        .iter()
                        .any(|bound| self.count(bound.set, repeated, in_copy, reads))
                        || self.count(*expression, true, in_copy, reads)
                }
                NodeKind::Choose { set, body, .. } => {
                    set.is_some_and(|set| self.count(set, repeated, in_copy, reads))
                        || self.count(*body, true, in_copy, reads)
                }
                NodeKind::SetFilter { bound, predicate } => {
                    self.count(bound.set, repeated, in_copy, reads)
                        || self.count(*predicate, true, in_copy, reads)
                }
                NodeKind::Lambda { body, .. } | NodeKind::UnboundedQuantifier { body, .. } => {
                    self.count(*body, true, in_copy, reads)
                }
                kind => kind
                    .children()
                    .into_iter()
                    .any(|child| self.count(child, repeated, in_copy, reads)),
            }
        }
    }
    let mut register_reads = CallReach::new(arena, definitions, reading, FastSet::default());
    let given = kept
        .iter()
        .copied()
        .filter(|&definition| !register_reads.calls(definition))
        .collect();
    let mut walk = Count {
        arena,
        definitions,
        live: CallReach::new(arena, definitions, drawing, given),
        all: CallReach::new(arena, definitions, drawing, FastSet::default()),
        recomputed,
        budget: 1_000_000,
    };
    definitions.iter().any(|&definition| {
        let NodeKind::Definition(written) = &arena[definition as usize].kind else {
            return false;
        };
        let is_function = matches!(written.form, DefinitionForm::Function(_));
        let mut reads = FastMap::default();
        walk.count(
            written.body,
            is_function,
            written.flags & IrDefinition::SUBSTITUTED != 0,
            &mut reads,
        )
    })
}

#[cfg(test)]
mod call_reach_tests {
    use super::*;

    // `G == F` and `F == IF G THEN G ELSE draw` as an arena: 0 G, 1 its body, 2 F, 3 its body,
    // 4 and 5 its reads of G, 6 the draw. Definitions 0 and 1 are G and F; builtin 0 draws.
    fn cycle() -> Vec<Node> {
        let node = |kind| Node {
            line: 0,
            column: 0,
            range: None,
            kind,
        };
        let name = |resolution| IrName {
            text: 0,
            resolution,
            is_local: false,
        };
        let definition = |body| {
            NodeKind::Definition(IrDefinition {
                name: 0,
                flags: IrDefinition::RECURSIVE,
                form: DefinitionForm::Operator(Vec::new()),
                body,
            })
        };
        vec![
            node(definition(1)),
            node(NodeKind::Identifier(name(Resolution::Definition(1)))),
            node(definition(3)),
            node(NodeKind::If {
                condition: 4,
                consequent: 5,
                alternative: 6,
            }),
            node(NodeKind::Identifier(name(Resolution::Definition(0)))),
            node(NodeKind::Identifier(name(Resolution::Definition(0)))),
            node(NodeKind::Identifier(name(Resolution::Builtin(0)))),
        ]
    }

    // A node on a cycle that a walk reached while the cycle's first node was still open holds
    // what the whole cycle reaches, whichever node a walk asks about first.
    #[test]
    fn a_cycle_reaches_alike_from_each_node() {
        let arena = cycle();
        let definitions = [0, 2];
        let drawing: FastSet<Index> = [0].into_iter().collect();
        let nothing = FastSet::default();
        for order in [[2, 0, 4, 1], [0, 2, 1, 4], [4, 5, 0, 2]] {
            let mut reach = CallReach::new(&arena, &definitions, &drawing, FastSet::default());
            for node in order {
                assert!(reach.calls(node), "{order:?} {node}");
            }
            let mut reach = CallReach::new(&arena, &definitions, &nothing, FastSet::default());
            for node in order {
                assert!(!reach.calls(node), "{order:?} {node}");
            }
            assert!(reach.open.is_empty() && reach.pending.is_empty() && reach.waiting.is_empty());
        }
        // Taking F as given, G reaches no draw, and F's own body still does.
        let mut reach = CallReach::new(&arena, &definitions, &drawing, [2].into_iter().collect());
        assert!(reach.calls(3));
        assert!(!reach.calls(0));
        assert!(reach.calls(2));
    }
}
