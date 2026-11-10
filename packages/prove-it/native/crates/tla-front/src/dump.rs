//! The front end's results as canonical JSON, for `scripts/front-differential.ts` to compare with
//! the TypeScript front end's: each object's fields in key order, a field TypeScript leaves
//! `undefined` left out, as `JSON.stringify` does.

use std::rc::Rc;

use crate::ast::*;
use crate::errors::SyntaxError;
use crate::json::{write_js_number, write_js_string};

pub enum Json {
    Null,
    Bool(bool),
    Number(f64),
    Text(Rc<str>),
    Array(Vec<Json>),
    Object(Vec<(&'static str, Json)>),
}

impl Json {
    pub fn write(&self, out: &mut String) {
        match self {
            Json::Null => out.push_str("null"),
            Json::Bool(value) => out.push_str(if *value { "true" } else { "false" }),
            Json::Number(value) => write_js_number(out, *value),
            Json::Text(text) => write_js_string(out, text),
            Json::Array(items) => {
                out.push('[');
                for (index, item) in items.iter().enumerate() {
                    if index > 0 {
                        out.push(',');
                    }
                    item.write(out);
                }
                out.push(']');
            }
            Json::Object(fields) => {
                let mut sorted: Vec<&(&str, Json)> = fields.iter().collect();
                sorted.sort_by_key(|field| field.0);
                out.push('{');
                for (index, (key, value)) in sorted.into_iter().enumerate() {
                    if index > 0 {
                        out.push(',');
                    }
                    write_js_string(out, key);
                    out.push(':');
                    value.write(out);
                }
                out.push('}');
            }
        }
    }
}

fn text(value: &str) -> Json {
    Json::Text(Rc::from(value))
}

fn name(value: &Name) -> Json {
    Json::Text(value.clone())
}

fn number(value: usize) -> Json {
    Json::Number(value as f64)
}

fn list<T>(items: &[T], each: impl Fn(&T) -> Json) -> Json {
    Json::Array(items.iter().map(each).collect())
}

fn names(items: &[Name]) -> Json {
    list(items, name)
}

/// An object, leaving out the fields whose value is `None`.
fn object(fields: Vec<(&'static str, Option<Json>)>) -> Json {
    Json::Object(
        fields
            .into_iter()
            .filter_map(|(key, value)| value.map(|value| (key, value)))
            .collect(),
    )
}

fn position(value: &Position) -> Json {
    object(vec![
        ("line", Some(Json::Number(f64::from(value.line)))),
        ("column", Some(Json::Number(f64::from(value.column)))),
    ])
}

fn range(value: &SourceRange) -> Json {
    object(vec![
        ("module", Some(name(&value.module))),
        ("start", Some(position(&value.start))),
        ("end", Some(position(&value.end))),
    ])
}

fn ranges(values: &[Range]) -> Json {
    list(values, range)
}

fn location(value: &Location) -> Json {
    object(vec![
        ("line", Some(Json::Number(f64::from(value.line)))),
        ("column", Some(Json::Number(f64::from(value.column)))),
        ("range", value.range.as_ref().map(range)),
    ])
}

fn expressions(values: &[Expr]) -> Json {
    list(values, |value| expression(value))
}

fn pattern(value: &BoundPattern) -> Json {
    match value {
        BoundPattern::Name {
            name: bound,
            ranges: bound_ranges,
        } => object(vec![
            ("kind", Some(text("Name"))),
            ("name", Some(name(bound))),
            ("ranges", pattern_ranges(bound_ranges)),
        ]),
        BoundPattern::Tuple {
            names: bound,
            ranges: bound_ranges,
        } => object(vec![
            ("kind", Some(text("Tuple"))),
            ("names", Some(names(bound))),
            ("ranges", pattern_ranges(bound_ranges)),
        ]),
    }
}

/// A pattern the front end makes, such as an instance copy's, has no ranges.
fn pattern_ranges(values: &[Range]) -> Option<Json> {
    (!values.is_empty()).then(|| ranges(values))
}

fn bound(value: &Bound) -> Json {
    object(vec![
        ("pattern", Some(pattern(&value.pattern))),
        ("set", Some(expression(&value.set))),
    ])
}

fn bounds(values: &[Bound]) -> Json {
    list(values, bound)
}

fn selector(value: &Selector) -> Json {
    match value {
        Selector::Name { name: part, args } => object(vec![
            ("kind", Some(text("Name"))),
            ("name", Some(name(part))),
            ("args", Some(expressions(args))),
        ]),
        Selector::Operand(operand) => object(vec![
            ("kind", Some(text("Operand"))),
            (
                "operand",
                Some(match operand {
                    Operand::Index(index) => Json::Number(*index),
                    Operand::First => text("<<"),
                    Operand::Last => text(">>"),
                }),
            ),
        ]),
        Selector::Bound(args) => object(vec![
            ("kind", Some(text("Bound"))),
            ("args", Some(expressions(args))),
        ]),
        Selector::At => object(vec![("kind", Some(text("At")))]),
        Selector::Colon => object(vec![("kind", Some(text("Colon")))]),
    }
}

/// The fields of a node, with what resolution wrote on it: a name's key in place of its name, as
/// `resolve.ts` writes it, and `resolution`.
fn with_kind(kind: &str, value: &Expression, fields: Vec<(&'static str, Option<Json>)>) -> Json {
    let key = value.resolved.key.borrow().clone();
    let mut all = vec![
        ("kind", Some(text(kind))),
        ("location", Some(location(&value.location))),
        (
            "resolution",
            value
                .resolved
                .is_local
                .get()
                .then(|| object(vec![("kind", Some(text("Local")))])),
        ),
    ];
    all.extend(fields.into_iter().map(|(field, json)| match (&key, field) {
        (Some(key), "name" | "operator") => (field, Some(name(key))),
        _ => (field, json),
    }));
    object(all)
}

pub fn expression(value: &Expression) -> Json {
    let some = Some;
    match &value.kind {
        ExpressionKind::Number {
            value: number,
            text: typed,
        } => with_kind(
            "Number",
            value,
            vec![
                ("value", some(Json::Number(*number))),
                ("text", some(name(typed))),
            ],
        ),
        ExpressionKind::Decimal { text: typed } => {
            with_kind("Decimal", value, vec![("text", some(name(typed)))])
        }
        ExpressionKind::String { value: string } => {
            with_kind("String", value, vec![("value", some(name(string)))])
        }
        ExpressionKind::Identifier {
            name: identifier,
            spelling,
            selector_ranges,
        } => with_kind(
            "Identifier",
            value,
            vec![
                ("name", some(name(identifier))),
                ("spelling", spelling.as_ref().map(name)),
                ("selectorRanges", selector_ranges.as_deref().map(ranges)),
            ],
        ),
        ExpressionKind::Apply {
            operator,
            spelling,
            args,
            argument_counts,
            arguments_range,
            selector_ranges,
            argument_ranges,
        } => with_kind(
            "Apply",
            value,
            vec![
                ("operator", some(name(operator))),
                ("spelling", spelling.as_ref().map(name)),
                ("args", some(expressions(args))),
                (
                    "argumentCounts",
                    argument_counts
                        .as_deref()
                        .map(|counts| list(counts, |count| number(*count))),
                ),
                ("argumentsRange", arguments_range.as_ref().map(range)),
                ("selectorRanges", selector_ranges.as_deref().map(ranges)),
                (
                    "argumentRanges",
                    argument_ranges.as_deref().map(|values| {
                        list(values, |value| value.as_ref().map_or(Json::Null, range))
                    }),
                ),
            ],
        ),
        ExpressionKind::OperatorReference { operator, spelling } => with_kind(
            "OperatorReference",
            value,
            vec![
                ("operator", some(name(operator))),
                ("spelling", spelling.as_ref().map(name)),
            ],
        ),
        ExpressionKind::Lambda {
            params,
            param_ranges,
            body,
            operator,
        } => with_kind(
            "Lambda",
            value,
            vec![
                ("params", some(names(params))),
                ("paramRanges", param_ranges.as_deref().map(ranges)),
                ("body", some(expression(body))),
                ("operator", operator.as_ref().map(name)),
            ],
        ),
        ExpressionKind::Junction {
            is_and,
            operands,
            is_bulleted,
            prefix_ends,
        } => with_kind(
            if *is_and { "And" } else { "Or" },
            value,
            vec![
                ("operands", some(expressions(operands))),
                ("isBulleted", is_bulleted.then_some(Json::Bool(true))),
                (
                    "prefixEnds",
                    prefix_ends.as_deref().map(|ends| list(ends, position)),
                ),
            ],
        ),
        ExpressionKind::Prime(inner) => with_kind(
            "Prime",
            value,
            vec![("expression", some(expression(inner)))],
        ),
        ExpressionKind::Unchanged(inner) => with_kind(
            "Unchanged",
            value,
            vec![("expression", some(expression(inner)))],
        ),
        ExpressionKind::Enabled(inner) => with_kind(
            "Enabled",
            value,
            vec![("expression", some(expression(inner)))],
        ),
        ExpressionKind::Always(inner) => with_kind(
            "Always",
            value,
            vec![("expression", some(expression(inner)))],
        ),
        ExpressionKind::Eventually(inner) => with_kind(
            "Eventually",
            value,
            vec![("expression", some(expression(inner)))],
        ),
        ExpressionKind::If {
            condition,
            consequent,
            alternative,
        } => with_kind(
            "If",
            value,
            vec![
                ("condition", some(expression(condition))),
                ("consequent", some(expression(consequent))),
                ("alternative", some(expression(alternative))),
            ],
        ),
        ExpressionKind::Case { arms, other } => with_kind(
            "Case",
            value,
            vec![
                (
                    "arms",
                    some(list(arms, |arm| {
                        object(vec![
                            ("condition", some(expression(&arm.condition))),
                            ("body", some(expression(&arm.body))),
                        ])
                    })),
                ),
                ("other", other.as_deref().map(expression)),
            ],
        ),
        ExpressionKind::Let {
            definitions,
            instances,
            body,
            ..
        } => with_kind(
            "Let",
            value,
            vec![
                (
                    "definitions",
                    some(list(definitions, |item| definition(item))),
                ),
                (
                    "instances",
                    instances
                        .as_deref()
                        .map(|items| list(items, |item| instance(item))),
                ),
                ("body", some(expression(body))),
            ],
        ),
        ExpressionKind::Quantified {
            quantifier,
            bounds: quantified,
            body,
        } => with_kind(
            quantifier_name(*quantifier),
            value,
            vec![
                ("bounds", some(bounds(quantified))),
                ("body", some(expression(body))),
            ],
        ),
        ExpressionKind::UnboundedQuantifier {
            quantifier,
            names: bound,
            name_ranges,
            is_temporal,
            body,
        } => with_kind(
            "UnboundedQuantifier",
            value,
            vec![
                ("quantifier", some(text(quantifier_name(*quantifier)))),
                ("names", some(names(bound))),
                ("nameRanges", some(ranges(name_ranges))),
                ("isTemporal", some(Json::Bool(*is_temporal))),
                ("body", some(expression(body))),
            ],
        ),
        ExpressionKind::Choose {
            pattern: bound,
            set,
            body,
        } => with_kind(
            "Choose",
            value,
            vec![
                ("pattern", some(pattern(bound))),
                ("set", set.as_deref().map(expression)),
                ("body", some(expression(body))),
            ],
        ),
        ExpressionKind::SetEnumeration(elements) => with_kind(
            "SetEnumeration",
            value,
            vec![("elements", some(expressions(elements)))],
        ),
        ExpressionKind::SetFilter {
            bound: filtered,
            predicate,
        } => with_kind(
            "SetFilter",
            value,
            vec![
                ("bound", some(bound(filtered))),
                ("predicate", some(expression(predicate))),
            ],
        ),
        ExpressionKind::SetMap {
            expression: mapped,
            bounds: mapping,
        } => with_kind(
            "SetMap",
            value,
            vec![
                ("expression", some(expression(mapped))),
                ("bounds", some(bounds(mapping))),
            ],
        ),
        ExpressionKind::Tuple(elements) => with_kind(
            "Tuple",
            value,
            vec![("elements", some(expressions(elements)))],
        ),
        ExpressionKind::FunctionConstruction {
            bounds: constructed,
            body,
        } => with_kind(
            "FunctionConstruction",
            value,
            vec![
                ("bounds", some(bounds(constructed))),
                ("body", some(expression(body))),
                (
                    "isRecursive",
                    value
                        .resolved
                        .is_recursive
                        .get()
                        .then_some(Json::Bool(true)),
                ),
            ],
        ),
        ExpressionKind::FunctionSet {
            domain,
            range: codomain,
        } => with_kind(
            "FunctionSet",
            value,
            vec![
                ("domain", some(expression(domain))),
                ("range", some(expression(codomain))),
            ],
        ),
        ExpressionKind::Record { is_set, fields } => with_kind(
            if *is_set { "RecordSet" } else { "Record" },
            value,
            vec![(
                "fields",
                some(list(fields, |field| {
                    object(vec![
                        ("name", some(name(&field.name))),
                        ("value", some(expression(&field.value))),
                        ("location", some(location(&field.location))),
                    ])
                })),
            )],
        ),
        ExpressionKind::Except { function, updates } => with_kind(
            "Except",
            value,
            vec![
                ("function", some(expression(function))),
                (
                    "updates",
                    some(list(updates, |update| {
                        object(vec![
                            (
                                "path",
                                some(list(&update.path, |step| match step {
                                    ExceptPathStep::Field(field) => object(vec![
                                        ("kind", some(text("Field"))),
                                        ("name", some(name(field))),
                                    ]),
                                    ExceptPathStep::Index(args) => object(vec![
                                        ("kind", some(text("Index"))),
                                        ("args", some(expressions(args))),
                                    ]),
                                })),
                            ),
                            ("value", some(expression(&update.value))),
                        ])
                    })),
                ),
            ],
        ),
        ExpressionKind::ExceptAt => with_kind("ExceptAt", value, Vec::new()),
        ExpressionKind::FunctionApplication { function, args } => with_kind(
            "FunctionApplication",
            value,
            vec![
                ("function", some(expression(function))),
                ("args", some(expressions(args))),
            ],
        ),
        ExpressionKind::Bracket(args) => {
            with_kind("Bracket", value, vec![("args", some(expressions(args)))])
        }
        ExpressionKind::FieldAccess { record, field } => with_kind(
            "FieldAccess",
            value,
            vec![
                ("record", some(expression(record))),
                ("field", some(name(field))),
            ],
        ),
        ExpressionKind::Product(factors) => with_kind(
            "Product",
            value,
            vec![("factors", some(expressions(factors)))],
        ),
        ExpressionKind::Action {
            is_box,
            action,
            subscript,
        } => with_kind(
            if *is_box { "BoxAction" } else { "AngleAction" },
            value,
            vec![
                ("action", some(expression(action))),
                ("subscript", some(expression(subscript))),
            ],
        ),
        ExpressionKind::Fairness {
            is_strong,
            subscript,
            action,
            enabled,
        } => with_kind(
            if *is_strong {
                "StrongFairness"
            } else {
                "WeakFairness"
            },
            value,
            vec![
                ("subscript", some(expression(subscript))),
                ("action", some(expression(action))),
                ("enabled", enabled.as_deref().map(expression)),
            ],
        ),
        ExpressionKind::Label {
            name: label,
            params,
            param_ranges,
            body,
        } => with_kind(
            "Label",
            value,
            vec![
                ("name", some(name(label))),
                ("params", some(names(params))),
                ("paramRanges", some(ranges(param_ranges))),
                ("body", some(expression(body))),
            ],
        ),
        ExpressionKind::Subexpression {
            selectors,
            selector_ranges,
            argument_ranges,
        } => with_kind(
            "Subexpression",
            value,
            vec![
                ("selectors", some(list(selectors, selector))),
                ("selectorRanges", some(ranges(selector_ranges))),
                (
                    "argumentRanges",
                    some(list(argument_ranges, |value| {
                        value.as_ref().map_or(Json::Null, range)
                    })),
                ),
            ],
        ),
    }
}

fn quantifier_name(quantifier: Quantifier) -> &'static str {
    match quantifier {
        Quantifier::Forall => "Forall",
        Quantifier::Exists => "Exists",
    }
}

fn param(value: &OperatorParam) -> Json {
    object(vec![
        ("name", Some(name(&value.name))),
        ("arity", Some(number(value.arity))),
        ("location", value.location.as_ref().map(location)),
    ])
}

pub fn definition(value: &Definition) -> Json {
    let mut fields = vec![
        ("name", Some(name(&value.name))),
        ("body", Some(expression(&value.body))),
        ("isLocal", Some(Json::Bool(value.is_local))),
        ("isRecursive", Some(Json::Bool(value.is_recursive))),
        ("location", Some(location(&value.location))),
    ];
    match &value.kind {
        DefinitionKind::Operator { params, body_range } => {
            fields.push(("kind", Some(text("Operator"))));
            fields.push(("params", Some(list(params, param))));
            fields.push(("bodyRange", body_range.as_ref().map(range)));
        }
        DefinitionKind::Function { bounds: domain } => {
            fields.push(("kind", Some(text("Function"))));
            fields.push(("bounds", Some(bounds(domain))));
            fields.push((
                "isSelfReferential",
                value.is_self_referential.get().map(Json::Bool),
            ));
        }
    }
    object(fields)
}

fn declaration(value: &Declaration) -> Json {
    object(vec![
        ("name", Some(name(&value.name))),
        ("arity", Some(number(value.arity))),
        ("location", Some(location(&value.location))),
    ])
}

fn declarations(values: &[Rc<Declaration>]) -> Json {
    list(values, |value| declaration(value))
}

fn assumption(value: &Assumption) -> Json {
    object(vec![
        ("name", value.name.as_ref().map(name)),
        ("expression", Some(expression(&value.expression))),
        ("isAxiom", Some(Json::Bool(value.is_axiom))),
        ("location", Some(location(&value.location))),
    ])
}

pub fn instance(value: &Instance) -> Json {
    object(vec![
        ("kind", Some(text("Instance"))),
        ("name", value.name.as_ref().map(name)),
        ("params", Some(list(&value.params, param))),
        ("module", Some(name(&value.module))),
        (
            "substitutions",
            Some(list(&value.substitutions, |substitution| {
                object(vec![
                    ("name", Some(name(&substitution.name))),
                    ("nameRange", Some(range(&substitution.name_range))),
                    ("expression", Some(expression(&substitution.expression))),
                ])
            })),
        ),
        ("isLocal", Some(Json::Bool(value.is_local))),
        ("location", Some(location(&value.location))),
        ("instanceRange", Some(range(&value.instance_range))),
        (
            "definitionRange",
            value.definition_range.as_ref().map(range),
        ),
    ])
}

fn definition_unit(value: &DefinitionUnit) -> Json {
    match value {
        DefinitionUnit::Definition(item) => definition(item),
        DefinitionUnit::Instance(item) => instance(item),
    }
}

fn new_symbol(value: &NewSymbol) -> Json {
    object(vec![
        ("kind", Some(text("NewSymbol"))),
        ("name", Some(name(&value.name))),
        ("arity", Some(number(value.arity))),
        ("level", Some(text(value.level.name()))),
        ("set", value.set.as_deref().map(expression)),
        ("nameRange", value.name_range.as_ref().map(range)),
        ("location", Some(location(&value.location))),
    ])
}

fn assume_prove(value: &AssumeProve) -> Json {
    object(vec![
        ("kind", Some(text("AssumeProve"))),
        (
            "assumptions",
            Some(list(&value.assumptions, |assumed| match assumed {
                Assumed::Expression(item) => expression(item),
                Assumed::NewSymbol(item) => new_symbol(item),
                Assumed::AssumeProve(item) => assume_prove(item),
            })),
        ),
        ("conclusion", Some(expression(&value.conclusion))),
        ("location", Some(location(&value.location))),
    ])
}

fn statement(value: &Statement) -> Json {
    match value {
        Statement::Expression(item) => expression(item),
        Statement::AssumeProve(item) => assume_prove(item),
    }
}

fn fact(value: &Fact) -> Json {
    match value {
        Fact::Expression(item) => expression(item),
        Fact::Module {
            name: module,
            location: at,
        } => object(vec![
            ("kind", Some(text("ModuleFact"))),
            ("name", Some(name(module))),
            ("location", Some(location(at))),
        ]),
    }
}

fn use_or_hide(value: &UseOrHide) -> Json {
    object(vec![
        (
            "kind",
            Some(text(if value.is_hide { "Hide" } else { "Use" })),
        ),
        ("isOnly", Some(Json::Bool(value.is_only))),
        ("facts", Some(list(&value.facts, fact))),
        ("defs", Some(list(&value.defs, fact))),
        ("keyword", Some(range(&value.keyword))),
        ("location", Some(location(&value.location))),
    ])
}

fn proof(value: &Proof) -> Json {
    let at = Some(location(&value.location));
    match &value.kind {
        ProofKind::Obvious { keyword } => object(vec![
            ("kind", Some(text("Obvious"))),
            ("keyword", Some(range(keyword))),
            ("location", at),
        ]),
        ProofKind::Omitted { keyword } => object(vec![
            ("kind", Some(text("Omitted"))),
            ("keyword", Some(range(keyword))),
            ("location", at),
        ]),
        ProofKind::By {
            is_only,
            facts,
            defs,
            keyword,
        } => object(vec![
            ("kind", Some(text("By"))),
            ("isOnly", Some(Json::Bool(*is_only))),
            ("facts", Some(list(facts, fact))),
            ("defs", Some(list(defs, fact))),
            ("keyword", Some(range(keyword))),
            ("location", at),
        ]),
        ProofKind::Steps { level, steps } => object(vec![
            ("kind", Some(text("Steps"))),
            ("level", Some(Json::Number(*level as f64))),
            ("steps", Some(list(steps, step))),
            ("location", at),
        ]),
    }
}

fn step_body(value: &StepBody) -> Json {
    let kind = |name: &str| ("kind", Some(text(name)));
    match value {
        StepBody::UseOrHide(item) => use_or_hide(item),
        StepBody::Instance(item) => instance(item),
        StepBody::Define {
            definitions,
            location: at,
        } => object(vec![
            kind("Define"),
            ("definitions", Some(list(definitions, definition_unit))),
            ("location", Some(location(at))),
        ]),
        StepBody::Have(item) => object(vec![kind("Have"), ("expression", Some(expression(item)))]),
        StepBody::Take {
            names: taken,
            name_ranges,
            bounds: domain,
        } => object(vec![
            kind("Take"),
            ("names", Some(names(taken))),
            ("nameRanges", Some(ranges(name_ranges))),
            ("bounds", Some(bounds(domain))),
        ]),
        StepBody::Witness(items) => object(vec![
            kind("Witness"),
            ("expressions", Some(expressions(items))),
        ]),
        StepBody::Pick {
            names: picked,
            name_ranges,
            bounds: domain,
            body,
        } => object(vec![
            kind("Pick"),
            ("names", Some(names(picked))),
            ("nameRanges", Some(ranges(name_ranges))),
            ("bounds", Some(bounds(domain))),
            ("body", Some(expression(body))),
        ]),
        StepBody::Case(item) => object(vec![kind("Case"), ("expression", Some(expression(item)))]),
        StepBody::Assert {
            is_suffices,
            statement: asserted,
        } => object(vec![
            kind("Assert"),
            ("isSuffices", Some(Json::Bool(*is_suffices))),
            ("statement", Some(statement(asserted))),
        ]),
        StepBody::Qed => object(vec![kind("Qed")]),
    }
}

fn step(value: &ProofStep) -> Json {
    object(vec![
        ("name", value.name.as_ref().map(name)),
        ("token", Some(name(&value.token))),
        ("body", Some(step_body(&value.body))),
        ("head", Some(range(&value.head))),
        ("statement", Some(range(&value.statement))),
        ("proof", value.proof.as_deref().map(proof)),
        ("location", Some(location(&value.location))),
    ])
}

fn theorem(value: &Theorem) -> Json {
    object(vec![
        ("name", value.name.as_ref().map(name)),
        ("statement", Some(statement(&value.statement))),
        ("proof", value.proof.as_ref().map(proof)),
        ("location", Some(location(&value.location))),
    ])
}

fn unit(value: &ModuleUnit) -> Json {
    let kind = |name: &str| ("kind", Some(text(name)));
    match value {
        ModuleUnit::Constants {
            declarations: items,
            location: at,
        } => object(vec![
            kind("Constants"),
            ("declarations", Some(declarations(items))),
            ("location", Some(location(at))),
        ]),
        ModuleUnit::Variables {
            declarations: items,
            location: at,
        } => object(vec![
            kind("Variables"),
            ("declarations", Some(declarations(items))),
            ("location", Some(location(at))),
        ]),
        ModuleUnit::Recursive(items) => object(vec![
            kind("Recursive"),
            ("declarations", Some(declarations(items))),
        ]),
        ModuleUnit::Definition(item) => object(vec![
            kind("Definition"),
            ("definition", Some(definition(item))),
        ]),
        ModuleUnit::Instance(item) => {
            object(vec![kind("Instance"), ("instance", Some(instance(item)))])
        }
        ModuleUnit::Assumption(item) => object(vec![
            kind("Assumption"),
            ("assumption", Some(assumption(item))),
        ]),
        ModuleUnit::Theorem(item) => {
            object(vec![kind("Theorem"), ("theorem", Some(theorem(item)))])
        }
        ModuleUnit::Use(item) => object(vec![kind("Use"), ("use", Some(use_or_hide(item)))]),
        ModuleUnit::Module(item) => object(vec![kind("Module"), ("module", Some(module(item)))]),
    }
}

pub fn module(value: &Module) -> Json {
    object(vec![
        ("name", Some(name(&value.name))),
        ("modules", Some(list(&value.modules, |item| module(item)))),
        ("extends", Some(names(&value.extends))),
        ("extendsRanges", Some(ranges(&value.extends_ranges))),
        ("constants", Some(declarations(&value.constants))),
        ("variables", Some(declarations(&value.variables))),
        (
            "definitions",
            Some(list(&value.definitions, |item| definition(item))),
        ),
        (
            "instances",
            Some(list(&value.instances, |item| instance(item))),
        ),
        (
            "assumptions",
            Some(list(&value.assumptions, |item| assumption(item))),
        ),
        ("location", Some(location(&value.location))),
        (
            "theorems",
            Some(list(&value.theorems, |item| theorem(item))),
        ),
        ("uses", Some(list(&value.uses, |item| use_or_hide(item)))),
        ("units", Some(list(&value.units, unit))),
    ])
}

pub fn syntax_error(value: &SyntaxError) -> Json {
    object(vec![
        ("error", Some(text(&value.message))),
        (
            "failure",
            value.failure.as_ref().map(|failure| {
                object(vec![
                    ("reason", Some(text(&failure.reason))),
                    ("line", Some(Json::Number(f64::from(failure.line)))),
                    ("column", Some(Json::Number(f64::from(failure.column)))),
                    ("isEnd", Some(Json::Bool(failure.is_end))),
                ])
            }),
        ),
        (
            "sany",
            value.sany.as_ref().map(|report| {
                let errors = |items: &[crate::errors::SanyError]| {
                    list(items, |item| {
                        object(vec![
                            ("location", Some(text(&item.location))),
                            ("message", Some(text(&item.message))),
                        ])
                    })
                };
                object(vec![
                    ("errors", Some(errors(&report.errors))),
                    ("warnings", Some(errors(&report.warnings))),
                    ("isFatal", Some(Json::Bool(report.is_fatal))),
                    ("parseError", report.parse_error.as_deref().map(text)),
                ])
            }),
        ),
    ])
}

fn config_value(value: &crate::config::ConfigValue) -> Json {
    use crate::config::ConfigValue;
    let kind = |name: &str| ("kind", Some(text(name)));
    match value {
        ConfigValue::Number(number) => {
            object(vec![kind("Number"), ("value", Some(Json::Number(*number)))])
        }
        ConfigValue::String(string) => object(vec![kind("String"), ("value", Some(text(string)))]),
        ConfigValue::Boolean(boolean) => {
            object(vec![kind("Boolean"), ("value", Some(Json::Bool(*boolean)))])
        }
        ConfigValue::ModelValue(model) => {
            object(vec![kind("ModelValue"), ("name", Some(text(model)))])
        }
        ConfigValue::Set(elements) => object(vec![
            kind("Set"),
            ("elements", Some(list(elements, config_value))),
        ]),
        ConfigValue::Record(fields) => object(vec![
            kind("Record"),
            (
                "fields",
                Some(list(fields, |(name, value)| {
                    object(vec![
                        ("name", Some(text(name))),
                        ("value", Some(config_value(value))),
                    ])
                })),
            ),
        ]),
    }
}

pub fn config(value: &Result<crate::config::ModelConfig, crate::config::ConfigError>) -> Json {
    let config = match value {
        Ok(config) => config,
        Err(error) => return object(vec![("error", Some(text(&error.message)))]),
    };
    let optional = |value: &Option<String>| value.as_deref().map(text);
    let words = |values: &[String]| Some(list(values, |value| text(value)));
    object(vec![
        ("init", optional(&config.init)),
        ("next", optional(&config.next)),
        ("specification", optional(&config.specification)),
        ("invariants", words(&config.invariants)),
        ("properties", words(&config.properties)),
        ("constraints", words(&config.constraints)),
        ("actionConstraints", words(&config.action_constraints)),
        (
            "constants",
            Some(list(&config.constants, |constant| {
                object(vec![
                    ("name", Some(text(&constant.name))),
                    ("value", Some(config_value(&constant.value))),
                    (
                        "args",
                        constant
                            .args
                            .as_deref()
                            .map(|args| list(args, config_value)),
                    ),
                    ("module", optional(&constant.module)),
                ])
            })),
        ),
        (
            "substitutions",
            Some(list(&config.substitutions, |substitution| {
                object(vec![
                    ("name", Some(text(&substitution.name))),
                    ("target", Some(text(&substitution.target))),
                    ("module", optional(&substitution.module)),
                ])
            })),
        ),
        ("checkDeadlock", Some(Json::Bool(config.check_deadlock))),
        ("symmetry", optional(&config.symmetry)),
        ("view", optional(&config.view)),
        ("alias", optional(&config.alias)),
        ("postconditions", words(&config.postconditions)),
        ("possible", words(&config.possible)),
        ("periodic", optional(&config.periodic)),
        ("rlReward", optional(&config.rl_reward)),
    ])
}

/// The facts of the environment's definitions, as `createDefinitionFacts` writes their rows.
fn facts(environment: &crate::environment::Environment) -> Json {
    let facts = crate::dependencies::create_definition_facts(environment);
    object(vec![
        ("words", Some(number(facts.words()))),
        (
            "rows",
            Some(list(facts.rows(), |word| Json::Number(f64::from(*word)))),
        ),
    ])
}

/// What linking makes of a spec, for `front-differential.ts resolve`: each definition by key, in
/// the environment's order, written the first time the environment holds it and named by that
/// key after; the builtins by key, with name, arity and flags; the variables and their indices;
/// the root module's constants; and what linking prints. A failure is its error, or `notYet` with
/// what the Rust front end doesn't cover yet.
pub fn environment(
    value: &Result<crate::environment::Environment, crate::errors::FrontError>,
) -> Json {
    use crate::errors::FrontError;
    let environment = match value {
        Ok(environment) => environment,
        Err(FrontError::Syntax(error)) => return syntax_error(error),
        Err(FrontError::Evaluation(message) | FrontError::Config(message)) => {
            return object(vec![("error", Some(text(message)))]);
        }
        Err(FrontError::StackOverflow) => {
            return object(vec![(
                "error",
                Some(text(crate::tlc_messages::STACK_OVERFLOW_MESSAGE)),
            )]);
        }
        Err(FrontError::NotYet(reason)) => return object(vec![("notYet", Some(text(reason)))]),
    };
    let mut keys: crate::hash::FastMap<*const Definition, Name> = Default::default();
    let definitions = environment
        .definitions
        .iter()
        .map(|(key, value)| {
            let written = match keys.get(&Rc::as_ptr(value)) {
                Some(first) => object(vec![("same", Some(name(first)))]),
                None => {
                    keys.insert(Rc::as_ptr(value), key.clone());
                    definition(value)
                }
            };
            Json::Array(vec![name(key), written])
        })
        .collect();
    object(vec![
        ("definitions", Some(Json::Array(definitions))),
        (
            "builtins",
            Some(Json::Array(
                environment
                    .builtins
                    .iter()
                    .map(|(key, builtin)| {
                        Json::Array(vec![
                            name(key),
                            name(&builtin.name),
                            number(builtin.arity),
                            Json::Number(f64::from(builtin.flags)),
                        ])
                    })
                    .collect(),
            )),
        ),
        (
            "substituted",
            Some(Json::Array(
                environment
                    .definitions
                    .iter()
                    .filter(|(_, value)| environment.is_substituted(value))
                    .map(|(key, _)| name(key))
                    .collect(),
            )),
        ),
        ("facts", Some(facts(environment))),
        (
            "assigned",
            Some(Json::Array(
                environment.constants.keys().map(name).collect(),
            )),
        ),
        (
            "substitutions",
            Some(Json::Array(
                environment
                    .substitutions
                    .iter()
                    .map(|(key, target)| Json::Array(vec![name(key), name(target)]))
                    .collect(),
            )),
        ),
        ("variables", Some(names(&environment.variables))),
        (
            "variableIndex",
            Some(Json::Array(
                environment
                    .variable_index
                    .iter()
                    .map(|(key, index)| Json::Array(vec![name(key), number(*index)]))
                    .collect(),
            )),
        ),
        (
            "constants",
            Some(list(&environment.root_constants, |constant| {
                name(&constant.name)
            })),
        ),
        (
            "printed",
            Some(list(&environment.printed, |printed| text(printed))),
        ),
        (
            "assumptions",
            Some(Json::Array(
                environment
                    .assumptions
                    .iter()
                    .filter(|assumption| !assumption.is_axiom)
                    .map(|assumption| text(&crate::errors::describe_range(&assumption.expression)))
                    .collect(),
            )),
        ),
        ("levels", Some(levels(environment, &keys))),
        (
            "startup",
            Some(list(&environment.startup_definitions, |definition| {
                name(&keys[&Rc::as_ptr(definition)])
            })),
        ),
    ])
}

/// Each operator without parameters by its first key, with its body's level (`getLevel`).
fn levels(
    environment: &crate::environment::Environment,
    keys: &crate::hash::FastMap<*const Definition, Name>,
) -> Json {
    let facts = crate::dependencies::create_definition_facts(environment);
    Json::Array(
        environment
            .definitions
            .iter()
            .filter(|(key, definition)| {
                keys.get(&Rc::as_ptr(definition)) == Some(key)
                    && matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty())
            })
            .map(|(key, definition)| {
                let level = crate::spec::get_level(&definition.body, None, environment, &facts, &[]);
                Json::Array(vec![name(key), number(level as usize)])
            })
            .collect(),
    )
}

/// What `front-differential spec` compares of `getSpecification`: Init's conjuncts and Next, each
/// its name if an identifier and where it is written, the scope's names, and the temporals.
pub fn specification(
    value: &Result<crate::spec::Specification, crate::errors::FrontError>,
) -> Json {
    use crate::errors::{FrontError, describe_range};
    let specification = match value {
        Ok(specification) => specification,
        Err(FrontError::Syntax(error)) => return syntax_error(error),
        Err(FrontError::Evaluation(message) | FrontError::Config(message)) => {
            return object(vec![("error", Some(text(message)))]);
        }
        Err(FrontError::StackOverflow) => {
            return object(vec![(
                "error",
                Some(text(crate::tlc_messages::STACK_OVERFLOW_MESSAGE)),
            )]);
        }
        Err(FrontError::NotYet(reason)) => return object(vec![("notYet", Some(text(reason)))]),
    };
    let describe = |expression: &Expr| {
        Json::Array(vec![
            match &expression.kind {
                ExpressionKind::Identifier { .. } => {
                    name(&expression.reference().unwrap_or_default())
                }
                _ => Json::Null,
            },
            text(&describe_range(expression)),
        ])
    };
    let init = specification.init.as_ref().map(|init| match &init.kind {
        ExpressionKind::Junction {
            is_and: true,
            operands,
            ..
        } => Json::Array(operands.iter().map(describe).collect()),
        _ => Json::Array(vec![describe(init)]),
    });
    let mut names = Vec::new();
    let mut scope = specification.scope.as_ref();
    while let Some(current) = scope {
        names.push(name(&current.name));
        scope = current.parent.as_ref();
    }
    object(vec![
        ("init", Some(init.unwrap_or(Json::Null))),
        (
            "next",
            Some(specification.next.as_ref().map_or(Json::Null, describe)),
        ),
        ("scope", Some(Json::Array(names))),
        (
            "temporals",
            Some(Json::Array(
                specification
                    .temporals
                    .iter()
                    .map(|temporal| text(&describe_range(&temporal.expression)))
                    .collect(),
            )),
        ),
    ])
}

/// What `front-differential properties` compares of `getProperties`: each conjunct's name, where
/// it is written, and whether it reads a scope.
pub fn properties(value: &Result<crate::spec::Properties, crate::errors::FrontError>) -> Json {
    use crate::errors::{FrontError, describe_range};
    let properties = match value {
        Ok(properties) => properties,
        Err(FrontError::Syntax(error)) => return syntax_error(error),
        Err(FrontError::Evaluation(message) | FrontError::Config(message)) => {
            return object(vec![("error", Some(text(message)))]);
        }
        Err(FrontError::StackOverflow) => {
            return object(vec![(
                "error",
                Some(text(crate::tlc_messages::STACK_OVERFLOW_MESSAGE)),
            )]);
        }
        Err(FrontError::NotYet(reason)) => return object(vec![("notYet", Some(text(reason)))]),
    };
    let describe = |property: &crate::spec::Property| {
        Json::Array(vec![
            name(&property.name),
            text(&describe_range(&property.expression)),
            Json::Bool(property.scope.is_some()),
        ])
    };
    object(vec![
        ("invariants", Some(list(&properties.invariants, describe))),
        (
            "actionProperties",
            Some(list(&properties.action_properties, |property| {
                Json::Array(vec![
                    name(&property.name),
                    text(&describe_range(&property.action)),
                    text(&describe_range(&property.subscript)),
                    Json::Bool(property.scope.is_some()),
                ])
            })),
        ),
        (
            "initialPredicates",
            Some(list(&properties.initial_predicates, describe)),
        ),
        ("liveness", Some(list(&properties.liveness, describe))),
        ("stateLevel", Some(list(&properties.state_level, name))),
    ])
}
