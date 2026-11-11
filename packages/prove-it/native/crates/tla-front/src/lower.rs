//! The lowering of a linked environment to the engine IR, as `lowerToIr` in `src/engine/ir.ts`
//! writes it: the nodes and definitions the model reaches, in the order `ir.ts` meets them, the
//! texts in the order it first uses them, and the builtins and constants the names resolve to.
//! `tla_ir::encode` writes the blob.

use std::collections::HashMap;
use std::rc::Rc;

use tla_ir::{
    ActionProperty as IrActionProperty, Atom as IrAtom, AtomKind, Bound as IrBound,
    Builtin as IrBuiltin, ConfigName, Constant, Definition as IrDefinition, DefinitionForm,
    EnabledActions, Index, Ir, Junction, LiveProperty, LiveTerm, Model, Name as IrName, Node,
    NodeId, NodeKind, Nodes, Param, PathStep, Pattern, PermutedSet, Possible, Printed, Resolution,
    Scope as IrScope, ScopeBinding, Selector as IrSelector, SourceRange as IrRange, Startup,
    Symmetry, TextId, Update, Value, Values,
};

use crate::ast::*;
use crate::config::ConfigValue;
use crate::dependencies::{DefinitionFacts, create_definition_facts};
use crate::environment::Environment;
use crate::errors::{FrontError, describe_range};
use crate::hash::{FastMap, FastSet};
use crate::live::{Live, Liveness};
use crate::resolve::Result;
use crate::values::ValueOrder;

/// SyntaxTreeNode.getHumanReadableImage, which joins the tokens of an expression without spaces.
fn get_expression_image(expression: &Expression) -> String {
    let name = expression.reference().unwrap_or_default();
    match &expression.kind {
        ExpressionKind::Identifier { .. } => name.to_string(),
        ExpressionKind::Apply { args, .. } => {
            let args: Vec<String> = args.iter().map(|arg| get_expression_image(arg)).collect();
            if name
                .chars()
                .next()
                .is_some_and(|first| first.is_ascii_alphabetic() || first == '_')
            {
                format!("{name}({})", args.join(","))
            } else {
                args.join(&name)
            }
        }
        _ => String::new(),
    }
}

/// The texts TLC ranks, which come first in the IR's table, in rank order.
pub struct RankedTexts<'a> {
    pub texts: &'a [Rc<str>],
    pub ranks: FastMap<Rc<str>, u32>,
    /// The units of each ranked text with a lone surrogate, by the name it ranks by.
    pub wide: &'a FastMap<Rc<str>, Box<[u16]>>,
}

/// `isStartupDefinition`: a constant definition without parameters the configuration doesn't
/// replace.
fn is_startup_definition(
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

/// The builtins whose effects show each time TLC evaluates them again: they print, set a
/// register, draw at random, or read the clock or TLC's registers. Reading a file or the process's
/// environment again reads the same.
const SHOWN_EFFECTS: [&str; 9] = [
    "Print",
    "PrintT",
    "TLCSet",
    "TLCGet",
    "JavaTime",
    "RandomElement",
    "RandomSubset",
    "RandomSetOfSubsets",
    "RandomSubsetSet",
];

/// Whether evaluating the definition again can show, as by printing twice, other than through
/// `cached`, whose value TLC keeps.
fn reaches_shown_effect(
    definition: &Rc<Definition>,
    environment: &Environment,
    cached: Option<&Rc<Definition>>,
) -> bool {
    let mut seen: FastSet<usize> = cached
        .map(|cached| Rc::as_ptr(cached) as usize)
        .into_iter()
        .collect();
    let mut pending = vec![definition.body.clone()];
    while let Some(expression) = pending.pop() {
        if let Some(name) = expression.reference()
            && !expression.is_locally_resolved()
        {
            if SHOWN_EFFECTS.contains(&&*name) && !environment.definitions.contains_key(&name) {
                return true;
            }
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
    /// The evaluator of the constant parts of the liveness formula, without which they stay
    /// `NotYet`.
    pub evaluator: Option<&'a crate::eval::Evaluator<'a>>,
    /// The constant definitions TLC computes and deep-normalizes at startup, by address.
    normalized: FastSet<usize>,
    facts: DefinitionFacts,
    ranked: RankedTexts<'a>,
    extra_texts: Vec<Name>,
    extra_ids: FastMap<Name, TextId>,
    arena: Vec<Node>,
    top: Vec<NodeId>,
    junctions: HashMap<NodeId, Junction>,
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
}

impl<'a> Lowering<'a> {
    pub fn new(environment: &'a Environment, ranked: RankedTexts<'a>) -> Lowering<'a> {
        let facts = create_definition_facts(environment);
        Lowering {
            branches: None,
            random_seed: 0,
            normalized: environment
                .startup_definitions
                .iter()
                .filter(|definition| is_startup_definition(definition, environment, &facts))
                .map(|definition| Rc::as_ptr(definition) as usize)
                .collect(),
            facts,
            environment,
            evaluator: None,
            ranked,
            extra_texts: Vec::new(),
            extra_ids: FastMap::default(),
            arena: Vec::new(),
            top: Vec::new(),
            junctions: HashMap::new(),
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
        let text = self.get_text(name);
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
        let flags = builtin.flags as i32 | table.as_ref().map_or(0, |_| IrBuiltin::TABLE);
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
        } | if self.environment.is_substituted(definition) {
            IrDefinition::SUBSTITUTED
        } else {
            0
        } | if self.normalized.contains(&(Rc::as_ptr(definition) as usize)) {
            IrDefinition::NORMALIZED
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
        let id = self.open(&expression.location);
        self.node_ids.insert(address, (expression.clone(), id));
        let is_local = expression.resolved.is_local.get();
        let kind = match &expression.kind {
            ExpressionKind::Number { value, text } => {
                if value.fract() == 0.0
                    && *value >= f64::from(i32::MIN)
                    && *value <= f64::from(i32::MAX)
                {
                    NodeKind::Number(*value as i32)
                } else {
                    NodeKind::WideNumber(self.get_text(text))
                }
            }
            ExpressionKind::Decimal { text } => NodeKind::Decimal(self.get_text(text)),
            ExpressionKind::String { value } => NodeKind::String(self.get_text(value)),
            ExpressionKind::Identifier { .. } => {
                let name = expression.reference().unwrap_or_default();
                NodeKind::Identifier(self.write_bound_name(&name, false, is_local)?)
            }
            ExpressionKind::Apply { args, .. } => {
                let name = expression.reference().unwrap_or_default();
                let name = self.write_bound_name(&name, true, is_local)?;
                NodeKind::Apply {
                    name,
                    args: self.write_nodes(args)?,
                }
            }
            ExpressionKind::OperatorReference { .. } => {
                let name = expression.reference().unwrap_or_default();
                NodeKind::OperatorReference(self.write_name(&name, true, false)?)
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
                body,
                ..
            } => {
                let names = self.write_texts(names);
                NodeKind::UnboundedQuantifier {
                    is_forall: *quantifier == Quantifier::Forall,
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
        self.arena[id as usize].kind = kind;
        Ok(id)
    }

    /// Writes an expression something outside the nodes refers to, unless it is written already,
    /// and returns its id.
    pub fn write_root(&mut self, expression: &Expr) -> Result<NodeId> {
        if let Some((_, known)) = self.node_ids.get(&(Rc::as_ptr(expression) as usize)) {
            return Ok(*known);
        }
        let id = self.write_node(expression)?;
        self.top.push(id);
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
        // `createLivenessChecker` runs inside `withUnexpectedException`.
        .map_err(crate::tlc_messages::with_unexpected_exception)
        // TLC warns that a symmetry is dangerous for liveness as it starts the liveness checker,
        // before it fails here, which the front end's failure doesn't print.
        .map_err(|error| match error {
            FrontError::NotYet(_) => error,
            _ if config.symmetry.is_some() && is_warning_enabled => {
                not_yet("a temporal property TLC rejects after it warns about the symmetry")
            }
            _ => error,
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
            let action = self.write_root(&property.action)?;
            let subscript = self.write_root(&property.subscript)?;
            action_properties.push(IrActionProperty {
                action,
                subscript,
                scope: self.get_scope_index(property.scope.as_ref()),
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
        let alias = config
            .alias
            .as_deref()
            .map(|name| self.config_name(name).root);
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
        let specification =
            definition.and_then(|definition| self.write_range(definition.location.range.as_ref()));
        let startup = self.write_startup(config)?;
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
            atoms,
            live_formula,
            live_properties,
            specification,
            startup,
            next_substitution: None,
            instance_actions: Vec::new(),
            instance_names: Vec::new(),
            tlc_spec: None,
        })
    }

    /// `getIrStartup`: what TLC evaluates when it starts. The substitutes it checks, the constant
    /// definitions with effects (one without computes the same wherever it is first used), and
    /// the assumptions that aren't axioms. SYMMETRY is `NotYet` before this.
    fn write_startup(&mut self, config: &crate::config::ModelConfig) -> Result<Startup> {
        let environment = self.environment;
        let mut substitutes = Vec::new();
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
            if is_constant && reaches_shown_effect(definition, environment, None) && !is_cached() {
                return Err(FrontError::NotYet(format!(
                    "a configuration substitute with effects, which TLC evaluates at every use: \
                     {name} <- {target}"
                )));
            }
            let is_checked = is_constant
                && matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty())
                && !self.facts.is_constant_level(definition, environment);
            if is_checked {
                let text = self.get_text(name);
                substitutes.push((text, self.get_definition_index(definition)));
            }
        }
        let mut seen = FastSet::default();
        let startup_definitions: Vec<Rc<Definition>> = environment
            .startup_definitions
            .iter()
            .filter(|definition| {
                is_startup_definition(definition, environment, &self.facts)
                    && self.facts.is_impure_definition(definition, environment)
                    && seen.insert(Rc::as_ptr(definition) as usize)
            })
            .cloned()
            .collect();
        let definitions = startup_definitions
            .iter()
            .map(|definition| self.get_definition_index(definition))
            .collect();
        let mut predicates = Vec::new();
        for (form, kind, name, definition) in
            crate::spec::get_constant_predicates(config, environment, &self.facts)
        {
            predicates.push(tla_ir::StartupPredicate {
                form,
                kind: self.get_text(kind),
                name: self.get_text(&name),
                definition: self.get_definition_index(&definition),
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
        Ok(Startup {
            substitutes,
            definitions,
            predicates,
            symmetry,
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
        // fails on a body that is no application, such as a LET (`Tool.getSymmetryPerms`).
        let permuted = match &definition.body.kind {
            ExpressionKind::Apply { args, .. } => args.clone(),
            ExpressionKind::Identifier { .. } => Vec::new(),
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
            let image = get_expression_image(operand.as_ref().unwrap_or(&set));
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
            Binding::Value(value) => {
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
        let startup = environment
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
            },
        };
        Ok((ir, startup))
    }
}

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
