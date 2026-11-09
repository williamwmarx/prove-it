//! The lowering of a linked environment to the engine IR, as `lowerToIr` in `src/engine/ir.ts`
//! writes it: the nodes and definitions the model reaches, in the order `ir.ts` meets them, the
//! texts in the order it first uses them, and the builtins and constants the names resolve to.
//! `tla_ir::encode` writes the blob.

use std::cmp::Ordering;
use std::collections::HashMap;
use std::rc::Rc;

use tla_ir::{
    ActionProperty as IrActionProperty, Bound as IrBound, Builtin as IrBuiltin, ConfigName,
    Constant, Definition as IrDefinition, DefinitionForm, Index, Ir, Junction, Model,
    Name as IrName, Node, NodeId, NodeKind, Nodes, Param, PathStep, Pattern, Possible, Printed,
    Resolution, Scope as IrScope, ScopeBinding, Selector as IrSelector, SourceRange as IrRange,
    Startup, TextId, Update, Value, Values,
};

use crate::ast::*;
use crate::config::ConfigValue;
use crate::dependencies::{DefinitionFacts, create_definition_facts};
use crate::environment::Environment;
use crate::errors::FrontError;
use crate::hash::FastMap;
use crate::resolve::Result;

/// A model value named like `a_b` has the type `a`, which TLC won't compare with another type.
fn get_model_value_type(name: &str) -> Option<char> {
    let mut characters = name.chars();
    let first = characters.next()?;
    (name.encode_utf16().count() > 2 && characters.next() == Some('_')).then_some(first)
}

/// The texts TLC ranks, which come first in the IR's table, in rank order.
pub struct RankedTexts<'a> {
    pub texts: &'a [Rc<str>],
    pub ranks: FastMap<Rc<str>, u32>,
}

pub struct Lowering<'a> {
    environment: &'a Environment,
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
        Lowering {
            facts: create_definition_facts(environment),
            environment,
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

    /// The rank of a string or model value in TLC's string order, which the configuration's
    /// values are all in.
    fn get_rank(&self, text: &str) -> Result<u32> {
        self.ranked
            .ranks
            .get(text)
            .copied()
            .ok_or_else(|| FrontError::NotYet("a configuration value TLC doesn't rank".to_owned()))
    }

    /// `compareValues` on the configuration's values. Values of kinds TLC can't compare stop the
    /// front end, whose messages the startup phase will word.
    fn compare(&self, left: &ConfigValue, right: &ConfigValue) -> Result<Ordering> {
        Ok(match (left, right) {
            (ConfigValue::Number(left), ConfigValue::Number(right)) => left.total_cmp(right),
            (ConfigValue::String(left), ConfigValue::String(right)) => {
                if left == right {
                    Ordering::Equal
                } else {
                    self.get_rank(left)?.cmp(&self.get_rank(right)?)
                }
            }
            (ConfigValue::Boolean(left), ConfigValue::Boolean(right)) => {
                if left == right {
                    Ordering::Equal
                } else if left < right {
                    Ordering::Less
                } else {
                    Ordering::Greater
                }
            }
            (ConfigValue::ModelValue(left), ConfigValue::ModelValue(right)) => {
                if get_model_value_type(left).is_some()
                    && get_model_value_type(right).is_some()
                    && get_model_value_type(left) != get_model_value_type(right)
                {
                    return Err(FrontError::NotYet(
                        "differently-typed model values".to_owned(),
                    ));
                }
                self.get_rank(left)?.cmp(&self.get_rank(right)?)
            }
            (ConfigValue::ModelValue(name), _) | (_, ConfigValue::ModelValue(name))
                if get_model_value_type(name).is_some() =>
            {
                return Err(FrontError::NotYet(
                    "a typed model value compared".to_owned(),
                ));
            }
            (ConfigValue::ModelValue(_), _) => Ordering::Less,
            (_, ConfigValue::ModelValue(_)) => Ordering::Greater,
            (ConfigValue::Set(left), ConfigValue::Set(right)) => {
                if left.len() != right.len() {
                    left.len().cmp(&right.len())
                } else {
                    for (left, right) in left.iter().zip(right) {
                        let comparison = self.compare(left, right)?;
                        if comparison != Ordering::Equal {
                            return Ok(comparison);
                        }
                    }
                    Ordering::Equal
                }
            }
            _ => {
                return Err(FrontError::NotYet(
                    "configuration values TLC can't compare".to_owned(),
                ));
            }
        })
    }

    /// `toValue`: a set of the configuration is sorted and its duplicates dropped, as `createSet`
    /// does.
    fn normalize(&self, value: &ConfigValue) -> Result<ConfigValue> {
        let ConfigValue::Set(elements) = value else {
            return Ok(value.clone());
        };
        let elements = elements
            .iter()
            .map(|element| self.normalize(element))
            .collect::<Result<Vec<_>>>()?;
        let mut is_sorted = true;
        for pair in elements.windows(2) {
            if self.compare(&pair[0], &pair[1])? != Ordering::Less {
                is_sorted = false;
                break;
            }
        }
        if elements.len() < 2 || is_sorted {
            return Ok(ConfigValue::Set(elements));
        }
        // Sorting compares the elements pairwise; a comparison that fails stops the front end.
        let mut failure = None;
        let mut sorted = elements.clone();
        sorted.sort_by(|left, right| {
            self.compare(left, right).unwrap_or_else(|error| {
                failure.get_or_insert(error);
                Ordering::Equal
            })
        });
        if let Some(error) = failure {
            return Err(error);
        }
        let mut unique: Vec<ConfigValue> = Vec::with_capacity(sorted.len());
        for element in sorted {
            if let Some(last) = unique.last()
                && self.compare(last, &element)? == Ordering::Equal
            {
                continue;
            }
            unique.push(element);
        }
        Ok(ConfigValue::Set(unique))
    }

    /// `createStateEncoder`'s `encode` of one value, whose strings and model values name their
    /// texts by their position among the encoder's strings.
    fn encode_value(&mut self, value: &ConfigValue) -> u32 {
        let encoded = self.write_value(value);
        self.values.push(encoded);
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
        self.builtins.push(IrBuiltin {
            name: text,
            arity: builtin.arity as i32,
            flags: builtin.flags as i32,
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
                NodeKind::Identifier(self.write_name(&name, false, is_local)?)
            }
            ExpressionKind::Apply { args, .. } => {
                let name = expression.reference().unwrap_or_default();
                let name = self.write_name(&name, true, is_local)?;
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
        let not_yet = |reason: &str| FrontError::NotYet(reason.to_owned());
        let (Some(init), Some(next)) = (&specification.init, &specification.next) else {
            return Err(not_yet("a model without Init or Next"));
        };
        if !specification.temporals.is_empty() || !properties.liveness.is_empty() {
            return Err(not_yet("a temporal property or fairness"));
        }
        let is_scoped = properties
            .invariants
            .iter()
            .any(|property| property.scope.is_some())
            || properties
                .initial_predicates
                .iter()
                .any(|property| property.scope.is_some())
            || properties
                .action_properties
                .iter()
                .any(|property| property.scope.is_some());
        if is_scoped {
            return Err(not_yet("a property read in a scope"));
        }
        if config.symmetry.is_some() {
            return Err(not_yet(
                "SYMMETRY, which the engine's startup phase will compute",
            ));
        }
        let init = self.write_root(init)?;
        let next = self.write_root(next)?;
        let scope = self.get_scope_index(specification.scope.as_ref());
        let invariants = config
            .invariants
            .iter()
            .map(|name| self.config_name(name))
            .collect();
        let mut property_invariants = Vec::new();
        let mut property_invariant_names = Vec::new();
        for invariant in &properties.invariants {
            let root = self.write_root(&invariant.expression)?;
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
            action_properties.push(IrActionProperty { action, subscript });
        }
        let mut initial_predicates = Vec::new();
        for predicate in &properties.initial_predicates {
            initial_predicates.push(self.write_root(&predicate.expression)?);
        }
        let view = config
            .view
            .as_deref()
            .map(|name| self.config_name(name).root);
        let alias = config
            .alias
            .as_deref()
            .map(|name| self.config_name(name).root);
        let version = version.map(|version| self.get_text(version));
        Ok(Model {
            init,
            next,
            scope,
            actions: Vec::new(),
            is_labelled: false,
            invariants,
            property_invariants,
            property_invariant_names,
            constraints,
            action_constraints,
            possible,
            action_properties,
            initial_predicates,
            view,
            alias,
            check_deadlock: config.check_deadlock,
            is_warning_enabled,
            is_recording_graph: false,
            version,
            // TLC's default seed.
            random_seed: 0,
            atoms: Vec::new(),
            live_formula: Vec::new(),
            live_properties: Vec::new(),
            startup: Startup::default(),
        })
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

    pub fn finish(mut self, model: Model) -> Result<Ir> {
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
        Ok(Ir {
            ranked_count: self.ranked.texts.len() as u32,
            texts,
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
        })
    }
}
