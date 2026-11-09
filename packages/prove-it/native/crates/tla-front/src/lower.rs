//! The lowering of a linked environment to the engine IR, as `lowerToIr` in `src/engine/ir.ts`
//! writes it: the nodes and definitions the model reaches, in the order `ir.ts` meets them, the
//! texts in the order it first uses them, and the builtins and constants the names resolve to.
//! `tla_ir::encode` writes the blob.

use std::collections::HashMap;
use std::rc::Rc;

use tla_ir::{
    Bound as IrBound, Builtin as IrBuiltin, ConfigName, Constant, Definition as IrDefinition,
    DefinitionForm, Index, Ir, Junction, Model, Name as IrName, Node, NodeId, NodeKind, Nodes,
    Param, PathStep, Pattern, Printed, Resolution, Selector as IrSelector, SourceRange as IrRange,
    Startup, TextId, Update, Values,
};

use crate::ast::*;
use crate::dependencies::{DefinitionFacts, create_definition_facts};
use crate::environment::Environment;
use crate::errors::FrontError;
use crate::hash::FastMap;
use crate::resolve::Result;

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

    fn get_constant_index(&mut self, name: &Name) -> Result<Index> {
        if let Some(index) = self.constant_ids.get(name) {
            return Ok(*index);
        }
        // The configuration's values are encoded as transfer.ts encodes them, which slice 3 ports.
        Err(FrontError::NotYet("a constant's value".to_owned()))
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
        if self.environment.constants.contains(name) {
            return Ok(Resolution::Constant(self.get_constant_index(name)?));
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
        // TLC computes a startup value only when it starts, which the engine's startup phase will
        // do; until then, linking alone holds none.
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
            startup: Startup::None,
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
    pub fn finish(mut self, model: Model) -> Result<Ir> {
        let mut definitions = Vec::new();
        let mut next = 0;
        while next < self.definition_queue.len() {
            let definition = self.definition_queue[next].clone();
            next += 1;
            let id = self.write_definition(&definition)?;
            self.top.push(id);
            definitions.push(id);
        }
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
            tlc_order: Vec::new(),
            builtins: self.builtins,
            constants: self.constants,
            scopes: Vec::new(),
            values: Values {
                strings: Vec::new(),
                list: Vec::new(),
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
