//! TLC's actions: the next-state relation split as `Tool.getActions` splits it
//! (`getActions` in `spec-description.ts`), each with the name and location a trace labels a step
//! with. A disjunction splits into its disjuncts, `\E` over a constant set into an action for each
//! binding, and an operator applied to constant arguments into the actions of its body, with the
//! arguments bound as values. Anything else is one action.
//!
//! The IR the front end writes evaluates nothing, so it carries no actions; [`add_actions`] gives
//! them to it, as `check.ts` gives them to the IR it writes.

use std::collections::{HashMap, HashSet};

use tla_ir::{
    Action, Bound, Builtin, Definition, DefinitionForm, Index, Ir, Name, Node, NodeId, NodeKind,
    Pattern, Resolution, Scope, ScopeBinding, TextId,
};

use crate::Unsupported;
use crate::eval::{Context, Evaluator};
use crate::print::format_value;
use crate::sets::as_tuple;
use crate::value::{Class, Value, elements};

/// One of TLC's actions: the expression it walks, with the values of the names the split bound,
/// and what a trace calls it.
struct SplitAction {
    expression: NodeId,
    place: Place,
    /// The operator the action is the body of, or none.
    name: Option<TextId>,
    /// The values of the operator's parameters, which the label prints.
    parameters: Vec<Value>,
}

/// Where an expression of the split is evaluated: its bindings for the evaluator, and the same
/// bindings as the IR's scopes, the existing ones and those the split adds.
#[derive(Clone)]
struct Place {
    context: Context,
    scope: Option<Index>,
}

/// The operator whose body the split is in, and the values bound to its parameters.
#[derive(Clone)]
struct Closure {
    name: TextId,
    parameters: Vec<Value>,
}

struct Splitter<'e, 'ir> {
    evaluator: &'e mut Evaluator<'ir>,
    /// The scopes the split binds, after the IR's own: each its parent, its name and what it
    /// binds.
    scopes: Vec<(Option<Index>, TextId, Added)>,
    /// The nodes the split adds, after the IR's own: the function constructions LET definitions
    /// of functions stand for, as `bindDefinitions` binds them.
    nodes: Vec<Node>,
}

/// What a scope the split adds binds: a value, or a binding of a LET definition.
enum Added {
    Value(Value),
    Binding(ScopeBinding),
}

/// The IR with TLC's actions, and the scopes, values and texts they need, where it has none:
/// `check.ts`'s `getTraceActions`. As there, a model whose next-state relation or the definitions
/// the configuration names may print, draw or set a register gets none, since finding them would
/// evaluate those, and so does one the split can't follow.
pub fn add_actions(ir: &Ir) -> Result<Ir, Unsupported> {
    let mut ir = ir.clone();
    // A spec without variables has no behaviors, and the IR's next-state relation stands for none.
    if !ir.model.actions.is_empty() || ir.model.is_labelled || ir.variables.is_empty() {
        return Ok(ir);
    }
    if ir.model.scope.is_some() {
        return Err(Unsupported(
            "TLC's actions of a next-state relation in an instance's scope".into(),
        ));
    }
    let (actions, scopes, nodes) = {
        let mut evaluator = Evaluator::new(&ir);
        if has_effect(&evaluator) {
            return Ok(ir);
        }
        // The actions read what TLC computed when it started, as the search does.
        if let Err(error) = evaluator.compute_startup() {
            return Err(Unsupported(format!(
                "TLC's actions of a model whose startup fails: {}",
                error.reason
            )));
        }
        let mut splitter = Splitter {
            evaluator: &mut evaluator,
            scopes: Vec::new(),
            nodes: Vec::new(),
        };
        let place = Place {
            context: Context::default(),
            scope: None,
        };
        let actions = splitter.split(ir.model.next, &place, None)?;
        let labels: Vec<String> = actions
            .iter()
            .map(|action| splitter.label(action))
            .collect();
        let actions: Vec<(NodeId, Option<Index>, String)> = actions
            .into_iter()
            .zip(labels)
            .map(|(action, label)| (action.expression, action.place.scope, label))
            .collect();
        (actions, splitter.scopes, splitter.nodes)
    };
    let mut writer = Writer::new(&mut ir);
    let scopes: Vec<Scope> = scopes
        .into_iter()
        .map(|(parent, name, bound)| {
            Ok(Scope {
                parent,
                name,
                binding: match bound {
                    Added::Value(value) => ScopeBinding::Value(Some(writer.value(&value)?)),
                    Added::Binding(binding) => binding,
                },
            })
        })
        .collect::<Result<_, Unsupported>>()?;
    let actions = actions
        .into_iter()
        .map(|(expression, scope, label)| Action {
            expression,
            scope,
            label: writer.text(&label),
        })
        .collect();
    let first = ir.nodes.arena.len() as NodeId;
    ir.nodes.top.extend(first..first + nodes.len() as NodeId);
    ir.nodes.arena.extend(nodes);
    ir.scopes.extend(scopes);
    ir.model.actions = actions;
    Ok(ir)
}

impl Splitter<'_, '_> {
    fn split(
        &mut self,
        expression: NodeId,
        place: &Place,
        closure: Option<&Closure>,
    ) -> Result<Vec<SplitAction>, Unsupported> {
        let whole = || SplitAction {
            expression,
            place: place.clone(),
            name: closure.map(|closure| closure.name),
            parameters: closure.map_or_else(Vec::new, |closure| closure.parameters.clone()),
        };
        let ir = self.evaluator.ir;
        match &ir.nodes.arena[expression as usize].kind {
            NodeKind::Reference(target) => return self.split(*target, place, closure),
            NodeKind::Let {
                instances,
                definitions,
                body,
            } => {
                let bound = self.bind_let(*instances, definitions, place)?;
                return self.split(*body, &bound, closure);
            }
            NodeKind::Label { body, .. } => return self.split(*body, place, closure),
            NodeKind::Or(operands) => {
                let mut actions = Vec::new();
                for &operand in operands {
                    actions.extend(self.split(operand, place, closure)?);
                }
                return Ok(actions);
            }
            NodeKind::Exists { bounds, body } => {
                let actions = self.split_exists(bounds, *body, place, closure)?;
                return Ok(actions.unwrap_or_else(|| vec![whole()]));
            }
            _ => {}
        }
        let (name, args): (&Name, &[NodeId]) = match &ir.nodes.arena[expression as usize].kind {
            NodeKind::Identifier(name) => (name, &[]),
            NodeKind::Apply { name, args } => (name, args),
            _ => return Ok(vec![whole()]),
        };
        if name.is_local {
            return Err(Unsupported(
                "TLC's actions through an operator bound locally".into(),
            ));
        }
        let Resolution::Definition(index) = name.resolution else {
            return Ok(vec![whole()]);
        };
        let node = ir.definitions[index as usize];
        let definition = self.evaluator.definition(node);
        // TLC names an action of an instance's operator by the instance (`instanceActions`),
        // which the IR doesn't carry yet.
        if self.evaluator.name(name.text).contains('!')
            || definition.flags & Definition::SUBSTITUTED != 0
        {
            return Err(Unsupported(
                "TLC's actions through an instance's operator".into(),
            ));
        }
        let DefinitionForm::Operator(params) = &definition.form else {
            return Ok(vec![whole()]);
        };
        if params.len() != args.len() {
            return Ok(vec![whole()]);
        }
        let call = SplitAction {
            expression,
            place: place.clone(),
            name: Some(definition.name),
            parameters: Vec::new(),
        };
        if self.is_constant_definition(definition)
            || args
                .iter()
                .any(|&arg| self.evaluator.can_read(arg, &place.context))
        {
            return Ok(vec![call]);
        }
        // The arguments are bound as values, over the operator's own scope: none, for a
        // definition of the module.
        let mut values = Vec::with_capacity(args.len());
        for &arg in args {
            match self.evaluator.evaluate(arg, &place.context) {
                Ok(value) => values.push(value),
                Err(_) => return Ok(vec![call]),
            }
        }
        let mut bound = Place {
            context: Context::default(),
            scope: None,
        };
        for (param, value) in params.iter().zip(&values) {
            bound = self.bind(&bound, param.name, value.clone());
        }
        let closure = Closure {
            name: definition.name,
            parameters: values,
        };
        let body = definition.body;
        self.split(body, &bound, Some(&closure))
    }

    // The actions of `\E` over constant sets: one set of actions for each binding, in TLC's order,
    // or none where a set can't be evaluated or no binding gives an action.
    fn split_exists(
        &mut self,
        bounds: &[Bound],
        body: NodeId,
        place: &Place,
        closure: Option<&Closure>,
    ) -> Result<Option<Vec<SplitAction>>, Unsupported> {
        let mut sets = Vec::with_capacity(bounds.len());
        for bound in bounds {
            let Ok(set) = self
                .evaluator
                .evaluate(bound.set, &place.context)
                .and_then(|set| elements(&set))
            else {
                return Ok(None);
            };
            sets.push(set);
        }
        if sets.iter().any(|set| set.is_empty()) {
            return Ok(None);
        }
        let mut actions = Vec::new();
        // The first bound varies fastest, as TLC's ContextEnumerator gives the bindings.
        let mut positions = vec![0; bounds.len()];
        loop {
            // TLC binds the last bound first.
            let mut inner = place.clone();
            for (level, bound) in bounds.iter().enumerate().rev() {
                let element = &sets[level][positions[level]];
                match &bound.pattern {
                    Pattern::Name(name) => inner = self.bind(&inner, *name, element.clone()),
                    Pattern::Tuple(names) => {
                        let Some(tuple) =
                            as_tuple(element).filter(|tuple| tuple.len() == names.len())
                        else {
                            return Ok(None);
                        };
                        for (&name, value) in names.iter().zip(tuple) {
                            inner = self.bind(&inner, name, value.clone());
                        }
                    }
                }
            }
            actions.extend(self.split(body, &inner, closure)?);
            let mut level = 0;
            while level < positions.len() {
                positions[level] += 1;
                if positions[level] < sets[level].len() {
                    break;
                }
                positions[level] = 0;
                level += 1;
            }
            if level == positions.len() {
                break;
            }
        }
        Ok((!actions.is_empty()).then_some(actions))
    }

    // A place with `name` bound to `value`, for the evaluator and as a scope of the IR.
    fn bind(&mut self, place: &Place, name: TextId, value: Value) -> Place {
        let index = (self.evaluator.ir.scopes.len() + self.scopes.len()) as Index;
        self.scopes
            .push((place.scope, name, Added::Value(value.clone())));
        Place {
            context: place.context.bind_value(name, value),
            scope: Some(index),
        }
    }

    // A place with a LET's definitions bound as `bindDefinitions` binds them, each seeing itself
    // and those before it: a function as the function construction it stands for, an operator
    // with parameters as a closure, and anything else as an expression evaluated where used.
    fn bind_let(
        &mut self,
        instances: u32,
        definitions: &[NodeId],
        place: &Place,
    ) -> Result<Place, Unsupported> {
        let context = self
            .evaluator
            .bind_let(instances, definitions, &place.context)
            .map_err(|error| {
                Unsupported(format!("TLC's actions through a LET: {}", error.reason))
            })?;
        let ir = self.evaluator.ir;
        let mut scope = place.scope;
        for &node in definitions {
            let index = (ir.scopes.len() + self.scopes.len()) as Index;
            let definition = self.evaluator.definition(node);
            let binding = match &definition.form {
                DefinitionForm::Function(bounds) => {
                    let written = &ir.nodes.arena[node as usize];
                    let construction = (ir.nodes.arena.len() + self.nodes.len()) as NodeId;
                    self.nodes.push(Node {
                        line: written.line,
                        column: written.column,
                        range: written.range,
                        kind: NodeKind::FunctionConstruction {
                            is_recursive: true,
                            bounds: bounds.clone(),
                            body: definition.body,
                        },
                    });
                    ScopeBinding::Thunk {
                        expression: construction,
                        scope: Some(index),
                    }
                }
                DefinitionForm::Operator(params) if !params.is_empty() => ScopeBinding::Closure {
                    name: definition.name,
                    params: params.clone(),
                    body: definition.body,
                    scope: Some(index),
                },
                DefinitionForm::Operator(_) => ScopeBinding::Thunk {
                    expression: definition.body,
                    scope: Some(index),
                },
            };
            self.scopes
                .push((scope, definition.name, Added::Binding(binding)));
            scope = Some(index);
        }
        Ok(Place { context, scope })
    }

    // `isConstantDefinition`: a definition of constant level without parameters whose body isn't a
    // literal and evaluates, which TLC computed when it started and takes as one action.
    fn is_constant_definition(&mut self, definition: &Definition) -> bool {
        let DefinitionForm::Operator(params) = &definition.form else {
            return false;
        };
        params.is_empty()
            && !matches!(
                self.evaluator.ir.nodes.arena[definition.body as usize].kind,
                NodeKind::Number(_) | NodeKind::String(_)
            )
            && !self
                .evaluator
                .can_read(definition.body, &Context::default())
            && self
                .evaluator
                .evaluate(definition.body, &Context::default())
                .is_ok()
    }

    // `getActionLabel`: the action's name, the values of its parameters but in TLC 1.7.4, and its
    // location.
    fn label(&mut self, action: &SplitAction) -> String {
        // TLC names an action of no operator `Action`.
        let name = action
            .name
            .map_or("Action", |name| self.evaluator.name(name));
        let parameters = if action.parameters.is_empty() || self.evaluator.is_174() {
            String::new()
        } else {
            let values: Vec<String> = action.parameters.iter().map(format_value).collect();
            format!("({})", values.join(","))
        };
        format!(
            "{name}{parameters} {}",
            self.evaluator.describe_range(action.expression)
        )
    }
}

// Whether evaluating the next-state relation, or a definition the configuration names, can change
// what a run does (`hasEffect`): draw a random value, set or read a TLC register, assert or print,
// itself or through a definition it names, but one TLC evaluates once, as it does a constant
// definition without parameters.
fn has_effect(evaluator: &Evaluator<'_>) -> bool {
    let ir = evaluator.ir;
    let model = &ir.model;
    let definitions = model
        .invariants
        .iter()
        .map(|invariant| &invariant.root)
        .filter_map(|name| name.definition)
        .map(|index| ir.definitions[index as usize]);
    let roots = [model.init, model.next]
        .into_iter()
        .chain(definitions)
        .chain(
            model
                .property_invariants
                .iter()
                .map(|invariant| invariant.root),
        )
        .chain(
            model
                .action_properties
                .iter()
                .flat_map(|property| [property.action, property.subscript]),
        )
        .chain(model.initial_predicates.iter().copied())
        .chain(model.atoms.iter().map(|atom| atom.expression));
    let mut seen = HashSet::new();
    roots
        .into_iter()
        .any(|root| may_have_effect(evaluator, root, &mut seen))
}

fn may_have_effect(evaluator: &Evaluator<'_>, node: NodeId, seen: &mut HashSet<NodeId>) -> bool {
    if !seen.insert(node) {
        return false;
    }
    let ir = evaluator.ir;
    let kind = &ir.nodes.arena[node as usize].kind;
    let named = match kind {
        NodeKind::Reference(target) => return may_have_effect(evaluator, *target, seen),
        NodeKind::Identifier(name) | NodeKind::Apply { name, .. } if !name.is_local => {
            match name.resolution {
                Resolution::Builtin(index) => {
                    let builtin = &ir.builtins[index as usize];
                    builtin.flags & Builtin::STATE_LEVEL != 0
                        || matches!(
                            &*ir.texts[builtin.name as usize],
                            "Print"
                                | "PrintT"
                                | "Assert"
                                | "JavaTime"
                                | "RandomElement"
                                | "TLCGet"
                                | "TLCSet"
                        )
                }
                Resolution::Definition(index) => {
                    let node = ir.definitions[index as usize];
                    let definition = evaluator.definition(node);
                    let is_evaluated_once = matches!(&definition.form, DefinitionForm::Operator(params) if params.is_empty())
                        && !evaluator.can_read(definition.body, &Context::default());
                    !is_evaluated_once && may_have_effect(evaluator, node, seen)
                }
                _ => false,
            }
        }
        _ => false,
    };
    named
        || kind
            .children()
            .into_iter()
            .any(|child| may_have_effect(evaluator, child, seen))
}

/// Adds the texts and values the actions need to the IR.
struct Writer<'i> {
    ir: &'i mut Ir,
    texts: HashMap<String, TextId>,
    strings: HashMap<TextId, u32>,
}

impl<'i> Writer<'i> {
    fn new(ir: &'i mut Ir) -> Writer<'i> {
        let texts = ir
            .texts
            .iter()
            .enumerate()
            .map(|(index, text)| (text.to_string(), index as TextId))
            .collect();
        let strings = ir
            .values
            .strings
            .iter()
            .enumerate()
            .map(|(index, &text)| (text, index as u32))
            .collect();
        Writer { ir, texts, strings }
    }

    fn text(&mut self, text: &str) -> TextId {
        if let Some(&id) = self.texts.get(text) {
            return id;
        }
        let id = self.ir.texts.len() as TextId;
        self.ir.texts.push(text.into());
        self.texts.insert(text.to_owned(), id);
        id
    }

    fn string(&mut self, units: &[u16]) -> u32 {
        let text = self.text(&String::from_utf16_lossy(units));
        if let Some(&index) = self.strings.get(&text) {
            return index;
        }
        let index = self.ir.values.strings.len() as u32;
        self.ir.values.strings.push(text);
        self.strings.insert(text, index);
        index
    }

    // A value's place among the IR's values, in `transfer.ts`'s encoding.
    fn value(&mut self, value: &Value) -> Result<u32, Unsupported> {
        let encoded = self.encode(value)?;
        self.ir.values.list.push(encoded);
        Ok(self.ir.values.list.len() as u32 - 1)
    }

    fn encode(&mut self, value: &Value) -> Result<tla_ir::Value, Unsupported> {
        let class = |class: Class| match class {
            Class::Plain => 0,
            Class::Lambda => 1,
            Class::Tuple => 2,
            Class::Record => 3,
        };
        Ok(match value {
            Value::Bool(value) => tla_ir::Value::Bool(*value),
            Value::Int(value) => tla_ir::Value::Int(*value),
            Value::Str(text) => tla_ir::Value::String(self.string(&text.units)),
            Value::Model(text) => tla_ir::Value::ModelValue(self.string(&text.units)),
            Value::Set(_) | Value::Interval(..) => {
                let elements = elements(value).map_err(|error| Unsupported(error.reason))?;
                tla_ir::Value::Set(
                    elements
                        .iter()
                        .map(|element| self.encode(element))
                        .collect::<Result<_, _>>()?,
                )
            }
            Value::Function(function) => {
                let range = function
                    .range
                    .iter()
                    .map(|element| self.encode(element))
                    .collect::<Result<_, _>>()?;
                match function.interval {
                    Some((low, _)) => tla_ir::Value::IntervalFunction {
                        class: class(function.class.get()),
                        low,
                        range,
                    },
                    None => tla_ir::Value::Function {
                        class: class(function.class.get()),
                        domain: function
                            .domain
                            .iter()
                            .map(|element| self.encode(element))
                            .collect::<Result<_, _>>()?,
                        range,
                    },
                }
            }
            Value::Lazy(_) => {
                return Err(Unsupported(
                    "an action's parameter TLC keeps as a lazy set".into(),
                ));
            }
        })
    }
}
