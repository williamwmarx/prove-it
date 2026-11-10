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
    Action, AtomKind, Bound, Builtin, Definition, DefinitionForm, EnabledActions, Index,
    InstanceAction, Ir, Name, Node, NodeId, NodeKind, Pattern, Resolution, Scope, ScopeBinding,
    SourceRange, TextId,
};

use crate::Unsupported;
use crate::eval::{Context, Evaluator};
use crate::print::format_value;
use crate::rebuild::run;
use crate::sets::as_tuple;
use crate::value::{Class, Evaluated, Value, elements, is_same, set_of};

/// One of TLC's actions: the expression it walks, with the values of the names the split bound,
/// and what a trace calls it.
struct SplitAction {
    expression: NodeId,
    place: Place,
    /// The operator the action is the body of, or none: TLC's `UnnamedAction`.
    name: Option<TextId>,
    location: Located,
    /// The definition TLC splits the action from (`Action.getOpDef`), by index.
    definition: Option<Index>,
    /// The values of the operator's parameters, which the label prints.
    parameters: Vec<Value>,
}

/// An action as the IR holds it, before its texts are added.
struct Labelled {
    expression: NodeId,
    scope: Option<Index>,
    label: String,
    name: String,
    location: Option<SourceRange>,
    definition: Option<Index>,
}

/// Where TLC says an action is written: at an expression, or at an INSTANCE it comes through.
#[derive(Clone, Copy)]
enum Located {
    Node(NodeId),
    Instance(Option<SourceRange>),
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
    /// The module's definition, or none for one a LET binds.
    definition: Option<Index>,
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

/// The IR with TLC's actions, and the scopes, values and texts they need, where it has none, as
/// `check.ts`'s `getTraceActions` gives them. Where the split would evaluate an expression that may
/// print, draw or set a register, or the split can't follow TLC, there are none. `check.ts` gives
/// none to a model whose next-state relation has an effect anywhere, which the interpreter would
/// evaluate; this split evaluates only the constants TLC evaluates, so it labels those too.
///
/// It also gives each ENABLED atom the actions it splits into, which the search's steps then
/// answer it from, and labels the steps where some atom is made of only some of them.
pub fn add_actions(ir: &Ir) -> Result<Ir, Unsupported> {
    let mut ir = ir.clone();
    // A spec without variables has no behaviors, and the IR's next-state relation stands for none.
    if !ir.model.actions.is_empty() || ir.model.is_labelled || ir.variables.is_empty() {
        return Ok(ir);
    }
    let (actions, enabled, scopes, nodes) = {
        let mut evaluator = Evaluator::new(&ir);
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
        let actions = splitter.split_next()?;
        let enabled: Vec<EnabledActions> = ir
            .model
            .atoms
            .iter()
            .map(|atom| splitter.find_enabled_actions(atom, &actions))
            .collect();
        let actions: Vec<Labelled> = actions
            .iter()
            .map(|action| {
                let name = action
                    .name
                    .map_or(UNNAMED_ACTION, |name| splitter.evaluator.name(name));
                let location = match action.location {
                    Located::Node(node) => {
                        ir.nodes.arena[splitter.evaluator.resolved(node) as usize].range
                    }
                    Located::Instance(range) => range,
                };
                Labelled {
                    expression: action.expression,
                    scope: action.place.scope,
                    label: splitter.label(action),
                    name: name.to_owned(),
                    location,
                    definition: action.definition,
                }
            })
            .collect();
        (actions, enabled, splitter.scopes, splitter.nodes)
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
        .map(|action| Action {
            expression: action.expression,
            scope: action.scope,
            label: writer.text(&action.label),
            name: writer.text(&action.name),
            location: action.location,
            definition: action.definition,
        })
        .collect();
    let first = ir.nodes.arena.len() as NodeId;
    ir.nodes.top.extend(first..first + nodes.len() as NodeId);
    ir.nodes.arena.extend(nodes);
    ir.scopes.extend(scopes);
    ir.model.actions = actions;
    for (atom, actions) in ir.model.atoms.iter_mut().zip(enabled) {
        if let AtomKind::Enabled { .. } = atom.kind {
            ir.model.is_labelled |= matches!(actions, EnabledActions::Some(_));
            atom.kind = AtomKind::Enabled { actions };
        }
    }
    Ok(ir)
}

/// A part of the specification as TLC processed it, which TLCGet("spec") records: its name and
/// where it is written, or none for TLC's built-in range.
pub struct Described {
    pub name: String,
    pub range: Option<SourceRange>,
}

/// What TLCGet("spec") records of a specification besides its actions, which [`add_spec`]
/// splits, as `getSpecificationValue` in `spec-description.ts` describes it.
#[derive(Default)]
pub struct SpecDescription {
    pub inits: Vec<Described>,
    pub temporals: Vec<Described>,
    pub invariants: Vec<Described>,
    pub implied_inits: Vec<Described>,
    pub implied_actions: Vec<Described>,
    pub implied_temporals: Vec<Described>,
    pub variables: Vec<Described>,
    pub action_constraints: Vec<Described>,
    pub constraints: Vec<Described>,
}

/// The IR with TLCGet("spec"), the record of the specification as TLC processed it
/// (`TLCGetSet.TLCGetStringValue`), of the description and TLC's actions, split as
/// [`add_actions`] splits them.
pub fn add_spec(ir: &Ir, description: &SpecDescription) -> Result<Ir, Unsupported> {
    let mut ir = ir.clone();
    let record = {
        let mut evaluator = Evaluator::new(&ir);
        if let Err(error) = evaluator.compute_startup() {
            return Err(Unsupported(format!(
                "TLCGet(\"spec\") of a model whose startup fails: {}",
                error.reason
            )));
        }
        let mut splitter = Splitter {
            evaluator: &mut evaluator,
            scopes: Vec::new(),
            nodes: Vec::new(),
        };
        let actions = splitter.split_next()?;
        let actions = actions
            .iter()
            .map(|action| splitter.action_record(action))
            .collect::<Result<Vec<_>, _>>()?;
        let evaluator = &*splitter.evaluator;
        let field = |name: &str| evaluator.text_of(name.encode_utf16().collect());
        let fields = [
            ("inits", &description.inits),
            ("temporals", &description.temporals),
            ("invariants", &description.invariants),
            ("impliedinits", &description.implied_inits),
            ("impliedactions", &description.implied_actions),
            ("impliedtemporals", &description.implied_temporals),
            ("variables", &description.variables),
            ("actionconstraints", &description.action_constraints),
            ("constraints", &description.constraints),
        ];
        let mut record = vec![(field("actions"), run(set_of(actions))?)];
        for (name, described) in fields {
            let entries = described
                .iter()
                .map(|described| {
                    let name = text_value(evaluator, &described.name);
                    let location = location_record(evaluator, described.range)?;
                    run(Value::record(vec![
                        (field("name"), name),
                        (field("location"), location),
                    ]))
                })
                .collect::<Result<Vec<_>, Unsupported>>()?;
            record.push((field(name), run(set_of(entries))?));
        }
        run(Value::record(record))?
    };
    let mut writer = Writer::new(&mut ir);
    let value = writer.value(&record)?;
    ir.model.tlc_spec = Some(value);
    Ok(ir)
}

fn text_value(evaluator: &Evaluator<'_>, text: &str) -> Value {
    Value::Str(evaluator.text_of(text.encode_utf16().collect()))
}

// TLC's record of where something is written (`RecordValue(Location)`), its built-in range for
// what has none.
fn location_record(
    evaluator: &Evaluator<'_>,
    range: Option<SourceRange>,
) -> Result<Value, Unsupported> {
    let ir = evaluator.ir;
    let (module, start_line, start_column, end_line, end_column) = match range {
        Some(range) => (
            &*ir.texts[range.module as usize],
            range.start_line,
            range.start_column,
            range.end_line,
            range.end_column,
        ),
        None => ("--TLA+ BUILTINS--", 0, 0, 0, 0),
    };
    let field = |name: &str| evaluator.text_of(name.encode_utf16().collect());
    run(Value::record(vec![
        (field("beginLine"), Value::Int(start_line)),
        (field("beginColumn"), Value::Int(start_column)),
        (field("endLine"), Value::Int(end_line)),
        (field("endColumn"), Value::Int(end_column)),
        (field("module"), text_value(evaluator, module)),
    ]))
}

impl Splitter<'_, '_> {
    // TLC's record of an action (`RecordValue(Action)`): its name and location, and the values of
    // its operator's parameters, by name and in order.
    fn action_record(&mut self, action: &SplitAction) -> Result<Value, Unsupported> {
        let ir = self.evaluator.ir;
        let name = action
            .name
            .map_or(UNNAMED_ACTION, |name| self.evaluator.name(name))
            .to_owned();
        let range = match action.location {
            Located::Node(node) => ir.nodes.arena[self.evaluator.resolved(node) as usize].range,
            Located::Instance(range) => range,
        };
        let evaluator = &*self.evaluator;
        let field = |name: &str| evaluator.text_of(name.encode_utf16().collect());
        let mut fields = vec![
            (field("name"), text_value(evaluator, &name)),
            (field("location"), location_record(evaluator, range)?),
        ];
        if !action.parameters.is_empty() {
            let params = action
                .definition
                .map(|index| &evaluator.definition(ir.definitions[index as usize]).form);
            let Some(DefinitionForm::Operator(params)) = params else {
                return Err(Unsupported("an action's parameters of no operator".into()));
            };
            // An INSTANCE's copy of a parameter keeps its name.
            let names: Vec<Value> = params
                .iter()
                .map(|param| {
                    let name = evaluator.name(param.name);
                    let name = name.rsplit_once('#').filter(|(_, suffix)| {
                        !suffix.is_empty() && suffix.chars().all(|digit| digit.is_ascii_digit())
                    });
                    text_value(
                        evaluator,
                        name.map_or(evaluator.name(param.name), |(name, _)| name),
                    )
                })
                .collect();
            let context = names
                .iter()
                .zip(&action.parameters)
                .map(|(name, value)| match name {
                    Value::Str(text) => (text.clone(), value.clone()),
                    _ => unreachable!("a parameter's name"),
                })
                .collect();
            fields.push((field("context"), run(Value::record(context))?));
            fields.push((field("parameters"), Value::tuple(names)));
        }
        run(Value::record(fields))
    }

    // The next-state relation split into TLC's actions. One that comes through an INSTANCE with
    // substitutions is one action, named at the INSTANCE.
    fn split_next(&mut self) -> Result<Vec<SplitAction>, Unsupported> {
        let ir = self.evaluator.ir;
        let Some((next, scope)) = next_state_relation(ir) else {
            return Err(Unsupported(
                "TLC's actions of a model without a next-state relation".into(),
            ));
        };
        let context = self.evaluator.scope_context(scope).map_err(|error| {
            Unsupported(format!(
                "TLC's actions of a next-state relation in a scope: {}",
                error.reason
            ))
        })?;
        let place = Place { context, scope };
        match ir.model.next_substitution {
            Some(range) => Ok(vec![SplitAction {
                expression: next,
                place,
                name: None,
                location: Located::Instance(Some(range)),
                definition: None,
                parameters: Vec::new(),
            }]),
            None => self.split(next, &place, None),
        }
    }

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
            location: Located::Node(expression),
            definition: closure.and_then(|closure| closure.definition),
            parameters: closure.map_or_else(Vec::new, |closure| closure.parameters.clone()),
        };
        let ir = self.evaluator.ir;
        match &ir.nodes.arena[expression as usize].kind {
            NodeKind::Reference(target) => return self.split(*target, place, closure),
            NodeKind::Let {
                definitions, body, ..
            } => {
                let bound = self.bind_let(definitions, place)?;
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
            // An operator a LET defines without parameters, such as one an INSTANCE in the LET
            // copies, splits into its body, named as the LET names it.
            let Some(body) = self
                .get_let_operator(place.scope, name.text)
                .filter(|_| args.is_empty())
            else {
                return Err(Unsupported(
                    "TLC's actions through an operator bound locally".into(),
                ));
            };
            let closure = Closure {
                name: name.text,
                definition: None,
                parameters: Vec::new(),
            };
            return self.split(body, place, Some(&closure));
        }
        let Resolution::Definition(index) = name.resolution else {
            return Ok(vec![whole()]);
        };
        let node = ir.definitions[index as usize];
        let definition = self.evaluator.definition(node);
        let DefinitionForm::Operator(params) = &definition.form else {
            return Ok(vec![whole()]);
        };
        if let Some(instance) = ir
            .model
            .instance_actions
            .iter()
            .find(|instance| instance.definition == index)
        {
            return self.split_instance(expression, args, place, instance);
        }
        if params.len() != args.len() {
            return Ok(vec![whole()]);
        }
        // TLC names an action after the operator it applies, as SANY names it in the spec.
        let called = ir
            .model
            .instance_names
            .iter()
            .find(|&&(named, _)| named == index)
            .map_or(definition.name, |&(_, name)| name);
        let call = SplitAction {
            expression,
            place: place.clone(),
            name: Some(called),
            location: Located::Node(expression),
            definition: Some(index),
            parameters: Vec::new(),
        };
        if self.is_constant_definition(definition)?
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
            match self.evaluate(arg, &place.context)? {
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
            name: called,
            definition: Some(index),
            parameters: values,
        };
        let body = definition.body;
        self.split(body, &bound, Some(&closure))
    }

    // `getInstanceActions`: an operator an INSTANCE with substitutions copies is one action, named
    // as the instance exports it, at the INSTANCE, and with the values of constant arguments; or
    // at the application, where an argument isn't constant.
    fn split_instance(
        &mut self,
        expression: NodeId,
        args: &[NodeId],
        place: &Place,
        instance: &InstanceAction,
    ) -> Result<Vec<SplitAction>, Unsupported> {
        let at_instance = |parameters| SplitAction {
            expression,
            place: place.clone(),
            name: Some(instance.name),
            location: Located::Instance(instance.location),
            definition: Some(instance.definition),
            parameters,
        };
        let call = SplitAction {
            location: Located::Node(expression),
            ..at_instance(Vec::new())
        };
        if args
            .iter()
            .any(|&arg| self.evaluator.can_read(arg, &place.context))
        {
            return Ok(vec![call]);
        }
        let mut values = Vec::with_capacity(args.len());
        for &arg in args {
            match self.evaluate(arg, &place.context)? {
                Ok(value) => values.push(value),
                Err(_) => return Ok(vec![call]),
            }
        }
        Ok(vec![at_instance(values)])
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
                .evaluate(bound.set, &place.context)?
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

    // `findActionPositions`: the positions among TLC's actions of the actions an ENABLED <<A>>_v
    // atom's A splits into, each the same expression with the same bindings as one of them and in
    // TLC's order, or unknown. ENABLED is then true of a state where a step the search took through
    // one of them changes v, which holds only where the search keeps every step those actions
    // take: TLC's ENABLED ignores a CONSTRAINT or ACTION_CONSTRAINT, which drops steps
    // (`ModelChecker.java`'s `isInModel` and `isInActions`), and a VIEW or SYMMETRY leaves the
    // step at a state the search saw before, not the one A takes it to. Where A or the next-state
    // relation may have an effect, such as printing, TLC shows it as it runs A, so A runs.
    fn find_enabled_actions(
        &mut self,
        atom: &tla_ir::Atom,
        actions: &[SplitAction],
    ) -> EnabledActions {
        let ir = self.evaluator.ir;
        let model = &ir.model;
        let NodeKind::AngleAction { action, .. } =
            &ir.nodes.arena[self.evaluator.resolved(atom.expression) as usize].kind
        else {
            return EnabledActions::Unknown;
        };
        let is_kept = model.constraints.is_empty()
            && model.action_constraints.is_empty()
            && model.view.is_none()
            && model.startup.symmetry.is_none()
            && model
                .next
                .is_none_or(|next| !may_have_effect(self.evaluator, next, &mut HashSet::new()))
            && !may_have_effect(self.evaluator, atom.expression, &mut HashSet::new());
        if !is_kept {
            return EnabledActions::Unknown;
        }
        let Ok(context) = self.evaluator.scope_context(atom.scope) else {
            return EnabledActions::Unknown;
        };
        let place = Place {
            context,
            scope: atom.scope,
        };
        let Some(splits) = self
            .split(*action, &place, None)
            .ok()
            .filter(|splits| !splits.is_empty())
        else {
            return EnabledActions::Unknown;
        };
        let mut positions: Vec<i32> = Vec::with_capacity(splits.len());
        for split in &splits {
            let start = positions.last().map_or(0, |&last| last as usize + 1);
            let found = (start..actions.len()).find(|&position| {
                actions[position].expression == split.expression
                    && self.is_same_scope(actions[position].place.scope, split.place.scope)
            });
            let Some(position) = found else {
                return EnabledActions::Unknown;
            };
            positions.push(position as i32);
        }
        if positions.len() == actions.len() {
            EnabledActions::All
        } else {
            EnabledActions::Some(positions)
        }
    }

    // `isSameScope`: whether two scopes bind the same names to the same values. A scope of the IR,
    // or one binding a LET's definitions, is the same only as itself.
    fn is_same_scope(&self, scope: Option<Index>, other: Option<Index>) -> bool {
        if scope == other {
            return true;
        }
        let own = self.evaluator.ir.scopes.len();
        let added = |scope: Option<Index>| {
            scope
                .and_then(|index| (index as usize).checked_sub(own))
                .map(|index| &self.scopes[index])
        };
        match (added(scope), added(other)) {
            (
                Some((parent, name, Added::Value(value))),
                Some((other_parent, other_name, Added::Value(other_value))),
            ) => {
                name == other_name
                    && is_same(value, other_value)
                    && self.is_same_scope(*parent, *other_parent)
            }
            _ => false,
        }
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
    fn bind_let(&mut self, definitions: &[NodeId], place: &Place) -> Result<Place, Unsupported> {
        let context = self
            .evaluator
            .bind_let(definitions, &place.context)
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

    /// The body of the operator without parameters named `name` that a LET the split bound
    /// defines, looking out from `scope`.
    fn get_let_operator(&self, scope: Option<Index>, name: TextId) -> Option<NodeId> {
        let own = self.evaluator.ir.scopes.len();
        let mut scope = scope;
        while let Some(index) = scope.and_then(|index| (index as usize).checked_sub(own)) {
            let (parent, bound, added) = &self.scopes[index];
            if *bound == name {
                return match added {
                    Added::Binding(ScopeBinding::Thunk { expression, .. }) => Some(*expression),
                    _ => None,
                };
            }
            scope = *parent;
        }
        None
    }

    // `isConstantDefinition`: a definition of constant level without parameters whose body isn't a
    // literal and evaluates, which TLC computed when it started and takes as one action.
    fn is_constant_definition(&mut self, definition: &Definition) -> Result<bool, Unsupported> {
        let DefinitionForm::Operator(params) = &definition.form else {
            return Ok(false);
        };
        Ok(params.is_empty()
            && !matches!(
                self.evaluator.ir.nodes.arena[definition.body as usize].kind,
                NodeKind::Number(_) | NodeKind::String(_)
            )
            && !self
                .evaluator
                .can_read(definition.body, &Context::default())
            && self.evaluate(definition.body, &Context::default())?.is_ok())
    }

    // An expression the split evaluates, as TLC does when it starts. One that may print, draw or
    // set a register would change what TLC prints and draws then, which the split doesn't follow.
    fn evaluate(
        &mut self,
        node: NodeId,
        context: &Context,
    ) -> Result<Evaluated<Value>, Unsupported> {
        if may_have_effect(self.evaluator, node, &mut HashSet::new()) {
            return Err(Unsupported(
                "TLC's actions whose split prints, draws or sets a register".into(),
            ));
        }
        Ok(self.evaluator.evaluate(node, context))
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
        let location = match action.location {
            Located::Node(node) => self.evaluator.describe_range(node),
            Located::Instance(range) => describe_instance(self.evaluator, range),
        };
        format!("{name}{parameters} {location}")
    }
}

const UNNAMED_ACTION: &str = "UnnamedAction";

// Where an INSTANCE is written, as TLC's messages say it, or TLC's built-in range for one the IR
// has none of.
fn describe_instance(evaluator: &Evaluator<'_>, range: Option<SourceRange>) -> String {
    match range {
        Some(range) => format!(
            "line {}, col {} to line {}, col {} of module {}",
            range.start_line,
            range.start_column,
            range.end_line,
            range.end_column,
            evaluator.name(range.module)
        ),
        None => "line 0, col 0 to line 0, col 0 of module --TLA+ BUILTINS--".to_owned(),
    }
}

// The next-state relation and the scope it is read in: where the IR names it by a binding of the
// specification's scope, as `getSpecification` does for one read in an instance's scope, the
// expression bound.
fn next_state_relation(ir: &Ir) -> Option<(NodeId, Option<Index>)> {
    let model = &ir.model;
    let next = model.next?;
    let NodeKind::Identifier(name) = &ir.nodes.arena[next as usize].kind else {
        return Some((next, model.scope));
    };
    let mut scope = model.scope;
    while let Some(index) = scope.filter(|_| name.is_local) {
        let entry = &ir.scopes[index as usize];
        if entry.name == name.text {
            return Some(match entry.binding {
                ScopeBinding::Thunk { expression, scope } => (expression, scope),
                _ => (next, model.scope),
            });
        }
        scope = entry.parent;
    }
    Some((next, model.scope))
}

// Whether evaluating an expression can change what a run does (`hasEffect`): draw a random value,
// set or read a TLC register, assert or print, itself or through a definition it names, but one
// TLC evaluates once, as it does a constant definition without parameters.
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
            Value::Unsorted(_) => return Err(Unsupported("a set TLC leaves unnormalized".into())),
            Value::Lambda(_) => {
                return Err(Unsupported(
                    "a function over a set TLC doesn't enumerate".into(),
                ));
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
