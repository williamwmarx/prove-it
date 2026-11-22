//! The expression kinds of `compileNode`, each as `compile.ts` compiles it.

use std::collections::HashSet;
use std::sync::Arc;
use std::sync::atomic::{AtomicU32, Ordering};

use tla_ir::{Bound, NodeId, NodeKind, PathStep, Pattern, TextId, Update};
use tla_values::store::{
    EMPTY_SET, EMPTY_TUPLE, FALSE, KIND_INT, KIND_LAZY_FUNCTION, KIND_SET, KIND_STRING, KIND_TUPLE,
    Outcome, TRUE, is_function_kind,
};
use tla_values::{Bail, Id, check_set_insertion};

use super::builtins::{self, SimulationRun};
use super::lazy::{self, Lazy, Reference};
use super::lazy_function::{self, LambdaDefinition, is_lazy_domain};
use super::predicate::{Predicate, Reject, Test};
use super::{
    Binding, Compiled, Compiler, Compiling, Context, Filter, Shape, bind, bool_id,
    call_recursive_element, call_recursive_function, combine_references, constant, eval, leaf,
    lookup, member, predicate_node, reference_of, unsupported,
};
use crate::footprint::Footprint;
use crate::machine::{Eval, Machine, Printed, RuntimeWarning, UNASSIGNED};

/// A bound's names, at fresh slots: one name, or a tuple pattern's.
pub(crate) struct Binder {
    pub context: Context,
    pub slots: Vec<u32>,
    pub tuple: bool,
}

/// Binds a bound's names to an element as TLC's `ContextEnumerator` and set filter do: a tuple
/// pattern only to a `TupleValue`, which a tuple TLC built as a function isn't.
pub(crate) fn assign_bound(
    machine: &mut Machine<'_>,
    slots: &[u32],
    tuple: bool,
    element: Id,
) -> Outcome<()> {
    if tuple && machine.store.is_built_as_function(element) {
        return Err(Bail("a tuple pattern with an ambiguous physical class"));
    }
    assign_converted(machine, slots, tuple, element)
}

/// Binds a bound's names as `Tool`'s OPCODE_sso does filtering a Reducible set: a tuple
/// pattern's names to the elements of the TupleValue at their indices, ignoring those past them.
pub(crate) fn assign_reduced(
    machine: &mut Machine<'_>,
    slots: &[u32],
    tuple: bool,
    element: Id,
) -> Outcome<()> {
    if tuple
        && machine.store.kind_of(element) == KIND_TUPLE
        && machine.store.size_of(element) as usize > slots.len()
        && !machine.store.is_built_as_function(element)
    {
        for (index, &slot) in slots.iter().enumerate() {
            machine.locals[slot as usize] = machine.store.get_range_value(element, index as u32);
        }
        return Ok(());
    }
    assign_bound(machine, slots, tuple, element)
}

/// Binds a bound's names to an element as TLC's CHOOSE, a set filter's membership and a
/// function's application do, which take a function over 1..n as a tuple (`toTuple`).
pub(crate) fn assign_converted(
    machine: &mut Machine<'_>,
    slots: &[u32],
    tuple: bool,
    element: Id,
) -> Outcome<()> {
    if !tuple {
        machine.locals[slots[0] as usize] = element;
        return Ok(());
    }
    if machine.store.kind_of(element) != KIND_TUPLE
        || machine.store.size_of(element) as usize != slots.len()
    {
        return Err(Bail("a tuple pattern that doesn't match"));
    }
    for (index, &slot) in slots.iter().enumerate() {
        machine.locals[slot as usize] = machine.store.get_range_value(element, index as u32);
    }
    Ok(())
}

// Evaluates each of the evaluators onto the stack, which holds them from `at`, or pops what it
// pushed and fails.
pub(crate) fn push_all(machine: &mut Machine<'_>, evaluators: &[Eval]) -> Outcome<usize> {
    let at = machine.stack.len();
    for evaluate in evaluators {
        match evaluate(machine) {
            Ok(value) => machine.stack.push(value),
            Err(bail) => {
                machine.stack.truncate(at);
                return Err(bail);
            }
        }
    }
    Ok(at)
}

// The tuple of what the evaluators give.
pub(crate) fn evaluate_tuple(machine: &mut Machine<'_>, evaluators: &[Eval]) -> Outcome<Id> {
    let at = push_all(machine, evaluators)?;
    let tuple = machine.store.tuple_of(&machine.stack[at..]);
    machine.stack.truncate(at);
    Ok(tuple)
}

pub(crate) fn expect_set(machine: &Machine<'_>, id: Id, reason: &'static str) -> Outcome<Id> {
    if machine.store.kind_of(id) == KIND_SET {
        Ok(id)
    } else {
        Err(Bail(reason))
    }
}

pub(crate) fn evaluate_set(
    machine: &mut Machine<'_>,
    set: &Eval,
    reason: &'static str,
) -> Outcome<Id> {
    let id = set(machine)?;
    expect_set(machine, id, reason)
}

// The ids a level of nested bounds binds, and the set each draws from.
// A function built over the sets of its bounds.
type Construct = Arc<dyn Fn(&mut Machine<'_>, &[Id]) -> Outcome<Id> + Send + Sync>;

// Where an expression the compiler looks through is: the context its names are looked up in, or,
// in a body it reaches through an application, the names bound to values there.
struct Within<'c> {
    context: Option<&'c Context>,
    bound: Vec<TextId>,
}

fn bound_names(bounds: &[Bound]) -> Vec<TextId> {
    bounds
        .iter()
        .flat_map(|bound| match &bound.pattern {
            Pattern::Name(name) => vec![*name],
            Pattern::Tuple(names) => names.clone(),
        })
        .collect()
}

struct Level {
    set: Compiled,
    slots: Vec<u32>,
    tuple: bool,
    /// Whether it shares the set of the bound before it, as `a, b \in S` does.
    is_shared: bool,
}

pub(crate) fn kind_name(kind: &NodeKind) -> &'static str {
    match kind {
        NodeKind::Number(_) | NodeKind::WideNumber(_) => "Number",
        NodeKind::Decimal(_) => "Decimal",
        NodeKind::String(_) => "String",
        NodeKind::Identifier(_) => "Identifier",
        NodeKind::Apply { .. } => "Apply",
        NodeKind::OperatorReference(_) => "OperatorReference",
        NodeKind::Lambda { .. } => "Lambda",
        NodeKind::And(_) => "And",
        NodeKind::Or(_) => "Or",
        NodeKind::Prime(_) => "Prime",
        NodeKind::Unchanged(_) => "Unchanged",
        NodeKind::Enabled(_) => "Enabled",
        NodeKind::If { .. } => "If",
        NodeKind::Case { .. } => "Case",
        NodeKind::Let { .. } => "Let",
        NodeKind::Forall { .. } => "Forall",
        NodeKind::Exists { .. } => "Exists",
        NodeKind::UnboundedQuantifier { .. } => "UnboundedQuantifier",
        NodeKind::Choose { .. } => "Choose",
        NodeKind::SetEnumeration(_) => "SetEnumeration",
        NodeKind::SetFilter { .. } => "SetFilter",
        NodeKind::SetMap { .. } => "SetMap",
        NodeKind::Tuple(_) => "Tuple",
        NodeKind::FunctionConstruction { .. } => "FunctionConstruction",
        NodeKind::FunctionSet { .. } => "FunctionSet",
        NodeKind::Record(_) => "Record",
        NodeKind::RecordSet(_) => "RecordSet",
        NodeKind::Except { .. } => "Except",
        NodeKind::ExceptAt => "ExceptAt",
        NodeKind::FunctionApplication { .. } => "FunctionApplication",
        NodeKind::Bracket(_) => "Bracket",
        NodeKind::FieldAccess { .. } => "FieldAccess",
        NodeKind::Product(_) => "Product",
        NodeKind::Always(_) => "Always",
        NodeKind::Eventually(_) => "Eventually",
        NodeKind::BoxAction { .. } => "BoxAction",
        NodeKind::AngleAction { .. } => "AngleAction",
        NodeKind::WeakFairness { .. } => "WeakFairness",
        NodeKind::StrongFairness { .. } => "StrongFairness",
        NodeKind::Label { .. } => "Label",
        NodeKind::Subexpression(_) => "Subexpression",
        NodeKind::Definition(_) => "Definition",
        NodeKind::Reference(_) => "Reference",
    }
}

impl Compiler<'_> {
    pub(crate) fn compile_node(&mut self, node: NodeId, context: &Context) -> Compiling<Compiled> {
        let (_, kind) = self.node(node);
        match kind {
            NodeKind::Number(value) => Ok(constant(self.store.int(i64::from(*value))?)),
            NodeKind::WideNumber(_) => Err(Bail("integer overflow").into()),
            NodeKind::String(text) => {
                let units = self.units(*text);
                Ok(constant(self.store.str(&units)))
            }
            NodeKind::Identifier(name) => self.compile_identifier(name, context),
            NodeKind::Apply { name, args } => self.compile_apply(name, args, context),
            NodeKind::And(operands) => self.compile_junction(operands, true, context),
            NodeKind::Or(operands) => self.compile_junction(operands, false, context),
            NodeKind::Prime(expression) => {
                if context.is_primed {
                    return unsupported("a doubly primed expression");
                }
                self.compile(*expression, &context.primed(true))
            }
            NodeKind::If {
                condition,
                consequent,
                alternative,
            } => {
                let condition = self.compile_boolean(*condition, context)?;
                let consequent = self.compile(*consequent, context)?;
                let alternative = self.compile(*alternative, context)?;
                let (test, then, otherwise) = (
                    condition.eval.clone(),
                    consequent.eval.clone(),
                    alternative.eval.clone(),
                );
                Ok(Compiled {
                    is_costly: consequent.is_costly || alternative.is_costly,
                    is_normalized: consequent.is_normalized && alternative.is_normalized,
                    is_enumerated: consequent.is_enumerated && alternative.is_enumerated,
                    are_elements_enumerated: consequent.are_elements_enumerated
                        && alternative.are_elements_enumerated,
                    is_in_order: consequent.is_in_order && alternative.is_in_order,
                    are_elements_in_order: consequent.are_elements_in_order
                        && alternative.are_elements_in_order,
                    are_elements_of_elements_in_order: consequent.are_elements_of_elements_in_order
                        && alternative.are_elements_of_elements_in_order,
                    is_boolean: consequent.is_boolean && alternative.is_boolean,
                    has_infinite_part: consequent.may_be_infinite()
                        || alternative.may_be_infinite(),
                    // The reference evaluates the condition again, which mustn't print twice.
                    reference: if [&condition, &consequent, &alternative]
                        .iter()
                        .any(|part| part.is_printing())
                    {
                        None
                    } else {
                        let test = condition.eval.clone();
                        reference_of(&consequent)
                            .zip(reference_of(&alternative))
                            .map(|(then, otherwise)| {
                                Arc::new(move |machine: &mut Machine<'_>| {
                                    if test(machine)? == TRUE {
                                        then(machine)
                                    } else {
                                        otherwise(machine)
                                    }
                                }) as lazy::Reference
                            })
                    },
                    ..leaf(
                        eval(move |machine| {
                            if test(machine)? == TRUE {
                                then(machine)
                            } else {
                                otherwise(machine)
                            }
                        }),
                        Footprint::merge_all([
                            &condition.footprint,
                            &consequent.footprint,
                            &alternative.footprint,
                        ]),
                    )
                })
            }
            NodeKind::Case { arms, other } => {
                let mut conditions = Vec::new();
                let mut bodies = Vec::new();
                for &(condition, body) in arms {
                    conditions.push(self.compile_boolean(condition, context)?);
                    bodies.push(self.compile(body, context)?);
                }
                let other = other
                    .map(|other| self.compile(other, context))
                    .transpose()?;
                let footprint = Footprint::merge_all(
                    conditions
                        .iter()
                        .map(|condition| &condition.footprint)
                        .chain(bodies.iter().map(|body| &body.footprint))
                        .chain(other.iter().map(|other| &other.footprint)),
                );
                let is_normalized = bodies.iter().all(|body| body.is_normalized)
                    && other.as_ref().is_none_or(|other| other.is_normalized);
                let is_enumerated = bodies.iter().all(|body| body.is_enumerated)
                    && other.as_ref().is_none_or(|other| other.is_enumerated);
                let are_elements_enumerated =
                    bodies.iter().all(|body| body.are_elements_enumerated)
                        && other
                            .as_ref()
                            .is_none_or(|other| other.are_elements_enumerated);
                // A CASE whose every arm is a boolean is one, as an IF is.
                let is_boolean = bodies.iter().all(|body| body.is_boolean)
                    && other.as_ref().is_none_or(|other| other.is_boolean);
                let tests: Vec<Eval> = conditions
                    .iter()
                    .map(|condition| condition.eval.clone())
                    .collect();
                let values: Vec<Eval> = bodies.iter().map(|body| body.eval.clone()).collect();
                let otherwise = other.map(|other| other.eval);
                Ok(Compiled {
                    is_costly: true,
                    is_normalized,
                    is_enumerated,
                    are_elements_enumerated,
                    is_boolean,
                    ..leaf(
                        eval(move |machine| {
                            for (test, value) in tests.iter().zip(&values) {
                                if test(machine)? == TRUE {
                                    return value(machine);
                                }
                            }
                            match &otherwise {
                                Some(otherwise) => otherwise(machine),
                                None => Err(Bail("no CASE arm holds")),
                            }
                        }),
                        footprint,
                    )
                })
            }
            NodeKind::Let {
                definitions, body, ..
            } => {
                let (inner, kept_once) =
                    self.bind_let_definitions_kept(definitions, *body, context, true, true)?;
                let compiled = self.compile(*body, &inner)?;
                Self::keep_once(&kept_once, compiled)
            }
            NodeKind::Forall { bounds, body } => {
                self.compile_quantifier(bounds, *body, true, context)
            }
            NodeKind::Exists { bounds, body } => {
                self.compile_quantifier(bounds, *body, false, context)
            }
            NodeKind::Choose { pattern, set, body } => {
                // TLC fails to evaluate a CHOOSE without a bound, only where it evaluates one.
                let Some(set) = set else {
                    return Ok(leaf(
                        eval(|_| Err(Bail("an unbounded CHOOSE"))),
                        Footprint::default(),
                    ));
                };
                self.compile_choose(pattern, *set, *body, context)
            }
            // TLC fails to evaluate a quantifier without a bound (`Tool`'s OPCODE_ue and
            // OPCODE_uf), and a temporal one in a state (OPCODE_te and OPCODE_tf), only where it
            // evaluates one.
            NodeKind::UnboundedQuantifier { is_temporal, .. } => Ok(leaf(
                if *is_temporal {
                    eval(|_| Err(Bail("a temporal formula in a state")))
                } else {
                    eval(|_| Err(Bail("an unbounded quantifier")))
                },
                Footprint::default(),
            )),
            NodeKind::SetEnumeration(elements) => {
                let elements = elements
                    .iter()
                    .map(|&element| self.compile(element, context).map(Compiled::held))
                    .collect::<Compiling<Vec<Compiled>>>()?;
                // A state can't hold Nat, Int or STRING, which TLC can't fingerprint: the search
                // looks for one as it does for a function TLC keeps lazy.
                self.is_lambda_built |= elements
                    .iter()
                    .any(|element| element.infinite_value.is_some());
                Ok(Self::compile_set_enumeration(&elements))
            }
            NodeKind::Tuple(elements) => {
                if elements.is_empty() {
                    return Ok(constant(EMPTY_TUPLE));
                }
                let elements = elements
                    .iter()
                    .map(|&element| self.compile(element, context).map(Compiled::held))
                    .collect::<Compiling<Vec<Compiled>>>()?;
                let evaluators: Vec<Eval> = elements
                    .iter()
                    .map(|element| element.eval.clone())
                    .collect();
                Ok(Compiled {
                    is_costly: true,
                    ..leaf(
                        eval(move |machine| evaluate_tuple(machine, &evaluators)),
                        Footprint::merge_all(elements.iter().map(|element| &element.footprint)),
                    )
                })
            }
            NodeKind::Record(fields) => {
                let mut compiled = Vec::new();
                for &(name, value) in fields {
                    let units = self.units(name);
                    let key = self.store.str(&units);
                    compiled.push((key, self.compile(value, context)?.held()));
                }
                // TLC evaluates the fields in the order written, and keeps them in its order of
                // their names, which strings compare without fail.
                let mut order: Vec<usize> = (0..compiled.len()).collect();
                let mut sort_error = None;
                order.sort_by(|&left, &right| {
                    match self.store.compare(compiled[left].0, compiled[right].0) {
                        Ok(order) => order.cmp(&0),
                        Err(bail) => {
                            sort_error = Some(bail);
                            std::cmp::Ordering::Equal
                        }
                    }
                });
                if let Some(bail) = sort_error {
                    return Err(bail.into());
                }
                let keys: Vec<Id> = order.iter().map(|&field| compiled[field].0).collect();
                let shape = self.store.create_record_shape(&keys);
                // Each field as written, with its place among the fields in TLC's order.
                let mut evaluators: Vec<(Eval, usize)> = compiled
                    .iter()
                    .map(|field| (field.1.eval.clone(), 0))
                    .collect();
                for (place, &field) in order.iter().enumerate() {
                    evaluators[field].1 = place;
                }
                Ok(Compiled {
                    is_costly: true,
                    ..leaf(
                        eval(move |machine| {
                            let at = machine.stack.len();
                            machine.stack.resize(at + evaluators.len(), 0);
                            for (evaluate, place) in &evaluators {
                                match evaluate(machine) {
                                    Ok(value) => machine.stack[at + place] = value,
                                    Err(bail) => {
                                        machine.stack.truncate(at);
                                        return Err(bail);
                                    }
                                }
                            }
                            let values = machine.stack.split_off(at);
                            Ok(machine.store.record_of(&shape, &values))
                        }),
                        Footprint::merge_all(compiled.iter().map(|field| &field.1.footprint)),
                    )
                })
            }
            NodeKind::FunctionApplication { function, args } => {
                // `RecordValue.apply` of a field, or `TupleValue.apply` of a position, written so,
                // reads only that one.
                let nulls = match args.as_slice() {
                    [argument] => self.null_fields(*function).filter(|nulls| {
                        let (record_field, tuple_position) = match self.node(*argument).1 {
                            NodeKind::String(text) => (Some(*text), None),
                            NodeKind::Number(number) => (None, Some(*number)),
                            _ => (None, None),
                        };
                        let is_read = |(_, at): &(NodeId, Result<TextId, usize>)| match at {
                            Ok(name) => record_field.is_some_and(|field| {
                                self.ir.texts[field as usize] == self.ir.texts[*name as usize]
                            }),
                            Err(position) => tuple_position == Some(*position as i32),
                        };
                        let is_present = match self.node(*function).1 {
                            NodeKind::Record(fields) => record_field.is_some_and(|field| {
                                fields.iter().any(|(name, _)| {
                                    self.ir.texts[*name as usize] == self.ir.texts[field as usize]
                                })
                            }),
                            NodeKind::Tuple(elements) => tuple_position.is_some_and(|position| {
                                (1..=elements.len() as i32).contains(&position)
                            }),
                            _ => false,
                        };
                        is_present && !nulls.iter().any(is_read)
                    }),
                    _ => None,
                };
                let nulls: Vec<NodeId> =
                    nulls.into_iter().flatten().map(|(node, _)| node).collect();
                self.with_null_substituted(&nulls, |compiler| {
                    compiler.compile_function_application(*function, args, context)
                })
            }
            NodeKind::FieldAccess { record, field } => {
                if let Some(statistic) = self.compile_statistic(*record, *field, context)? {
                    return Ok(statistic);
                }
                // `RecordValue.apply` of another field than those holding a null reads none of
                // them.
                let nulls: Vec<NodeId> = match self.node(*record).1 {
                    NodeKind::Record(fields)
                        if fields.iter().any(|(name, value)| {
                            self.ir.texts[*name as usize] == self.ir.texts[*field as usize]
                                && !self.is_uninitialized_literal(*value)
                        }) =>
                    {
                        self.null_fields(*record)
                            .into_iter()
                            .flatten()
                            .map(|(node, _)| node)
                            .collect()
                    }
                    _ => Vec::new(),
                };
                let record = self
                    .with_null_substituted(&nulls, |compiler| compiler.compile(*record, context))?;
                let units = self.units(*field);
                let key = self.store.str(&units);
                let hint = Arc::new(AtomicU32::new(0));
                // A field of a simulation's statistics or of its behavior that holds no empty
                // record reads the value as TLC holds it; the behavior is one too.
                let name = String::from_utf16_lossy(&units);
                let record = match record.shape {
                    Shape::SimulationRun(SimulationRun::Stats) if name == "behavior" => {
                        return Ok(Compiled {
                            shape: Shape::SimulationRun(SimulationRun::Behavior),
                            ..leaf(SimulationRun::Behavior.guarded(), record.footprint)
                        });
                    }
                    Shape::SimulationRun(SimulationRun::Stats | SimulationRun::Behavior)
                        if name != "actions" =>
                    {
                        builtins::unguarded(record)
                    }
                    _ => record,
                };
                // FieldOfVar: r.f of a variable r, read straight from the register.
                if let Shape::Current(variable) = record.shape {
                    return Ok(leaf(
                        eval(move |machine| {
                            let value = machine.read_current(variable)?;
                            field_of(machine, value, key, &hint)
                        }),
                        record.footprint,
                    ));
                }
                // FieldOfSlot: r.f of a bound name r.
                if let Shape::Slot(slot) = record.shape {
                    return Ok(Compiled {
                        shape: Shape::Field { slot, key },
                        ..leaf(
                            eval(move |machine| {
                                let value = machine.locals[slot as usize];
                                field_of(machine, value, key, &hint)
                            }),
                            record.footprint,
                        )
                    });
                }
                let evaluate = record.eval.clone();
                Ok(leaf(
                    eval(move |machine| {
                        let value = evaluate(machine)?;
                        field_of(machine, value, key, &hint)
                    }),
                    record.footprint,
                ))
            }
            NodeKind::Except { function, updates } => {
                self.compile_except(*function, updates, context)
            }
            NodeKind::ExceptAt => {
                let at = self.at;
                match lookup(&context.scope, at) {
                    Some(found) => self.compile_binding(&found, context),
                    None => unsupported("@ outside EXCEPT"),
                }
            }
            NodeKind::FunctionConstruction { bounds, body, .. } => {
                self.compile_function_construction(bounds, *body, context)
            }
            NodeKind::SetFilter { bound, predicate } => {
                self.compile_set_filter(bound, *predicate, context)
            }
            NodeKind::SetMap { expression, bounds } => {
                self.compile_set_map(*expression, bounds, context)
            }
            NodeKind::FunctionSet { .. } | NodeKind::RecordSet(_) | NodeKind::Product(_) => {
                self.compile_lazy_set(kind, context)
            }
            NodeKind::Unchanged(expression) => self.compile_unchanged(*expression, context),
            // TLC evaluates <<A>>_e and [A]_e as A, then, unless A decides, e in each state.
            NodeKind::AngleAction { action, subscript }
            | NodeKind::BoxAction { action, subscript } => {
                if context.is_primed {
                    return unsupported("a primed action");
                }
                let is_angle = matches!(kind, NodeKind::AngleAction { .. });
                let action = self.compile_boolean(*action, context)?;
                let now = self.compile(*subscript, context)?;
                let next = self.compile(*subscript, &context.primed(true))?;
                let footprint =
                    Footprint::merge_all([&action.footprint, &now.footprint, &next.footprint]);
                let (action, now, next) = (action.eval, now.eval, next.eval);
                Ok(leaf(
                    eval(move |machine| {
                        if (action(machine)? == TRUE) != is_angle {
                            return Ok(bool_id(!is_angle));
                        }
                        let value = now(machine)?;
                        let next = next(machine)?;
                        let is_unchanged = machine.store.equals(value, next)?;
                        Ok(bool_id(is_unchanged != is_angle))
                    }),
                    footprint,
                ))
            }
            NodeKind::Enabled(action) => self.compile_enabled(*action, context),
            NodeKind::Label { body, .. } => self.compile(*body, context),
            // TLC can't evaluate a temporal formula in a state, but a predicate may hold one in a
            // branch it never takes, such as a recursive operator's: the interpreter reports where
            // a run reaches one.
            NodeKind::Always(_)
            | NodeKind::Eventually(_)
            | NodeKind::WeakFairness { .. }
            | NodeKind::StrongFairness { .. } => Ok(leaf(
                eval(|_| Err(Bail("a temporal formula in a state"))),
                Footprint::default(),
            )),
            kind => unsupported(format!("expression {}", kind_name(kind))),
        }
    }

    pub(crate) fn compile_unchanged(
        &mut self,
        expression: NodeId,
        context: &Context,
    ) -> Compiling<Compiled> {
        let now = self.compile(expression, &context.primed(false))?;
        let next = self.compile(expression, &context.primed(true))?;
        let footprint = now.footprint.merge(&next.footprint);
        let (now, next) = (now.eval, next.eval);
        // TLC evaluates the current state's side first (Tool.evalAppl's OPCODE_unchanged).
        let evaluate = move |machine: &mut Machine<'_>| {
            let now = now(machine)?;
            let next = next(machine)?;
            Ok(bool_id(machine.store.equals(now, next)?))
        };
        // Where the expression is a tuple of state variables, or of such tuples, its two values
        // are equal just where each variable's two values are, which TLC compares in order
        // (`TupleValue.equals`): the tuples are built only where a variable isn't assigned or a
        // pair doesn't compare as unequal, for whatever TLC does then.
        let variables = self
            .get_unchanged_indices(expression, &context.primed(false), 0)
            .ok()
            .flatten()
            .filter(|found| {
                found
                    .iter()
                    .all(|&(variable, _)| (variable as usize) < self.ir.variables.len())
            });
        let Some(variables) = variables else {
            return Ok(leaf(eval(evaluate), footprint));
        };
        let variables: Box<[usize]> = variables
            .into_iter()
            .map(|(variable, _)| variable as usize)
            .collect();
        Ok(leaf(
            eval(move |machine| {
                let is_assigned = variables.iter().all(|&variable| {
                    machine.cur[variable] != UNASSIGNED && machine.next[variable] != UNASSIGNED
                });
                if !is_assigned {
                    return evaluate(machine);
                }
                for &variable in &variables {
                    let (now, next) = (machine.cur[variable], machine.next[variable]);
                    if now == next && !machine.store.comparison_can_fail(now) {
                        continue;
                    }
                    return match machine.store.equals(now, next) {
                        Ok(false) => Ok(FALSE),
                        _ => evaluate(machine),
                    };
                }
                Ok(TRUE)
            }),
            footprint,
        ))
    }

    fn compile_junction(
        &mut self,
        operands: &[NodeId],
        is_and: bool,
        context: &Context,
    ) -> Compiling<Compiled> {
        let operands = operands
            .iter()
            .map(|&operand| self.compile(operand, context))
            .collect::<Compiling<Vec<Compiled>>>()?;
        Ok(Self::junction(&operands, is_and))
    }

    // AndAll and OrAny: the operands in one predicate, each checked to be a boolean as
    // compileBoolean checks it.
    pub(crate) fn junction(operands: &[Compiled], is_and: bool) -> Compiled {
        let predicates = operands.iter().map(Predicate::of).collect();
        Compiled {
            is_costly: operands.iter().any(|operand| operand.is_costly),
            ..predicate_node(
                if is_and {
                    Predicate::And(predicates)
                } else {
                    Predicate::Or(predicates)
                },
                Footprint::merge_all(operands.iter().map(|operand| &operand.footprint)),
            )
        }
    }

    // --- quantifiers and bindings ---

    // Binds the names of a bound to fresh slots.
    pub(crate) fn bind_bound(&mut self, pattern: &Pattern, context: &Context) -> Binder {
        match pattern {
            Pattern::Name(name) => {
                let slot = self.allocate_slot();
                Binder {
                    context: context.with_scope(bind(&context.scope, *name, Binding::Slot(slot))),
                    slots: vec![slot],
                    tuple: false,
                }
            }
            Pattern::Tuple(names) => {
                let mut scope = context.scope.clone();
                let slots = names
                    .iter()
                    .map(|&name| {
                        let slot = self.allocate_slot();
                        scope = bind(&scope, name, Binding::Slot(slot));
                        slot
                    })
                    .collect();
                Binder {
                    context: context.with_scope(scope),
                    slots,
                    tuple: true,
                }
            }
        }
    }

    // The levels of several bounds. With `is_null_empty`, a bound written as a set enumeration of
    // one INSTANCE fact literal TLC did not initialize compiles as the empty set: `Tool.contexts`
    // evaluates and enumerates every bound in turn, and the null that enumeration gives first
    // ends the `ContextEnumerator` at once, as an empty bound's does, once every bound after it
    // was evaluated as well.
    fn compile_levels(
        &mut self,
        bounds: &[Bound],
        context: &Context,
        is_null_empty: bool,
    ) -> Compiling<(Vec<Level>, Vec<u32>, Context)> {
        let mut inner = context.clone();
        let mut levels = Vec::new();
        let mut bound = Vec::new();
        for (index, item) in bounds.iter().enumerate() {
            let is_shared =
                index > 0 && self.node(item.set).0 == self.node(bounds[index - 1].set).0;
            let is_null = is_null_empty
                && matches!(self.node(item.set).1, NodeKind::SetEnumeration(items)
                    if items.len() == 1 && self.is_uninitialized_literal(items[0]));
            let set = if is_null {
                Self::compile_set_enumeration(&[])
            } else {
                self.compile(item.set, &inner)?
            };
            let binder = self.bind_bound(&item.pattern, &inner);
            if !binder.tuple && set.interval.is_some() {
                self.int_slots.insert(binder.slots[0]);
            }
            inner = binder.context;
            bound.extend(&binder.slots);
            levels.push(Level {
                set,
                slots: binder.slots,
                tuple: binder.tuple,
                is_shared,
            });
        }
        Ok((levels, bound, inner))
    }

    fn compile_quantifier(
        &mut self,
        bounds: &[Bound],
        body: NodeId,
        is_forall: bool,
        context: &Context,
    ) -> Compiling<Compiled> {
        let (mut levels, bound, inner) = self.compile_levels(bounds, context, true)?;
        // TLC enumerates each bound's set (`Tool.contexts`).
        for level in &mut levels {
            level.set = Self::listed(&level.set);
        }
        let body = self.compile(body, &inner)?;
        let footprint = Footprint::merge_all(levels.iter().map(|level| &level.set.footprint))
            .merge(&body.footprint.without_slots(&bound));
        // A body that prints is evaluated for each element in the order TLC enumerates the set
        // (`Tool.contexts`), until one decides the quantifier.
        // Of several bounds, TLC evaluates each bound's set, then the body for each binding, the
        // first bound varying fastest (`ContextEnumerator`), until one decides the quantifier.
        if body.is_printing()
            && levels.len() > 1
            && levels.iter().all(|level| level.set.infinite.is_none())
        {
            let (levels, body) = (Arc::new(levels), body.eval);
            return Ok(Compiled {
                is_costly: true,
                is_boolean: true,
                ..leaf(
                    eval(move |machine| {
                        let sets = evaluate_bound_sets(
                            machine,
                            &levels,
                            "quantified over a non-set",
                            true,
                        )?;
                        let is_undecided =
                            for_each_binding(machine, &levels, &sets, |machine, _| {
                                Ok((super::check_boolean(body(machine)?)? == TRUE) == is_forall)
                            })?;
                        Ok(bool_id(if is_undecided { is_forall } else { !is_forall }))
                    }),
                    footprint,
                )
            });
        }
        if body.is_printing()
            && let [level] = &levels[..]
        {
            let ordered = self.order(level.set.clone(), bounds[0].set, context, false)?;
            let set = level.set.clone();
            let (slots, tuple, body) = (level.slots.clone(), level.tuple, body.eval);
            return Ok(Compiled {
                is_costly: true,
                is_boolean: true,
                ..leaf(
                    eval(move |machine| {
                        let id = (ordered.eval)(machine)?;
                        let size = ordered.size(machine, id)?;
                        set.check_enumerated(machine, id, size)?;
                        for position in 0..size {
                            let element = machine.store.element_at(id, position);
                            assign_bound(machine, &slots, tuple, element)?;
                            let value = super::check_boolean(body(machine)?)?;
                            if (value == TRUE) != is_forall {
                                return Ok(bool_id(!is_forall));
                            }
                        }
                        Ok(bool_id(is_forall))
                    }),
                    footprint,
                )
            });
        }
        // TLC takes an enumerator of each bound's set before it binds any (`Tool.contexts`), and
        // fails at the first it only tests for membership, such as Nat or Seq(S), whatever the
        // sets before it hold.
        if let Some(first) = levels.iter().position(|level| level.set.infinite.is_some()) {
            let before: Vec<Eval> = levels[..first]
                .iter()
                .map(|level| level.set.eval.clone())
                .collect();
            return Ok(Compiled {
                is_costly: true,
                is_boolean: true,
                ..leaf(
                    eval(move |machine| {
                        for set in &before {
                            set(machine)?;
                        }
                        Err(Bail(super::INFINITE_BOUND))
                    }),
                    footprint,
                )
            });
        }
        let predicate = Predicate::of(&body);
        // ForallInterval and ExistsInterval: a name over a..b at each level counts through the
        // interval without building it.
        let evaluate = if levels
            .iter()
            .all(|level| !level.tuple && level.set.interval.is_some())
        {
            super::fused::quantify_intervals(
                levels
                    .iter()
                    .map(|level| {
                        (
                            level.slots[0],
                            level.set.interval.clone().unwrap(),
                            level.is_shared,
                        )
                    })
                    .collect(),
                predicate,
                is_forall,
            )
        } else {
            let reject = match &levels[..] {
                [level] if !level.tuple => Reject::of(&predicate, level.slots[0]),
                _ => None,
            };
            let levels = Arc::new(levels);
            let body = predicate.build();
            eval(move |machine| {
                quantify(machine, &levels, &body, reject.as_ref(), is_forall).map(bool_id)
            })
        };
        Ok(Compiled {
            is_costly: true,
            is_boolean: true,
            ..leaf(evaluate, footprint)
        })
    }

    fn compile_choose(
        &mut self,
        pattern: &Pattern,
        set: NodeId,
        body: NodeId,
        context: &Context,
    ) -> Compiling<Compiled> {
        let set = self.compile(set, context)?;
        let binder = self.bind_bound(pattern, context);
        let body = self.compile_boolean(body, &binder.context)?;
        let footprint = set
            .footprint
            .merge(&body.footprint.without_slots(&binder.slots));
        // CHOOSE over SUBSET S takes the subsets in their normalized order without building
        // the power set (`SubsetValue.elementsNormalized`): by size, and each size in the order
        // of S's elements, which the engine follows where it would build too many.
        let subset_base = set
            .subset_base
            .as_ref()
            .filter(|base| base.is_normalized && base.infinite.is_none() && !base.has_infinite_part)
            .map(|base| base.eval.clone());
        let bound = set.clone();
        let (set, body, slots, tuple) = (set.eval, body.eval, binder.slots, binder.tuple);
        Ok(Compiled {
            is_costly: true,
            ..leaf(
                eval(move |machine| {
                    let id = match &subset_base {
                        Some(base) => {
                            let base = base(machine)?;
                            let base = expect_set(machine, base, "expected a set")?;
                            if machine.store.size_of(base) <= super::builtins::MAXIMUM_POWER_SET {
                                super::builtins::power_set(machine, base)?
                            } else {
                                return choose_subset(machine, base, &slots, tuple, &body);
                            }
                        }
                        None => {
                            let id = evaluate_set(machine, &set, "CHOOSE from a non-set")?;
                            let size = machine.store.size_of(id);
                            bound.check_enumerated(machine, id, size)?;
                            id
                        }
                    };
                    for index in 0..machine.store.size_of(id) {
                        let element = machine.store.element_at(id, index);
                        assign_converted(machine, &slots, tuple, element)?;
                        if body(machine)? == TRUE {
                            return Ok(element);
                        }
                    }
                    Err(Bail("CHOOSE found no element"))
                }),
                footprint,
            )
        })
    }

    fn compile_set_filter(
        &mut self,
        bound: &Bound,
        predicate: NodeId,
        context: &Context,
    ) -> Compiling<Compiled> {
        let set = self.compile(bound.set, context)?;
        let binder = self.bind_bound(&bound.pattern, context);
        let compiled = self.compile(predicate, &binder.context)?;
        let footprint = set
            .footprint
            .merge(&compiled.footprint.without_slots(&binder.slots));
        let predicate = Predicate::of(&compiled);
        let reject = (!binder.tuple)
            .then(|| Reject::of(&predicate, binder.slots[0]))
            .flatten();
        let filter = Arc::new(Filter {
            set: set.eval.clone(),
            stream: (!set.is_reducible && set.interval.is_none())
                .then(|| super::reference_of(&set))
                .flatten(),
            slots: binder.slots,
            tuple: binder.tuple,
            predicate: predicate.build(),
            reject,
        });
        // TLC tests membership in a filter of a set it can't enumerate, such as Nat, by the set's
        // membership and the predicate (SetPredValue.member), and fails where it enumerates it.
        if set.infinite.is_some() {
            let base = self.member_test(&set);
            let tested = Arc::clone(&filter);
            return Ok(Compiled {
                is_costly: true,
                infinite: set.infinite,
                parts: Some(Self::parts_of(&set)),
                member: Some(member(move |machine, element| {
                    Ok(base(machine, element)? && test_element(machine, &tested, element)?)
                })),
                ..leaf(
                    eval(|_| Err(Bail("enumerated a filter of an infinite set"))),
                    footprint,
                )
            });
        }
        let parts = Arc::clone(&filter);
        // Whether TLC's set is Reducible, a set enumeration or an interval, which it filters at
        // once (`Tool`'s OPCODE_sso).
        let is_reduced = set.is_enumerated || set.interval.is_some() || set.is_reducible;
        // TLC filters a set it can't enumerate, such as SUBSET S, lazily, in the order of the set.
        let reference = if set.is_normalized {
            None
        } else {
            let tested = Arc::clone(&filter);
            let test: lazy::Test =
                Arc::new(move |machine, element| test_element(machine, &tested, element));
            combine_references(&[&set], move |machine, mut bases| {
                lazy::Lazy::filter(machine, bases.remove(0), Arc::clone(&test))
            })
        };
        // TLC keeps a filter of a set it doesn't reduce (any but an enumeration or an interval)
        // lazy too, and tests membership in it the same way: the predicate of the one element.
        let tested = (!set.is_normalized).then(|| {
            let base = self.member_test(&set);
            let tested = Arc::clone(&filter);
            member(move |machine, element| {
                Ok(base(machine, element)? && test_element(machine, &tested, element)?)
            })
        });
        let tested_parts = (!set.is_normalized).then(|| Self::parts_of(&set));
        Ok(Compiled {
            is_costly: true,
            is_normalized: set.is_normalized,
            has_infinite_part: set.has_infinite_part,
            member: tested,
            parts: tested_parts,
            reference,
            is_enumerated: set.is_enumerated,
            // TLC filters a Reducible set at once, into a set enumeration, and keeps the filter
            // of any other set lazy (`Tool`'s OPCODE_sso).
            is_reducible: set.is_reducible || set.interval.is_some(),
            is_irreducible: set.is_irreducible,
            are_elements_enumerated: set.are_elements_enumerated,
            is_in_order: set.is_in_order,
            are_elements_in_order: set.are_elements_in_order,
            are_elements_of_elements_in_order: set.are_elements_of_elements_in_order,
            filter: Some(filter),
            ..leaf(
                eval(move |machine| {
                    let (input, elements) = parts.elements(machine)?;
                    let size = elements.len();
                    let at = machine.stack.len();
                    for element in elements {
                        if let Some(reject) = &parts.reject
                            && reject.rejects(machine, element)
                        {
                            continue;
                        }
                        let assign = if is_reduced {
                            assign_reduced
                        } else {
                            assign_bound
                        };
                        let kept = assign(machine, &parts.slots, parts.tuple, element)
                            .and_then(|()| (parts.predicate)(machine));
                        match kept {
                            Ok(true) => {
                                if let Err(bail) = check_set_insertion(machine.stack.len() - at) {
                                    machine.stack.truncate(at);
                                    return Err(bail);
                                }
                                machine.stack.push(element);
                            }
                            Ok(false) => {}
                            Err(bail) => {
                                machine.stack.truncate(at);
                                return Err(bail);
                            }
                        }
                    }
                    let kept = machine.stack.split_off(at);
                    match input {
                        Some(set) if kept.len() == size => Ok(set),
                        Some(_) => Ok(machine.store.set_of_sorted(&kept)),
                        None => machine.store.set_of(&kept),
                    }
                }),
                footprint,
            )
        })
    }

    fn compile_set_map(
        &mut self,
        expression: NodeId,
        bounds: &[Bound],
        context: &Context,
    ) -> Compiling<Compiled> {
        let (mut levels, bound, inner) = self.compile_levels(bounds, context, true)?;
        // TLC enumerates each bound's set into the set it builds (`Tool.evalImpl`'s
        // OPCODE_soa).
        for level in &mut levels {
            level.set = Self::listed(&level.set);
        }
        let body = self.compile(expression, &inner)?;
        let footprint = Footprint::merge_all(levels.iter().map(|level| &level.set.footprint))
            .merge(&body.footprint.without_slots(&bound));
        let are_elements_enumerated = body.is_enumerated;
        let are_elements_in_order = body.is_in_order;
        let are_elements_of_elements_in_order = body.are_elements_in_order;
        let levels = Arc::new(levels);
        let body = body.eval;
        Ok(Compiled {
            is_costly: true,
            is_enumerated: true,
            are_elements_enumerated,
            is_in_order: true,
            are_elements_in_order,
            are_elements_of_elements_in_order,
            ..leaf(
                eval(move |machine| {
                    let at = machine.stack.len();
                    let result = map_images(machine, &levels, &body);
                    let images = machine.stack.split_off(at);
                    result?;
                    machine.store.set_of_range(&images)
                }),
                footprint,
            )
        })
    }

    pub(crate) fn compile_function_construction(
        &mut self,
        bounds: &[Bound],
        body: NodeId,
        context: &Context,
    ) -> Compiling<Compiled> {
        // An application's function TLC keeps lazy whatever its domain where its body has an
        // effect, evaluating the body only at the key applied (`is_applied_lazily`).
        let is_effect_kept_lazy = self.applied_construction.is_some_and(|applied| {
            matches!(self.node(applied).1, NodeKind::FunctionConstruction { body: applied, .. }
                if *applied == body)
        });
        let (mut levels, bound, inner) = self.compile_levels(bounds, context, false)?;
        // A function over a set TLC doesn't reduce, such as S \X T or SUBSET S, TLC keeps lazy
        // wherever it evaluates it (OPCODE_fc).
        let is_kept_lazy = levels.iter().any(|level| level.set.is_irreducible);
        // TLC enumerates each bound's set (`Tool.contexts`).
        for level in &mut levels {
            level.set = Self::listed(&level.set);
        }
        let body_node = self.node(body).0;
        let body_id = body;
        let body = self.compile(body, &inner)?;
        let footprint = Footprint::merge_all(levels.iter().map(|level| &level.set.footprint))
            .merge(&body.footprint.without_slots(&bound));
        let body_footprint = body.footprint.clone();
        let body_for_lambda = body.eval.clone();
        let body_eval = body.eval;
        let body = eval(move |machine| machine.constructed_function_body(&body_eval));
        let levels_for_lambda: Vec<(Compiled, Vec<u32>, bool)> = levels
            .iter()
            .map(|level| (level.set.clone(), level.slots.clone(), level.tuple))
            .collect();
        let levels = Arc::new(levels);
        // The function over the bounds' sets, evaluated once each (`Tool.contexts`).
        let construct: Construct = if let [level] = &levels[..] {
            // A function of one bound, a tuple pattern included, takes each element of its
            // set.
            let (slots, tuple) = (level.slots.clone(), level.tuple);
            Arc::new(move |machine, sets| {
                let set = sets[0];
                let size = machine.store.size_of(set);
                let at = machine.stack.len();
                for index in 0..size {
                    let element = machine.store.element_at(set, index);
                    let bound =
                        assign_bound(machine, &slots, tuple, element).and_then(|()| body(machine));
                    match bound {
                        Ok(value) => machine.stack.push(value),
                        Err(bail) => {
                            machine.stack.truncate(at);
                            return Err(bail);
                        }
                    }
                }
                let values = machine.stack.split_off(at);
                let function = machine.store.function_over_set(set, &values);
                Ok(machine.store.mark_built_as_function(function))
            })
        } else {
            // A function of several arguments takes tuples, in TLC's order of the product.
            let levels = Arc::clone(&levels);
            Arc::new(move |machine, sets| {
                let mut keys = Vec::new();
                let mut values = Vec::new();
                for_each_binding(machine, &levels, sets, |machine, current| {
                    keys.push(machine.store.tuple_of(current));
                    values.push(body(machine)?);
                    Ok(true)
                })?;
                machine.store.function_of(&keys, &values)
            })
        };
        // TLC keeps a function lazy where it can't enumerate a bound's set
        // (`FcnLambdaValue`), as it can't Nat.
        // So it does over a value that isn't a set, such as `[e \in <<1, 2>> |-> e]`, which isn't
        // Reducible (OPCODE_fc builds the function at once only over Reducible domains): one
        // written as such a value is held as it is, as the domain of a function kept lazy.
        let has_non_set_bound = bounds.iter().any(|bound| self.is_non_set_value(bound.set));
        let is_lambda_possible = has_non_set_bound
            || levels_for_lambda
                .iter()
                .any(|(set, ..)| set.may_be_infinite());
        // Whether the body may have an effect, which a key outside the domain shows
        // (`OUTSIDE_WITH_EFFECTS`): known of the constructor an application keeps lazy for its
        // effects, and looked for only where TLC may keep the function lazy otherwise, as the
        // walk through the definitions the body names costs.
        let has_effect = is_effect_kept_lazy
            || (is_kept_lazy || is_lambda_possible)
                && self.may_have_effect_in(body_id, &inner, &mut HashSet::new());
        // A domain TLC only tests, such as `{n \in Nat : n < k}` or `Seq(S)`, is tested as the
        // engine tests membership in it.
        let domains: Vec<Reference> = levels_for_lambda
            .iter()
            .map(|(set, ..)| -> Reference {
                let domain: Reference = match (set.infinite, &set.member, &set.reference) {
                    // The test evaluates the operands again as it applies the function, so where
                    // they read a register, TLC's search, or draw (below), what they read may
                    // have changed by then.
                    (Some(_), Some(member), _) => {
                        let member = Arc::clone(member);
                        Arc::new(move |_| Ok(Lazy::Tested(Arc::clone(&member))))
                    }
                    (Some(name), None, _) => Arc::new(move |_| Ok(Lazy::Infinite(name))),
                    (None, _, Some(reference)) => Arc::clone(reference),
                    (None, _, None) if has_non_set_bound => {
                        let set = set.eval.clone();
                        return Arc::new(move |machine| Ok(Lazy::Set(set(machine)?)));
                    }
                    (None, _, None) => {
                        let set = set.eval.clone();
                        return Arc::new(move |machine| {
                            Ok(Lazy::Set(evaluate_set(
                                machine,
                                &set,
                                "a function over a non-set",
                            )?))
                        });
                    }
                };
                // TLC evaluates the domain's parts as it builds the function, so one that fails
                // fails there, applied or not (`FcnParams` holds the values): `Seq(1 \div 0)`,
                // `Nat \ {1 \div 0}` or `SUBSET Seq(S)`, where neither the test nor the reference
                // evaluates S. A filter's predicate stays lazy, as SetPredValue keeps it. Where
                // they may print, set a register or draw, evaluating them again for the reference
                // would do so twice.
                if set.reads_search() {
                    return Arc::new(|_| {
                        Err(Bail(
                            "unsupported: a domain TLC keeps lazy that reads what may change before it is applied",
                        ))
                    });
                }
                let parts = Self::parts_of(set);
                Arc::new(move |machine| {
                    machine.run_parts(&parts)?;
                    domain(machine)
                })
            })
            .collect();
        // The domains are tested when the function is applied, as TLC tests them
        // (`FcnLambdaValue.apply`), with what they read as it was when the function was built.
        let read = Footprint::merge_all(levels_for_lambda.iter().map(|(set, ..)| &set.footprint))
            .merge(&body_footprint);
        let definition = Arc::new(LambdaDefinition {
            levels: levels_for_lambda
                .iter()
                .map(|(_, slots, tuple)| (slots.clone(), *tuple))
                .collect(),
            body: body_for_lambda,
            captured: read
                .slots
                .iter()
                .copied()
                .filter(|slot| !bound.contains(slot) && *slot != super::WARNING_SLOT)
                .collect(),
            vars: read.vars.clone(),
            primes: read.primes.clone(),
            has_effect,
        });
        // `Tool`'s OPCODE_fc builds a function over Reducible sets at once, unless it evaluates
        // it with KeepLazy, as the function of an application, which keeps it a FcnLambdaValue
        // that `FcnLambdaValue.apply` evaluates only at the keys it is applied to, with the
        // application's control. Where this constructor is the function an application evaluates
        // (`Machine::function_value`), the engine builds it too, and where that fails at a key with
        // no effect, keeps it lazy instead, which no cache keeps: TLC evaluates a definition anew
        // where it isn't applied, as `processConstantDefns` kept no value of it. Elsewhere TLC
        // builds it at once, as the body of a function applied with Clear is evaluated. One TLC
        // keeps lazy wherever it is (`is_kept_lazy`) the engine builds too, and keeps lazy where
        // that fails at a key with no effect.
        let construct = {
            let definition = Arc::clone(&definition);
            let construct = Arc::clone(&construct);
            Arc::new(
                move |machine: &mut Machine<'_>, sets: &[Id], is_applied: bool| {
                    if !is_applied && !is_kept_lazy {
                        return construct(machine, sets);
                    }
                    if is_applied && is_effect_kept_lazy {
                        let domains = sets.iter().map(|&set| Lazy::Set(set)).collect();
                        let function = lazy_function::build(machine, &definition, domains)?;
                        machine.kept_lazy_function = function;
                        return Ok(function);
                    }
                    let (output, effects) = (machine.output.len(), machine.effects());
                    match construct(machine, sets) {
                        Err(_)
                            if machine.output.len() == output && machine.effects() == effects =>
                        {
                            let domains = sets.iter().map(|&set| Lazy::Set(set)).collect();
                            let function = lazy_function::build(machine, &definition, domains)?;
                            machine.kept_lazy_function = function;
                            Ok(function)
                        }
                        result => result,
                    }
                },
            )
        };
        self.is_lambda_built |= is_effect_kept_lazy;
        let evaluate = if is_lambda_possible {
            self.is_lambda_built = true;
            eval(move |machine| {
                let is_applied = machine.take_applied_construction(body_node);
                let mut lazy: Vec<Lazy> = Vec::with_capacity(domains.len());
                for (domain, level) in domains.iter().zip(levels.iter()) {
                    let set = match lazy.last() {
                        Some(last) if level.is_shared => last.clone(),
                        _ => domain(machine)?,
                    };
                    lazy.push(set);
                }
                // TLC prints, compares and fingerprints a function it keeps lazy as the one
                // `toFcnRcd` builds over its domain's enumeration, and a \cup, \cap or \ prints
                // as its enumeration too, so over one it enumerates the engine builds that one.
                for set in &lazy {
                    let is_non_set =
                        matches!(set, Lazy::Set(id) if machine.store.kind_of(*id) != KIND_SET);
                    if is_non_set
                        || (is_lazy_domain(set)
                            && !(matches!(set, Lazy::Operation(..))
                                && set.enumerate(machine).is_ok()))
                    {
                        return lazy_function::build(machine, &definition, lazy);
                    }
                }
                // A function TLC builds at once (`toFcnRcd`), over the sets just evaluated.
                let mut sets = Vec::with_capacity(lazy.len());
                for set in &lazy {
                    sets.push(match set {
                        Lazy::Set(id) => expect_set(machine, *id, "a function over a non-set")?,
                        set => {
                            let elements = set.enumerate(machine)?;
                            machine.store.set_of(&elements)?
                        }
                    });
                }
                construct(machine, &sets, is_applied)
            })
        } else {
            let levels = Arc::clone(&levels);
            eval(move |machine| {
                let is_applied = machine.take_applied_construction(body_node);
                let sets =
                    evaluate_bound_sets(machine, &levels, "a function over a non-set", false)?;
                construct(machine, &sets, is_applied)
            })
        };
        Ok(Compiled {
            is_costly: true,
            ..leaf(evaluate, footprint)
        })
    }

    // --- functions ---

    // The bodies of the function constructors whose value an application's function may be,
    // which TLC evaluates there with KeepLazy (`Tool`'s OPCODE_fa): the constructor itself, a
    // branch of an IF or a CASE whose tests evaluate no definition, a definition without
    // parameters or one whose arguments are values, a parameter's or a LET's argument, a
    // function a LET defines, and the value at a key of a constructor itself applied to values,
    // which `FcnLambdaValue.apply` evaluates with that application's control. Nothing evaluates
    // one of these constructors before the one applied: a test or an argument that may is no
    // way through. An EXCEPT of one, with values for its keys and values, is one too.
    pub(super) fn get_applied_constructions(
        &self,
        function: NodeId,
        context: &Context,
    ) -> Option<Arc<[NodeId]>> {
        let mut constructions = Vec::new();
        let within = Within {
            context: Some(context),
            bound: Vec::new(),
        };
        self.collect_applied_constructions(function, &within, &mut constructions, 0);
        (!constructions.is_empty())
            .then(|| constructions.into_iter().map(|(body, _)| body).collect())
    }

    fn collect_applied_constructions(
        &self,
        node: NodeId,
        within: &Within<'_>,
        constructions: &mut Vec<(NodeId, Vec<TextId>)>,
        depth: u32,
    ) {
        if depth > 8 || constructions.len() > 32 {
            return;
        }
        let depth = depth + 1;
        match self.node(node).1 {
            NodeKind::FunctionConstruction {
                is_recursive: false,
                bounds,
                body,
            } => constructions.push((self.node(*body).0, bound_names(bounds))),
            NodeKind::If {
                condition,
                consequent,
                alternative,
            } if self.is_plain(*condition, within) => {
                self.collect_applied_constructions(*consequent, within, constructions, depth);
                self.collect_applied_constructions(*alternative, within, constructions, depth);
            }
            NodeKind::Case { arms, other }
                if arms.iter().all(|&(guard, _)| self.is_plain(guard, within)) =>
            {
                for &(_, arm) in arms {
                    self.collect_applied_constructions(arm, within, constructions, depth);
                }
                if let Some(other) = other {
                    self.collect_applied_constructions(*other, within, constructions, depth);
                }
            }
            NodeKind::Label { body, .. } => {
                self.collect_applied_constructions(*body, within, constructions, depth)
            }
            // `FcnLambdaValue.takeExcept` keeps it lazy.
            NodeKind::Except { function, updates }
                if updates.iter().all(|update| {
                    self.is_plain(update.value, within)
                        && update.path.iter().all(|step| match step {
                            PathStep::Field(_) => true,
                            PathStep::Index(args) => {
                                args.iter().all(|&argument| self.is_plain(argument, within))
                            }
                        })
                }) =>
            {
                self.collect_applied_constructions(*function, within, constructions, depth)
            }
            // The value at a key of a constructor applied to values: its body's, where its bound
            // names are values and other names global.
            NodeKind::FunctionApplication { function, args }
                if args.iter().all(|&argument| self.is_plain(argument, within)) =>
            {
                let mut applied = Vec::new();
                self.collect_applied_constructions(*function, within, &mut applied, depth);
                for (body, bound) in applied {
                    let within = Within {
                        context: None,
                        bound,
                    };
                    self.collect_applied_constructions(body, &within, constructions, depth);
                }
            }
            NodeKind::Identifier(name) if name.is_local => {
                let Some(found) = within
                    .context
                    .and_then(|context| lookup(&context.scope, name.text))
                else {
                    return;
                };
                match &found.binding {
                    Binding::Argument(argument) => {
                        let context = super::argument_context(argument);
                        let within = Within {
                            context: Some(&context),
                            bound: Vec::new(),
                        };
                        self.collect_applied_constructions(
                            argument.expression,
                            &within,
                            constructions,
                            depth,
                        )
                    }
                    Binding::Value {
                        lazy: Some(lazy), ..
                    } => self.collect_function_definition(lazy.definition, constructions),
                    _ => {}
                }
            }
            NodeKind::Identifier(name) => {
                self.collect_definition(name, &[], within, constructions, depth)
            }
            NodeKind::Apply { name, args } if !name.is_local => {
                self.collect_definition(name, args, within, constructions, depth)
            }
            _ => {}
        }
    }

    fn collect_function_definition(
        &self,
        node: NodeId,
        constructions: &mut Vec<(NodeId, Vec<TextId>)>,
    ) {
        let definition = self.definition(node);
        if let tla_ir::DefinitionForm::Function(bounds) = &definition.form
            && definition.flags
                & (tla_ir::Definition::RECURSIVE
                    | tla_ir::Definition::SELF_REFERENTIAL
                    | tla_ir::Definition::SUBSTITUTED)
                == 0
        {
            constructions.push((self.node(definition.body).0, bound_names(bounds)));
        }
    }

    fn collect_definition(
        &self,
        name: &tla_ir::Name,
        args: &[NodeId],
        within: &Within<'_>,
        constructions: &mut Vec<(NodeId, Vec<TextId>)>,
        depth: u32,
    ) {
        let tla_ir::Resolution::Definition(index) = name.resolution else {
            return;
        };
        let node = self.ir.definitions[index as usize];
        let definition = self.definition(node);
        if definition.flags
            & (tla_ir::Definition::RECURSIVE
                | tla_ir::Definition::SELF_REFERENTIAL
                | tla_ir::Definition::SUBSTITUTED)
            != 0
            || !args.iter().all(|&argument| self.is_value(argument, within))
        {
            return;
        }
        match &definition.form {
            tla_ir::DefinitionForm::Function(_) if args.is_empty() => {
                self.collect_function_definition(node, constructions)
            }
            // Its body's names are its parameters, bound to values, or global.
            tla_ir::DefinitionForm::Operator(params) if params.len() == args.len() => {
                let within = Within {
                    context: None,
                    bound: params
                        .iter()
                        .filter(|param| param.arity == 0)
                        .map(|param| param.name)
                        .collect(),
                };
                self.collect_applied_constructions(definition.body, &within, constructions, depth)
            }
            _ => {}
        }
    }

    // A literal, or a name bound to a value: a variable, a constant, a builtin's, or a bound name.
    fn is_value(&self, node: NodeId, within: &Within<'_>) -> bool {
        match self.node(node).1 {
            NodeKind::Number(_) | NodeKind::String(_) => true,
            NodeKind::Identifier(name) if name.is_local => match within.context {
                Some(context) => lookup(&context.scope, name.text)
                    .is_some_and(|found| matches!(found.binding, Binding::Slot(_))),
                None => within.bound.contains(&name.text),
            },
            NodeKind::Identifier(name) => matches!(
                name.resolution,
                tla_ir::Resolution::Variable(_)
                    | tla_ir::Resolution::Constant(_)
                    | tla_ir::Resolution::Builtin(_)
            ),
            _ => false,
        }
    }

    // A domain that evaluates no definition, no constructor and no name but a value, and reads
    // no register, the time or a draw: the same set however often it is evaluated.
    pub(super) fn is_fixed_domain(&self, node: NodeId, context: &Context) -> bool {
        let within = Within {
            context: Some(context),
            bound: Vec::new(),
        };
        self.is_plain(node, &within) && self.reads_nothing_changing(node)
    }

    fn reads_nothing_changing(&self, node: NodeId) -> bool {
        let kind = self.node(node).1;
        if let NodeKind::Identifier(name) | NodeKind::Apply { name, .. } = kind
            && let tla_ir::Resolution::Builtin(index) = name.resolution
            && !matches!(
                self.builtin_name(index),
                "Nat"
                    | "Int"
                    | "BOOLEAN"
                    | "STRING"
                    | ".."
                    | "SUBSET"
                    | "UNION"
                    | "\\cup"
                    | "\\cap"
                    | "\\"
                    | "+"
                    | "-"
                    | "*"
                    | "-."
                    | "Seq"
            )
        {
            return false;
        }
        kind.children()
            .into_iter()
            .all(|child| self.reads_nothing_changing(child))
    }

    // An expression that evaluates no definition, no constructor, and no name but a value.
    fn is_plain(&self, node: NodeId, within: &Within<'_>) -> bool {
        match self.node(node).1 {
            NodeKind::Number(_) | NodeKind::String(_) => true,
            NodeKind::Identifier(_) => self.is_value(node, within),
            NodeKind::Apply { name, args } if !name.is_local => {
                matches!(name.resolution, tla_ir::Resolution::Builtin(_))
                    && args.iter().all(|&argument| self.is_plain(argument, within))
            }
            NodeKind::SetEnumeration(elements) | NodeKind::Tuple(elements) => elements
                .iter()
                .all(|&element| self.is_plain(element, within)),
            NodeKind::Record(fields) => fields
                .iter()
                .all(|&(_, value)| self.is_plain(value, within)),
            _ => false,
        }
    }

    fn compile_function_application(
        &mut self,
        function: NodeId,
        args: &[NodeId],
        context: &Context,
    ) -> Compiling<Compiled> {
        if let NodeKind::FunctionApplication {
            function: applied,
            args: applied_args,
        } = self.node(function).1
            && let Some(recursive) = self.get_applied_recursive_function(*applied, context)?
            && let Some(element) = recursive.element
            && (applied_args.len() == 1 || applied_args.len() == recursive.arity)
        {
            if recursive.converted.is_some() {
                return unsupported(
                    "a recursive function TLC keeps lazy, of a function constructor",
                );
            }
            let applied_args = applied_args
                .iter()
                .map(|&argument| self.compile(argument, context))
                .collect::<Compiling<Vec<Compiled>>>()?;
            let args = args
                .iter()
                .map(|&argument| self.compile(argument, context))
                .collect::<Compiling<Vec<Compiled>>>()?;
            let footprint = Footprint::merge_all(
                applied_args
                    .iter()
                    .chain(&args)
                    .map(|argument| &argument.footprint),
            )
            .merge(&recursive.footprint());
            let recursive = (recursive.runtime, recursive.slot);
            let applied_args: Vec<Eval> = applied_args
                .into_iter()
                .map(|argument| argument.eval)
                .collect();
            let args: Vec<Eval> = args.into_iter().map(|argument| argument.eval).collect();
            return Ok(leaf(
                eval(move |machine| {
                    let argument = match &applied_args[..] {
                        [argument] => argument(machine)?,
                        evaluators => evaluate_tuple(machine, evaluators)?,
                    };
                    let domain = machine.recursive_domain(recursive.0);
                    if !domain(machine, argument)? {
                        return Err(Bail("applied a recursive function outside its domain"));
                    }
                    let key = match &args[..] {
                        [argument] => argument(machine)?,
                        evaluators => evaluate_tuple(machine, evaluators)?,
                    };
                    call_recursive_element(machine, recursive.1, element, argument, key)
                }),
                footprint,
            ));
        }
        if let Some(recursive) = self.get_applied_recursive_function(function, context)?
            && (args.len() == 1 || args.len() == recursive.arity)
        {
            // f[a, b] applies f to the tuple <<a, b>>.
            let args = args
                .iter()
                .map(|&argument| self.compile(argument, context))
                .collect::<Compiling<Vec<Compiled>>>()?;
            let footprint = Footprint::merge_all(args.iter().map(|argument| &argument.footprint))
                .merge(&recursive.footprint());
            let (runtime, slot) = (recursive.runtime, recursive.slot);
            let converted = recursive.converted;
            let evaluators: Vec<Eval> = args.into_iter().map(|argument| argument.eval).collect();
            return Ok(leaf(
                eval(move |machine| {
                    let value = match &evaluators[..] {
                        [argument] => argument(machine)?,
                        evaluators => evaluate_tuple(machine, evaluators)?,
                    };
                    // One TLC keeps lazy as it starts it applies as the function it converted
                    // to, once it converted it (`FcnLambdaValue.apply`'s `fcnRcd`), and before
                    // that evaluates its body anew, which prints only as TLC starts.
                    if let Some(once) = converted {
                        let function = machine.onces[once];
                        if function != crate::memo::EMPTY {
                            return lazy_function::apply(machine, function, value);
                        }
                        if !machine.is_starting {
                            return Err(Bail(super::KEPT_LAZY_AFTER_STARTUP));
                        }
                    }
                    call_recursive_function(machine, runtime, slot, value)
                }),
                footprint,
            ));
        }
        // `Tool.evalAppl` evaluates the function of an application with `EvalControl.KeepLazy`,
        // so TestRandomSetOfSubsets's function constructor stays a `FcnLambdaValue`, which
        // draws once, for the key applied.
        if self.is_test_draws(function)
            && let NodeKind::Apply { name, args: drawn } = self.node(function).1
            && let tla_ir::Resolution::Builtin(index) = name.resolution
            && let [key] = args
        {
            let operands: Vec<(NodeId, Context)> =
                drawn.iter().map(|&node| (node, context.clone())).collect();
            return self.compile_test_random_set_of_subsets(index, &operands, context, Some(*key));
        }
        let construction = self.get_applied_constructions(function, context);
        let within = Within {
            context: Some(context),
            bound: Vec::new(),
        };
        let is_applied_to_values = args
            .iter()
            .all(|&argument| self.is_plain(argument, &within));
        let applied = self.applied_lazily(function, context);
        let outer = std::mem::replace(&mut self.applied_construction, applied);
        let function_node = function;
        let function = self.compile(function, context);
        self.applied_construction = outer;
        let mut function = function?;
        let evaluate_function = function.eval.clone();
        // An argument or a LET definition holding a function constructor whose records TLC may
        // print as written, read here with KeepLazy: the value read is noted, which a later print
        // of it declines (`push_prints`).
        let notes_records = matches!(self.node(function_node).1,
            NodeKind::Identifier(name) if name.is_local)
            && self.names_argument_with_written_records(function_node, context, 0);
        function.eval = eval(move |machine| {
            let value = machine.function_value(
                &evaluate_function,
                construction.as_ref(),
                is_applied_to_values,
            )?;
            if notes_records && machine.last_kept_lazy_record != value {
                machine.last_kept_lazy_record = value;
                machine.kept_lazy_records.insert(value);
            }
            Ok(value)
        });
        let args = args
            .iter()
            .map(|&argument| self.compile(argument, context))
            .collect::<Compiling<Vec<Compiled>>>()?;
        let footprint = Footprint::merge_all(
            [&function.footprint]
                .into_iter()
                .chain(args.iter().map(|argument| &argument.footprint)),
        );
        // TLC fails on a value that isn't a function, and on a tuple or a record of several
        // arguments, before it evaluates the argument (`Tool`'s OPCODE_fa), which shows where the
        // argument prints. The store doesn't tell a record from a function TLC built of strings.
        let is_printing = args.iter().any(Compiled::is_printing);
        if let [argument] = &args[..]
            && !is_printing
        {
            return Ok(super::fused::apply(&function, argument, footprint));
        }
        let is_several = args.len() > 1;
        let evaluators: Vec<Eval> = args.iter().map(|argument| argument.eval.clone()).collect();
        let function = function.eval;
        Ok(leaf(
            eval(move |machine| {
                let value = function(machine)?;
                if is_printing {
                    check_applied(machine, value, is_several)?;
                }
                let key = match &evaluators[..] {
                    [argument] => argument(machine)?,
                    evaluators => evaluate_tuple(machine, evaluators)?,
                };
                lazy_function::apply(machine, value, key)
            }),
            footprint,
        ))
    }

    fn compile_except(
        &mut self,
        function: NodeId,
        updates: &[Update],
        context: &Context,
    ) -> Compiling<Compiled> {
        let warning = self.ir.model.is_warning_enabled.then_some(function);
        self.is_warning |= warning.is_some();
        let function = self.compile(function, context)?;
        let at = self.at;
        let mut compiled = Vec::new();
        for update in updates {
            let mut path = Vec::new();
            for step in &update.path {
                path.push(match step {
                    PathStep::Field(name) => {
                        let units = self.units(*name);
                        constant(self.store.str(&units))
                    }
                    PathStep::Index(args) => {
                        let args = args
                            .iter()
                            .map(|&argument| self.compile(argument, context))
                            .collect::<Compiling<Vec<Compiled>>>()?;
                        if let [argument] = &args[..] {
                            argument.clone()
                        } else {
                            let evaluators: Vec<Eval> =
                                args.iter().map(|argument| argument.eval.clone()).collect();
                            leaf(
                                eval(move |machine| evaluate_tuple(machine, &evaluators)),
                                Footprint::merge_all(
                                    args.iter().map(|argument| &argument.footprint),
                                ),
                            )
                        }
                    }
                });
            }
            let at_slot = self.allocate_slot();
            let value_context =
                context.with_scope(bind(&context.scope, at, Binding::Slot(at_slot)));
            let value = self.compile(update.value, &value_context)?;
            let uses_at = value.footprint.slots.contains(&at_slot);
            compiled.push((path, at_slot, value, uses_at));
        }
        let footprint = Footprint::merge_all(
            [function.footprint.clone()]
                .into_iter()
                .chain(compiled.iter().flat_map(|(path, at_slot, value, _)| {
                    path.iter()
                        .map(|step| step.footprint.clone())
                        .chain([value.footprint.without_slots(&[*at_slot])])
                        .collect::<Vec<_>>()
                }))
                .collect::<Vec<_>>()
                .iter(),
        );
        let footprint = if warning.is_some() {
            footprint.merge(&Footprint::slot(super::WARNING_SLOT))
        } else {
            footprint
        };
        let base = function.eval.clone();
        let evaluate = if compiled.iter().all(|(path, ..)| path.len() == 1) {
            // Each update names one key, as [f EXCEPT ![k] = v] and [r EXCEPT !.a = v] do.
            let flat: Vec<(Eval, Eval, Option<u32>)> = compiled
                .iter()
                .map(|(path, at_slot, value, uses_at)| {
                    (
                        path[0].eval.clone(),
                        value.eval.clone(),
                        uses_at.then_some(*at_slot),
                    )
                })
                .collect();
            if flat.len() > 1 {
                except_many(base, flat, warning)
            } else if let (Shape::Current(variable), [(key, value, None)]) =
                (function.shape, &flat[..])
            {
                super::fused::except_var_at(variable, key.clone(), value.clone(), warning)
            } else {
                except_flat(base, flat, warning)
            }
        } else {
            let updates: Vec<(Vec<Eval>, u32, Eval)> = compiled
                .iter()
                .map(|(path, at_slot, value, _)| {
                    (
                        path.iter().map(|step| step.eval.clone()).collect(),
                        *at_slot,
                        value.eval.clone(),
                    )
                })
                .collect();
            except_nested(base, updates, warning)
        };
        // TLC takes an EXCEPT of a FcnLambdaValue as another, so that of a function the engine
        // keeps lazy where building it failed is one no cache keeps either.
        let evaluate = eval(move |machine| {
            let kept = machine.kept_lazy_function;
            let value = evaluate(machine)?;
            if machine.kept_lazy_function != kept {
                machine.kept_lazy_function = value;
            }
            Ok(value)
        });
        Ok(Compiled {
            is_costly: true,
            ..leaf(evaluate, footprint)
        })
    }

    // {e1, ..., en} of elements already compiled.
    pub(crate) fn compile_set_enumeration(elements: &[Compiled]) -> Compiled {
        if elements.is_empty() {
            return Compiled {
                is_enumerated: true,
                are_elements_enumerated: true,
                is_in_order: true,
                are_elements_in_order: true,
                are_elements_of_elements_in_order: true,
                ..constant(EMPTY_SET)
            };
        }
        // TLC holds Nat, Int or STRING as an element, where the engine otherwise only tests it.
        let evaluators: Vec<Eval> = elements
            .iter()
            .map(|element| match element.infinite_value {
                Some(name) => eval(move |machine| Ok(machine.store.infinite_set(name))),
                None => element.eval.clone(),
            })
            .collect();
        let held = evaluators.clone();
        let reference = Arc::new(move |machine: &mut Machine<'_>| {
            let at = push_all(machine, &held)?;
            let values = machine.stack.split_off(at);
            if values.iter().any(|value| machine.store.holds_any(*value)) {
                Ok(Lazy::Enumeration(
                    values.into_iter().map(Lazy::Set).collect(),
                ))
            } else {
                Ok(Lazy::Set(machine.store.set_of(&values)?))
            }
        });
        let are_elements_in_order = elements.iter().all(|element| element.is_in_order);
        // TLC holds an element it keeps lazy as built, which a UNION of the set streams.
        let element_references = (!are_elements_in_order
            && !elements.iter().any(Compiled::may_be_infinite))
        .then(|| {
            // An element not known to stream in order streams as its reference says where that is
            // exact, which a variable's the initial predicate assigned isn't.
            elements
                .iter()
                .map(|element| {
                    if element.is_in_order {
                        reference_of(element)
                    } else {
                        element
                            .reference
                            .clone()
                            .filter(|_| element.is_reference_exact)
                    }
                })
                .collect::<Option<Vec<_>>>()
        })
        .flatten();
        Compiled {
            is_costly: true,
            reference: Some(reference),
            is_reference_exact: true,
            is_enumerated: true,
            are_elements_enumerated: elements.iter().all(|element| element.is_enumerated),
            is_in_order: true,
            are_elements_in_order,
            are_elements_of_elements_in_order: elements
                .iter()
                .all(|element| element.are_elements_in_order),
            element_references,
            unsorted_first: elements
                .first()
                .filter(|first| !first.is_normalized)
                .map(|first| (first.eval.clone(), first.reference.clone())),
            ..leaf(
                eval(move |machine| {
                    let at = push_all(machine, &evaluators)?;
                    let values = machine.stack.split_off(at);
                    machine.store.set_of(&values).map_err(|error| {
                        if values.iter().any(|value| machine.store.holds_any(*value)) {
                            Bail("unsupported: eagerly normalizing a set containing ANY")
                        } else {
                            error
                        }
                    })
                }),
                Footprint::merge_all(elements.iter().map(|element| &element.footprint)),
            )
        }
    }
}

pub(crate) fn field_of(
    machine: &mut Machine<'_>,
    record: Id,
    key: Id,
    hint: &AtomicU32,
) -> Outcome<Id> {
    let hinted = hint.load(Ordering::Relaxed);
    let mut position = hinted;
    let value = machine.store.apply_field(record, key, &mut position);
    // Threads share the hint, so it is written only when it changes: a write on every read would
    // move its cache line between them.
    if position != hinted {
        hint.store(position, Ordering::Relaxed);
    }
    value
}

// `Tool.contexts`: the set of each bound once, in the order written, and the set `a, b \in S`
// shares once for both, before any name is bound. A quantifier and a set map take each in
// normalized order (`is_normalized`), where a function's constructor walks its domain as built
// (`FcnLambdaValue`).
fn evaluate_bound_sets(
    machine: &mut Machine<'_>,
    levels: &[Level],
    reason: &'static str,
    is_normalized: bool,
) -> Outcome<Vec<Id>> {
    let mut sets: Vec<Id> = Vec::with_capacity(levels.len());
    for level in levels {
        let set = match sets.last() {
            Some(&last) if level.is_shared => last,
            _ => {
                let set = evaluate_set(machine, &level.set.eval, reason)?;
                if is_normalized {
                    let size = machine.store.size_of(set);
                    level.set.check_enumerated(machine, set, size)?;
                }
                set
            }
        };
        sets.push(set);
    }
    Ok(sets)
}

// The bindings of several bounds in TLC's order (`ContextEnumerator`, `FcnParams.Enumerator`),
// the first bound varying fastest, until `visit` says to stop: whether it visited them all.
fn for_each_binding(
    machine: &mut Machine<'_>,
    levels: &[Level],
    sets: &[Id],
    mut visit: impl FnMut(&mut Machine<'_>, &[Id]) -> Outcome<bool>,
) -> Outcome<bool> {
    if sets.iter().any(|&set| machine.store.size_of(set) == 0) {
        return Ok(true);
    }
    let mut positions = vec![0; sets.len()];
    let mut current: Vec<Id> = sets
        .iter()
        .map(|&set| machine.store.element_at(set, 0))
        .collect();
    loop {
        for (level, &element) in levels.iter().zip(&current) {
            assign_bound(machine, &level.slots, level.tuple, element)?;
        }
        if !visit(machine, &current)? {
            return Ok(false);
        }
        let mut level = 0;
        loop {
            let Some(&set) = sets.get(level) else {
                return Ok(true);
            };
            positions[level] += 1;
            if positions[level] < machine.store.size_of(set) {
                current[level] = machine.store.element_at(set, positions[level]);
                break;
            }
            positions[level] = 0;
            current[level] = machine.store.element_at(set, 0);
            level += 1;
        }
    }
}

// Fails where TLC fails applying a value before it evaluates the argument: one that isn't a
// function, or, of several arguments, a tuple, or a function of strings, which may be a record.
fn check_applied(machine: &mut Machine<'_>, function: Id, is_several: bool) -> Outcome<()> {
    let kind = machine.store.kind_of(function);
    if kind == KIND_LAZY_FUNCTION {
        return Ok(());
    }
    if !is_function_kind(kind) {
        return Err(Bail("applied a non-function"));
    }
    if is_several
        && (kind == KIND_TUPLE
            || (0..machine.store.size_of(function)).all(|index| {
                let key = machine.store.get_key(function, index);
                machine.store.kind_of(key) == KIND_STRING
            }))
    {
        return Err(Bail(
            "unsupported: a tuple or a record of several arguments that print",
        ));
    }
    Ok(())
}

fn quantify(
    machine: &mut Machine<'_>,
    levels: &[Level],
    body: &Test,
    reject: Option<&Reject>,
    is_forall: bool,
) -> Outcome<bool> {
    if let [level] = levels {
        let set = evaluate_set(machine, &level.set.eval, "quantified over a non-set")?;
        let size = machine.store.size_of(set);
        level.set.check_enumerated(machine, set, size)?;
        for index in 0..size {
            let element = machine.store.element_at(set, index);
            if let Some(reject) = reject
                && reject.rejects(machine, element)
            {
                if is_forall {
                    return Ok(false);
                }
                continue;
            }
            assign_bound(machine, &level.slots, level.tuple, element)?;
            if body(machine)? != is_forall {
                return Ok(!is_forall);
            }
        }
        return Ok(is_forall);
    }
    let sets = evaluate_bound_sets(machine, levels, "quantified over a non-set", true)?;
    let is_undecided = for_each_binding(machine, levels, &sets, |machine, _| {
        Ok(body(machine)? == is_forall)
    })?;
    Ok(if is_undecided { is_forall } else { !is_forall })
}

// Pushes the images on the stack, above whatever evaluating them pushes and pops.
fn map_images(machine: &mut Machine<'_>, levels: &[Level], body: &Eval) -> Outcome<()> {
    let sets = evaluate_bound_sets(machine, levels, "mapped a non-set", true)?;
    let at = machine.stack.len();
    for_each_binding(machine, levels, &sets, |machine, _| {
        let image = body(machine)?;
        check_set_insertion(machine.stack.len() - at)?;
        machine.stack.push(image);
        Ok(true)
    })?;
    Ok(())
}

// Whether an element passes a filter's predicate, its names bound to it and then restored.
fn test_element(machine: &mut Machine<'_>, filter: &Filter, element: Id) -> Outcome<bool> {
    let saved: Vec<Id> = filter
        .slots
        .iter()
        .map(|&slot| machine.locals[slot as usize])
        .collect();
    let kept = assign_converted(machine, &filter.slots, filter.tuple, element)
        .and_then(|()| (filter.predicate)(machine));
    for (&slot, &value) in filter.slots.iter().zip(&saved) {
        machine.locals[slot as usize] = value;
    }
    kept
}

// Several updates write one new function: each key's position is the same in every intermediate
// function, and @ reads the value an earlier update gave the key, if any.
fn except_many(
    base: Eval,
    updates: Vec<(Eval, Eval, Option<u32>)>,
    warning: Option<NodeId>,
) -> Eval {
    eval(move |machine| {
        let function = base(machine)?;
        if lazy_function::is_lazy(machine, function) {
            return except_each(machine, function, &updates, warning);
        }
        let mut positions = Vec::with_capacity(updates.len());
        let mut values = Vec::with_capacity(updates.len());
        for (key, value, at_slot) in &updates {
            let key = key(machine)?;
            if !is_function_kind(machine.store.kind_of(function)) {
                return Err(Bail("EXCEPT on a non-function"));
            }
            let position = match machine.store.find_key(function, key)? {
                -1 => {
                    check_missing_except_key(machine, function, key)?;
                    except_warning(machine, warning)?;
                    continue;
                }
                position => position as u32,
            };
            if let Some(at_slot) = at_slot {
                let mut old = machine.store.get_range_value(function, position);
                for earlier in 0..positions.len() {
                    if positions[earlier] == position {
                        old = values[earlier];
                    }
                }
                machine.locals[*at_slot as usize] = old;
            }
            positions.push(position);
            values.push(value(machine)?);
        }
        Ok(machine.store.except_at(function, &positions, &values))
    })
}

fn except_flat(
    base: Eval,
    updates: Vec<(Eval, Eval, Option<u32>)>,
    warning: Option<NodeId>,
) -> Eval {
    eval(move |machine| {
        let function = base(machine)?;
        except_each(machine, function, &updates, warning)
    })
}

fn except_each(
    machine: &mut Machine<'_>,
    function: Id,
    updates: &[(Eval, Eval, Option<u32>)],
    warning: Option<NodeId>,
) -> Outcome<Id> {
    let mut result = function;
    for (key, value, at_slot) in updates {
        let key = key(machine)?;
        let Some(old) = select_except(machine, result, key)? else {
            except_warning(machine, warning)?;
            continue;
        };
        if let Some(at_slot) = at_slot {
            machine.locals[*at_slot as usize] = old;
        }
        let value = value(machine)?;
        result = lazy_function::except(machine, result, key, value)?;
    }
    Ok(result)
}

// `Value.select`: unlike apply, an absent key is not an error.
pub(super) fn select_except(
    machine: &mut Machine<'_>,
    function: Id,
    key: Id,
) -> Outcome<Option<Id>> {
    if lazy_function::is_lazy(machine, function) {
        if !lazy_function::is_in_domain(machine, function, key)? {
            return Ok(None);
        }
        return lazy_function::apply(machine, function, key).map(Some);
    }
    if !is_function_kind(machine.store.kind_of(function)) {
        return Err(Bail("EXCEPT on a non-function"));
    }
    match machine.store.find_key(function, key)? {
        -1 => {
            check_missing_except_key(machine, function, key)?;
            Ok(None)
        }
        position => Ok(Some(
            machine.store.get_range_value(function, position as u32),
        )),
    }
}

/// What an EXCEPT stops with at a key of a class the record's or the tuple's keys can't be, which
/// TLC's `select` fails on (or warns of, in `takeExcept`), for the evaluator of failures to word.
pub(crate) const EXCEPT_INCOMPATIBLE_KEY: &str = "EXCEPT with an incompatible key";

// A missing id does not prove `select` returned null: TLC first checks the key's class,
// and FcnRcdValue's linear search compares keys with equals rather than their interned ids.
fn check_missing_except_key(machine: &mut Machine<'_>, function: Id, key: Id) -> Outcome<()> {
    let store = &mut machine.store;
    if store.kind_of(function) == KIND_TUPLE && store.kind_of(key) != KIND_INT
        || store.is_record(function) && store.kind_of(key) != KIND_STRING
    {
        return Err(Bail(EXCEPT_INCOMPATIBLE_KEY));
    }
    for index in 0..store.size_of(function) {
        let domain = store.get_key(function, index);
        store.equals(domain, key)?;
    }
    Ok(())
}

pub(super) fn except_warning(machine: &mut Machine<'_>, warning: Option<NodeId>) -> Outcome<()> {
    if let Some(node) = warning {
        if machine.guarding_function_body_warnings {
            return Err(Bail(super::LAZY_FUNCTION_WARNING));
        }
        if machine.guarding_atom_warnings {
            return Err(Bail(super::ATOM_WARNING));
        }
        machine
            .output
            .push(Printed::Warning(RuntimeWarning::Except { node }));
    }
    Ok(())
}

// Each update walks its path down, keeping each key and the function it indexes, then writes the
// new values back up.
fn except_nested(
    base: Eval,
    updates: Vec<(Vec<Eval>, u32, Eval)>,
    warning: Option<NodeId>,
) -> Eval {
    eval(move |machine| {
        let mut result = base(machine)?;
        'updates: for (steps, at_slot, value) in &updates {
            let mut keys = Vec::with_capacity(steps.len());
            for step in steps {
                keys.push(step(machine)?);
            }
            let mut functions = Vec::with_capacity(steps.len());
            let mut current = result;
            for &key in &keys {
                functions.push(current);
                let Some(selected) = select_except(machine, current, key)? else {
                    except_warning(machine, warning)?;
                    continue 'updates;
                };
                current = selected;
            }
            machine.locals[*at_slot as usize] = current;
            let mut value = value(machine)?;
            for (function, key) in functions.iter().zip(&keys).rev() {
                value = lazy_function::except(machine, *function, *key, value)?;
            }
            result = value;
        }
        Ok(result)
    })
}

// `CHOOSE s \in SUBSET S : P` over the k-element subsets of S for each k from 0 in turn, each
// size's in the lexicographic order of the positions of their elements in S, the normalized
// order TLC enumerates a power set in (`SubsetValue.elementsNormalized`).
fn choose_subset(
    machine: &mut Machine<'_>,
    base: Id,
    slots: &[u32],
    tuple: bool,
    body: &Eval,
) -> Outcome<Id> {
    let elements = machine.store.set_elements(base).to_vec();
    let n = elements.len();
    for k in 0..=n {
        let mut indices: Vec<usize> = (0..k).collect();
        loop {
            let subset: Vec<Id> = indices.iter().map(|&index| elements[index]).collect();
            let subset = machine.store.set_of_sorted(&subset);
            assign_converted(machine, slots, tuple, subset)?;
            if body(machine)? == TRUE {
                return Ok(subset);
            }
            // The next positions: the last that can move on moves, and those after it follow.
            let Some(last) = (0..k).rev().find(|&i| indices[i] < n - k + i) else {
                break;
            };
            indices[last] += 1;
            for i in last + 1..k {
                indices[i] = indices[i - 1] + 1;
            }
        }
    }
    Err(Bail("CHOOSE found no element"))
}
