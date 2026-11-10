//! The expression kinds of `compileNode`, each as `compile.ts` compiles it.

use std::sync::Arc;
use std::sync::atomic::{AtomicU32, Ordering};

use tla_ir::{Bound, NodeId, NodeKind, PathStep, Pattern, Update};
use tla_values::store::{
    EMPTY_SET, EMPTY_TUPLE, KIND_SET, KIND_TUPLE, Outcome, TRUE, is_function_kind,
};
use tla_values::{Bail, Id};

use super::lazy::{self, Lazy, Reference};
use super::lazy_function::{self, LambdaDefinition, is_lazy_domain};
use super::predicate::{Predicate, Test};
use super::{
    Binding, Compiled, Compiler, Compiling, Context, Filter, Shape, bind, bool_id,
    call_recursive_element, call_recursive_function, combine_references, constant, eval, leaf,
    lookup, member, predicate_node, reference_of, unsupported,
};
use crate::footprint::Footprint;
use crate::machine::{Eval, Machine};

/// A bound's names, at fresh slots: one name, or a tuple pattern's.
pub(crate) struct Binder {
    pub context: Context,
    pub slots: Vec<u32>,
    pub tuple: bool,
}

pub(crate) fn assign_bound(
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
struct Level {
    set: Compiled,
    slots: Vec<u32>,
    tuple: bool,
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
                let inner = self.bind_let_definitions(definitions, *body, context)?;
                self.compile(*body, &inner)
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
            NodeKind::SetEnumeration(elements) => {
                let elements = elements
                    .iter()
                    .map(|&element| self.compile(element, context))
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
                    .map(|&element| self.compile(element, context))
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
                    compiled.push((key, self.compile(value, context)?));
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
                self.compile_function_application(*function, args, context)
            }
            NodeKind::FieldAccess { record, field } => {
                let record = self.compile(*record, context)?;
                let units = self.units(*field);
                let key = self.store.str(&units);
                let hint = Arc::new(AtomicU32::new(0));
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
        Ok(leaf(
            // TLC evaluates the current state's side first (Tool.evalAppl's OPCODE_unchanged).
            eval(move |machine| {
                let now = now(machine)?;
                let next = next(machine)?;
                Ok(bool_id(machine.store.equals(now, next)?))
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

    fn compile_levels(
        &mut self,
        bounds: &[Bound],
        context: &Context,
    ) -> Compiling<(Vec<Level>, Vec<u32>, Context)> {
        let mut inner = context.clone();
        let mut levels = Vec::new();
        let mut bound = Vec::new();
        for item in bounds {
            let set = self.compile(item.set, &inner)?;
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
            });
        }
        Ok((levels, bound, inner))
    }

    // TLC evaluates the set of every bound before it binds any (`Tool.contexts`), so a later
    // bound's set fails though an earlier one is empty: what evaluates the later sets first.
    fn compile_later_bounds(levels: &[Level], reason: &'static str) -> Compiling<Eval> {
        let mut sets = Vec::new();
        for level in levels.iter().skip(1) {
            if level.set.is_printing() {
                return unsupported("Print in the set of a later bound");
            }
            match &level.set.interval {
                Some((low, high)) => sets.extend([(low.clone(), false), (high.clone(), false)]),
                None => sets.push((level.set.eval.clone(), true)),
            }
        }
        Ok(eval(move |machine| {
            for (set, is_set) in &sets {
                let id = set(machine)?;
                if *is_set {
                    expect_set(machine, id, reason)?;
                }
            }
            Ok(TRUE)
        }))
    }

    fn compile_quantifier(
        &mut self,
        bounds: &[Bound],
        body: NodeId,
        is_forall: bool,
        context: &Context,
    ) -> Compiling<Compiled> {
        let (levels, bound, inner) = self.compile_levels(bounds, context)?;
        let body = self.compile(body, &inner)?;
        let footprint = Footprint::merge_all(levels.iter().map(|level| &level.set.footprint))
            .merge(&body.footprint.without_slots(&bound));
        // A body that prints is evaluated for each element in the order TLC enumerates the set
        // (`Tool.contexts`), until one decides the quantifier.
        if body.is_printing() {
            let [level] = &levels[..] else {
                return unsupported("Print under a quantifier of several bounds");
            };
            let ordered = self.order(level.set.clone(), bounds[0].set, context, false)?;
            let (slots, tuple, body) = (level.slots.clone(), level.tuple, body.eval);
            return Ok(Compiled {
                is_costly: true,
                is_boolean: true,
                ..leaf(
                    eval(move |machine| {
                        let id = (ordered.eval)(machine)?;
                        for position in 0..ordered.size(machine, id)? {
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
        let later_bounds = Self::compile_later_bounds(&levels, "quantified over a non-set")?;
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
                    .map(|level| (level.slots[0], level.set.interval.clone().unwrap()))
                    .collect(),
                predicate,
                is_forall,
            )
        } else {
            let levels: Arc<Vec<(Eval, Vec<u32>, bool)>> = Arc::new(
                levels
                    .into_iter()
                    .map(|level| (level.set.eval, level.slots, level.tuple))
                    .collect(),
            );
            let body = predicate.build();
            eval(move |machine| quantify(machine, &levels, 0, &body, is_forall).map(bool_id))
        };
        Ok(Compiled {
            is_costly: true,
            is_boolean: true,
            ..leaf(
                eval(move |machine| {
                    later_bounds(machine)?;
                    evaluate(machine)
                }),
                footprint,
            )
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
        let (set, body, slots, tuple) = (set.eval, body.eval, binder.slots, binder.tuple);
        Ok(Compiled {
            is_costly: true,
            ..leaf(
                eval(move |machine| {
                    let id = evaluate_set(machine, &set, "CHOOSE from a non-set")?;
                    for index in 0..machine.store.size_of(id) {
                        let element = machine.store.element_at(id, index);
                        assign_bound(machine, &slots, tuple, element)?;
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
        let predicate = self.compile(predicate, &binder.context)?;
        let footprint = set
            .footprint
            .merge(&predicate.footprint.without_slots(&binder.slots));
        let filter = Arc::new(Filter {
            set: set.eval.clone(),
            slots: binder.slots,
            tuple: binder.tuple,
            predicate: Predicate::of(&predicate).build(),
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
            are_elements_enumerated: set.are_elements_enumerated,
            is_in_order: set.is_in_order,
            are_elements_in_order: set.are_elements_in_order,
            filter: Some(filter),
            ..leaf(
                eval(move |machine| {
                    let id = evaluate_set(machine, &parts.set, "filtered a non-set")?;
                    let size = machine.store.size_of(id);
                    let at = machine.stack.len();
                    for index in 0..size {
                        let element = machine.store.element_at(id, index);
                        let kept = assign_bound(machine, &parts.slots, parts.tuple, element)
                            .and_then(|()| (parts.predicate)(machine));
                        match kept {
                            Ok(true) => machine.stack.push(element),
                            Ok(false) => {}
                            Err(bail) => {
                                machine.stack.truncate(at);
                                return Err(bail);
                            }
                        }
                    }
                    let kept = machine.stack.split_off(at);
                    Ok(if kept.len() == size as usize {
                        id
                    } else {
                        machine.store.set_of_sorted(&kept)
                    })
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
        let (levels, bound, inner) = self.compile_levels(bounds, context)?;
        let body = self.compile(expression, &inner)?;
        let footprint = Footprint::merge_all(levels.iter().map(|level| &level.set.footprint))
            .merge(&body.footprint.without_slots(&bound));
        let are_elements_enumerated = body.is_enumerated;
        let are_elements_in_order = body.is_in_order;
        let later_bounds = Self::compile_later_bounds(&levels, "mapped a non-set")?;
        let levels: Arc<Vec<(Eval, Vec<u32>, bool)>> = Arc::new(
            levels
                .into_iter()
                .map(|level| (level.set.eval, level.slots, level.tuple))
                .collect(),
        );
        let body = body.eval;
        Ok(Compiled {
            is_costly: true,
            is_enumerated: true,
            are_elements_enumerated,
            is_in_order: true,
            are_elements_in_order,
            ..leaf(
                eval(move |machine| {
                    later_bounds(machine)?;
                    let at = machine.stack.len();
                    let result = map_images(machine, &levels, 0, &body);
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
        let (levels, bound, inner) = self.compile_levels(bounds, context)?;
        let body = self.compile(body, &inner)?;
        let footprint = Footprint::merge_all(levels.iter().map(|level| &level.set.footprint))
            .merge(&body.footprint.without_slots(&bound));
        let body_footprint = body.footprint.clone();
        let body = body.eval;
        let body_for_lambda = body.clone();
        let levels_for_lambda: Vec<(Compiled, Vec<u32>, bool)> = levels
            .iter()
            .map(|level| (level.set.clone(), level.slots.clone(), level.tuple))
            .collect();
        // A function of one bound, a tuple pattern included, takes each element of its set.
        let evaluate = if let [Level { set, slots, tuple }] = &levels[..] {
            let (set, slots, tuple) = (set.eval.clone(), slots.clone(), *tuple);
            eval(move |machine| {
                let set = evaluate_set(machine, &set, "a function over a non-set")?;
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
                Ok(machine.store.function_over_set(set, &values))
            })
        } else {
            // A function of several arguments takes tuples, in TLC's order of the product.
            let levels: Arc<Vec<Level>> = Arc::new(levels);
            eval(move |machine| {
                let mut sets = Vec::with_capacity(levels.len());
                for level in levels.iter() {
                    sets.push(evaluate_set(
                        machine,
                        &level.set.eval,
                        "a function over a non-set",
                    )?);
                }
                let mut keys = Vec::new();
                let mut values = Vec::new();
                let mut current = vec![0; levels.len()];
                construct_product(
                    machine,
                    &levels,
                    &sets,
                    0,
                    &mut current,
                    &body,
                    &mut keys,
                    &mut values,
                )?;
                machine.store.function_of(&keys, &values)
            })
        };
        // TLC keeps a function lazy where it can't enumerate a bound's set
        // (`FcnLambdaValue`), as it can't Nat.
        let is_lambda_possible = levels_for_lambda
            .iter()
            .any(|(set, ..)| set.may_be_infinite());
        let domains: Vec<(Option<&'static str>, Option<Reference>, Eval)> = levels_for_lambda
            .iter()
            .map(|(set, ..)| (set.infinite, set.reference.clone(), set.eval.clone()))
            .collect();
        let evaluate = if is_lambda_possible {
            self.is_lambda_built = true;
            let definition = Arc::new(LambdaDefinition {
                levels: levels_for_lambda
                    .into_iter()
                    .map(|(_, slots, tuple)| (slots, tuple))
                    .collect(),
                body: body_for_lambda,
                captured: body_footprint
                    .slots
                    .iter()
                    .copied()
                    .filter(|slot| !bound.contains(slot))
                    .collect(),
                vars: body_footprint.vars.clone(),
                primes: body_footprint.primes.clone(),
            });
            eval(move |machine| {
                let mut lazy = Vec::with_capacity(domains.len());
                for (infinite, reference, set) in &domains {
                    lazy.push(match (infinite, reference) {
                        (Some(name), _) => Lazy::Infinite(name),
                        (None, Some(reference)) => reference(machine)?,
                        (None, None) => {
                            Lazy::Set(evaluate_set(machine, set, "a function over a non-set")?)
                        }
                    });
                }
                if lazy.iter().any(is_lazy_domain) {
                    return lazy_function::build(machine, &definition, lazy);
                }
                evaluate(machine)
            })
        } else {
            evaluate
        };
        Ok(Compiled {
            is_costly: true,
            ..leaf(evaluate, footprint)
        })
    }

    // --- functions ---

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
            let evaluators: Vec<Eval> = args.into_iter().map(|argument| argument.eval).collect();
            return Ok(leaf(
                eval(move |machine| {
                    let value = match &evaluators[..] {
                        [argument] => argument(machine)?,
                        evaluators => evaluate_tuple(machine, evaluators)?,
                    };
                    call_recursive_function(machine, runtime, slot, value)
                }),
                footprint,
            ));
        }
        let function = self.compile(function, context)?;
        let args = args
            .iter()
            .map(|&argument| self.compile(argument, context))
            .collect::<Compiling<Vec<Compiled>>>()?;
        let footprint = Footprint::merge_all(
            [&function.footprint]
                .into_iter()
                .chain(args.iter().map(|argument| &argument.footprint)),
        );
        if let [argument] = &args[..] {
            return Ok(super::fused::apply(&function, argument, footprint));
        }
        let evaluators: Vec<Eval> = args.iter().map(|argument| argument.eval.clone()).collect();
        let function = function.eval;
        Ok(leaf(
            eval(move |machine| {
                let key = evaluate_tuple(machine, &evaluators)?;
                let value = function(machine)?;
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
                except_many(base, flat)
            } else if let (Shape::Current(variable), [(key, value, None)]) =
                (function.shape, &flat[..])
            {
                super::fused::except_var_at(variable, key.clone(), value.clone())
            } else {
                except_flat(base, flat)
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
            except_nested(base, updates)
        };
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
        Compiled {
            is_costly: true,
            is_enumerated: true,
            are_elements_enumerated: elements.iter().all(|element| element.is_enumerated),
            is_in_order: true,
            are_elements_in_order: elements.iter().all(|element| element.is_in_order),
            ..leaf(
                eval(move |machine| {
                    let at = push_all(machine, &evaluators)?;
                    let values = machine.stack.split_off(at);
                    machine.store.set_of(&values)
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

fn quantify(
    machine: &mut Machine<'_>,
    levels: &[(Eval, Vec<u32>, bool)],
    level: usize,
    body: &Test,
    is_forall: bool,
) -> Outcome<bool> {
    let Some((set, slots, tuple)) = levels.get(level) else {
        return body(machine);
    };
    let set = evaluate_set(machine, set, "quantified over a non-set")?;
    for index in 0..machine.store.size_of(set) {
        let element = machine.store.element_at(set, index);
        assign_bound(machine, slots, *tuple, element)?;
        if quantify(machine, levels, level + 1, body, is_forall)? != is_forall {
            return Ok(!is_forall);
        }
    }
    Ok(is_forall)
}

// Pushes the images on the stack, above whatever evaluating them pushes and pops.
fn map_images(
    machine: &mut Machine<'_>,
    levels: &[(Eval, Vec<u32>, bool)],
    level: usize,
    body: &Eval,
) -> Outcome<()> {
    let Some((set, slots, tuple)) = levels.get(level) else {
        let image = body(machine)?;
        machine.stack.push(image);
        return Ok(());
    };
    let set = evaluate_set(machine, set, "mapped a non-set")?;
    for index in 0..machine.store.size_of(set) {
        let element = machine.store.element_at(set, index);
        assign_bound(machine, slots, *tuple, element)?;
        map_images(machine, levels, level + 1, body)?;
    }
    Ok(())
}

// Whether an element passes a filter's predicate, its names bound to it and then restored.
fn test_element(machine: &mut Machine<'_>, filter: &Filter, element: Id) -> Outcome<bool> {
    let saved: Vec<Id> = filter
        .slots
        .iter()
        .map(|&slot| machine.locals[slot as usize])
        .collect();
    let kept = assign_bound(machine, &filter.slots, filter.tuple, element)
        .and_then(|()| (filter.predicate)(machine));
    for (&slot, &value) in filter.slots.iter().zip(&saved) {
        machine.locals[slot as usize] = value;
    }
    kept
}

#[allow(clippy::too_many_arguments)]
fn construct_product(
    machine: &mut Machine<'_>,
    levels: &[Level],
    sets: &[Id],
    level: usize,
    current: &mut Vec<Id>,
    body: &Eval,
    keys: &mut Vec<Id>,
    values: &mut Vec<Id>,
) -> Outcome<()> {
    if level == levels.len() {
        keys.push(machine.store.tuple_of(current));
        values.push(body(machine)?);
        return Ok(());
    }
    let set = sets[level];
    for index in 0..machine.store.size_of(set) {
        let element = machine.store.element_at(set, index);
        current[level] = element;
        let bound = &levels[level];
        assign_bound(machine, &bound.slots, bound.tuple, element)?;
        construct_product(
            machine,
            levels,
            sets,
            level + 1,
            current,
            body,
            keys,
            values,
        )?;
    }
    Ok(())
}

fn find_position(machine: &mut Machine<'_>, function: Id, key: Id) -> Outcome<u32> {
    if !is_function_kind(machine.store.kind_of(function)) {
        return Err(Bail("EXCEPT on a non-function"));
    }
    match machine.store.find_key(function, key)? {
        -1 => Err(Bail("EXCEPT outside the domain")),
        position => Ok(position as u32),
    }
}

// Several updates write one new function: each key's position is the same in every intermediate
// function, and @ reads the value an earlier update gave the key, if any.
fn except_many(base: Eval, updates: Vec<(Eval, Eval, Option<u32>)>) -> Eval {
    eval(move |machine| {
        let function = base(machine)?;
        if lazy_function::is_lazy(machine, function) {
            return except_each(machine, function, &updates);
        }
        if !is_function_kind(machine.store.kind_of(function)) {
            return Err(Bail("EXCEPT on a non-function"));
        }
        let mut positions = Vec::with_capacity(updates.len());
        let mut values = Vec::with_capacity(updates.len());
        for (index, (key, value, at_slot)) in updates.iter().enumerate() {
            let key = key(machine)?;
            let position = match machine.store.find_key(function, key)? {
                -1 => return Err(Bail("EXCEPT outside the domain")),
                position => position as u32,
            };
            if let Some(at_slot) = at_slot {
                let mut old = machine.store.get_range_value(function, position);
                for earlier in 0..index {
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

fn except_flat(base: Eval, updates: Vec<(Eval, Eval, Option<u32>)>) -> Eval {
    eval(move |machine| {
        let function = base(machine)?;
        except_each(machine, function, &updates)
    })
}

fn except_each(
    machine: &mut Machine<'_>,
    function: Id,
    updates: &[(Eval, Eval, Option<u32>)],
) -> Outcome<Id> {
    let mut result = function;
    for (key, value, at_slot) in updates {
        let key = key(machine)?;
        if let Some(at_slot) = at_slot {
            machine.locals[*at_slot as usize] = get_at(machine, result, key)?;
        }
        let value = value(machine)?;
        result = lazy_function::except(machine, result, key, value)?;
    }
    Ok(result)
}

// @: the value a function gives the key an EXCEPT updates.
fn get_at(machine: &mut Machine<'_>, function: Id, key: Id) -> Outcome<Id> {
    if lazy_function::is_lazy(machine, function) {
        return lazy_function::apply(machine, function, key);
    }
    let position = find_position(machine, function, key)?;
    Ok(machine.store.get_range_value(function, position))
}

// Each update walks its path down, keeping each key and the function it indexes, then writes the
// new values back up.
fn except_nested(base: Eval, updates: Vec<(Vec<Eval>, u32, Eval)>) -> Eval {
    eval(move |machine| {
        let mut result = base(machine)?;
        for (steps, at_slot, value) in &updates {
            let mut keys = Vec::with_capacity(steps.len());
            for step in steps {
                keys.push(step(machine)?);
            }
            let mut functions = Vec::with_capacity(steps.len());
            let mut current = result;
            for &key in &keys {
                functions.push(current);
                current = get_at(machine, current, key)?;
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
