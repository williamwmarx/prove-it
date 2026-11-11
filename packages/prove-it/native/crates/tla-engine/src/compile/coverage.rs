//! The counting variant of compiled code (`-coverage`): each expression TLC's `Tool` evaluates
//! counts into the wrapper of TLC's cost model that `CostModel.get` finds for it, where TLC counts
//! (design/coverage.md). The wrappers are known as the code compiles, since the compiler expands
//! each operator where it is applied, so each closure counts into fixed wrappers.
//!
//! A search compiles this variant only when it asks for coverage. It caches nothing it counts,
//! and walks the initial predicate and each of TLC's actions as `Tool.getInitStates` and
//! `Tool.getNextStates` do, which is where TLC counts the leaves of a walk. What it can't count as
//! TLC does, it declines as it compiles, or abandons as it runs (`Machine::abandon_coverage`),
//! and the report then comes from the replay.

use std::ops::Range;
use std::rc::Rc;
use std::sync::Arc;

use tla_ir::{Bound, Definition, DefinitionForm, NodeId, NodeKind, PathStep, Resolution, Value};
use tla_values::store::{FALSE, KIND_FUNCTION, KIND_SET, KIND_TUPLE, Outcome, TRUE};
use tla_values::{Bail, Id};

use super::nodes::assign_bound;
use super::{Binding, Compiled, Compiler, Compiling, Context, bool_id, eval, leaf, lookup};
use crate::coverage::{Cm, NO_CM, Plan};
use crate::footprint::Footprint;
use crate::machine::{Eval, Machine};

fn decline<T>(what: impl std::fmt::Display) -> Compiling<T> {
    Err(super::CompileError::Decline(format!("coverage: {what}")))
}

// The builtins whose values TLC computes without enumerating or converting what they're applied
// to, as the counting variant follows them.
const ARITHMETIC: &[&str] = &[
    "+", "-", "*", "\\div", "%", "^", "<", ">", "<=", ">=", "\\leq", "\\geq", "=<", "..", "-.",
];
const LOGICAL: &[&str] = &[
    "~", "\\lnot", "\\neg", "/\\", "\\land", "\\/", "\\lor", "=>", "<=>", "\\equiv",
];
const EQUALITIES: &[&str] = &["=", "#", "/="];
const MEMBERSHIPS: &[&str] = &["\\in", "\\notin"];
// `toTuple` of their first operand, or of both (`\o`), which counts into a function TLC built.
const SEQUENCES: &[&str] = &["Len", "Head", "Tail", "Append", "SubSeq", "\\o"];

/// What the counting variant knows of what an expression's value may carry of TLC's cost model:
/// TLC enumerates a value into the cost model of the node that built it, and converts a tuple or
/// a record into it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum Tag {
    /// A value that carries none, and none of its elements does: what TLC computed at startup,
    /// a constant's, an integer's interval.
    Deep,
    /// A value that carries none, whose elements may.
    Shallow,
    /// A value that may carry one.
    Unknown,
}

impl Compiler<'_> {
    /// Whether TLC computed the definition a name applies as it started, and reads its value
    /// from then on: a constant definition, unless the configuration substitutes it for a
    /// declared constant or another definition, which TLC evaluates each time (SANY's graph
    /// names it by the name it replaces).
    pub(super) fn is_computed_at_startup(
        &self,
        name: tla_ir::TextId,
        index: tla_ir::Index,
    ) -> bool {
        let definition = self.definition(self.ir.definitions[index as usize]);
        let unkeyed = |text: &str| {
            text.rsplit_once('@')
                .filter(|(name, _)| !name.is_empty())
                .map_or(text, |(name, _)| name)
                .to_owned()
        };
        definition.flags & Definition::NORMALIZED != 0
            && unkeyed(self.text(definition.name)) == unkeyed(self.text(name))
    }

    fn plan(&self) -> Arc<Plan> {
        Arc::clone(self.coverage.as_ref().expect("a counting compile"))
    }

    // The SANY node an IR node translates to.
    fn sany(&self, node: NodeId) -> Compiling<u32> {
        match self.plan().of_ir.get(&self.node(node).0) {
            Some(&sany) => Ok(sany),
            None => decline("an expression SANY's view of the IR lacks"),
        }
    }

    fn wrapper(&self, cm: Cm, sany: u32) -> Compiling<Cm> {
        self.plan().get(cm, sany).or_else(decline)
    }

    pub(super) fn allocate_cell(&mut self) -> Option<usize> {
        if !self.is_counting_now {
            return None;
        }
        self.cell_count += 1;
        Some(self.cell_count - 1)
    }

    /// Compiles an expression TLC evaluates counting into `context.cm`.
    pub(super) fn compile_counted(
        &mut self,
        node: NodeId,
        context: &Context,
    ) -> Compiling<Compiled> {
        let (_, kind) = self.node(node);
        match kind {
            NodeKind::Number(_)
            | NodeKind::String(_)
            | NodeKind::WideNumber(_)
            | NodeKind::ExceptAt => {
                return self.compile_node(node, context);
            }
            NodeKind::Label { body, .. } => return self.compile(*body, context),
            NodeKind::Let { .. } => {
                // TLC binds each definition to a lazy value as it evaluates the LET.
                let first = self.cell_count;
                let compiled = self.compile_node(node, context)?;
                return Ok(resetting(compiled, first..self.cell_count));
            }
            _ => {}
        }
        let sany = self.sany(node)?;
        let wrapper = self.wrapper(context.cm, sany)?;
        let inner = Context {
            cm: wrapper,
            ..context.clone()
        };
        let compiled = match kind {
            NodeKind::And(operands) | NodeKind::Or(operands) => {
                return self.compile_counted_junction(
                    sany,
                    operands,
                    matches!(kind, NodeKind::And(_)),
                    context,
                );
            }
            NodeKind::If {
                condition,
                consequent,
                alternative,
            } => {
                let condition = self.compile(*condition, &inner)?;
                let consequent = self.compile(*consequent, &inner)?;
                let alternative = self.compile(*alternative, &inner)?;
                let footprint = Footprint::merge_all([
                    &condition.footprint,
                    &consequent.footprint,
                    &alternative.footprint,
                ]);
                let (test, then, otherwise) = (condition.eval, consequent.eval, alternative.eval);
                leaf(
                    eval(move |machine| {
                        if boolean(machine, &test)? {
                            then(machine)
                        } else {
                            otherwise(machine)
                        }
                    }),
                    footprint,
                )
            }
            NodeKind::Case { arms, other } => {
                let pairs = self.plan().nodes[sany as usize].args.clone();
                let mut tests = Vec::new();
                let mut footprints = Vec::new();
                for (position, &(condition, body)) in arms.iter().enumerate() {
                    let pair = self.wrapper(wrapper, pairs[position].expect("an arm"))?;
                    let arm = Context {
                        cm: pair,
                        ..context.clone()
                    };
                    let condition = self.compile(condition, &arm)?;
                    let body = self.compile(body, &arm)?;
                    footprints.push(condition.footprint.merge(&body.footprint));
                    tests.push((condition.eval, body.eval));
                }
                let otherwise = match other {
                    Some(other) => {
                        let pair = self.wrapper(wrapper, pairs[arms.len()].expect("OTHER"))?;
                        let arm = Context {
                            cm: pair,
                            ..context.clone()
                        };
                        let other = self.compile(*other, &arm)?;
                        footprints.push(other.footprint);
                        Some(other.eval)
                    }
                    None => None,
                };
                leaf(
                    eval(move |machine| {
                        for (test, value) in &tests {
                            if boolean(machine, test)? {
                                return value(machine);
                            }
                        }
                        match &otherwise {
                            Some(otherwise) => otherwise(machine),
                            None => Err(Bail("no CASE arm holds")),
                        }
                    }),
                    Footprint::merge_all(&footprints),
                )
            }
            NodeKind::Forall { bounds, body } | NodeKind::Exists { bounds, body } => {
                let is_forall = matches!(kind, NodeKind::Forall { .. });
                let (set, slots, tuple, scope) = self.counted_bound(bounds, &inner)?;
                let body = self.compile(*body, &scope)?;
                let footprint = set.footprint.merge(&body.footprint.without_slots(&slots));
                let (set, body) = (set.eval, body.eval);
                leaf(
                    eval(move |machine| {
                        let id = set(machine)?;
                        for position in 0..machine.store.size_of(id) {
                            let element = machine.store.element_at(id, position);
                            assign_bound(machine, &slots, tuple, element)?;
                            if boolean(machine, &body)? != is_forall {
                                return Ok(bool_id(!is_forall));
                            }
                        }
                        Ok(bool_id(is_forall))
                    }),
                    footprint,
                )
            }
            NodeKind::Choose {
                pattern,
                set: Some(set),
                body,
            } => {
                let bound = [Bound {
                    pattern: pattern.clone(),
                    set: *set,
                }];
                let (set, slots, tuple, scope) = self.counted_bound(&bound, &inner)?;
                let body = self.compile(*body, &scope)?;
                let footprint = set.footprint.merge(&body.footprint.without_slots(&slots));
                let (set, body) = (set.eval, body.eval);
                leaf(
                    eval(move |machine| {
                        let id = set(machine)?;
                        for position in 0..machine.store.size_of(id) {
                            let element = machine.store.element_at(id, position);
                            assign_bound(machine, &slots, tuple, element)?;
                            if boolean(machine, &body)? {
                                return Ok(element);
                            }
                        }
                        Err(Bail("CHOOSE found no element"))
                    }),
                    footprint,
                )
            }
            NodeKind::SetFilter { bound, predicate } => {
                let (set, slots, tuple, scope) =
                    self.counted_bound(std::slice::from_ref(bound), &inner)?;
                let predicate = self.compile(*predicate, &scope)?;
                let footprint = set
                    .footprint
                    .merge(&predicate.footprint.without_slots(&slots));
                let (set, predicate) = (set.eval, predicate.eval);
                leaf(
                    eval(move |machine| {
                        let id = set(machine)?;
                        let mut kept = Vec::new();
                        for position in 0..machine.store.size_of(id) {
                            let element = machine.store.element_at(id, position);
                            assign_bound(machine, &slots, tuple, element)?;
                            if boolean(machine, &predicate)? {
                                kept.push(element);
                            }
                        }
                        machine.store.set_of(&kept)
                    }),
                    footprint,
                )
            }
            NodeKind::SetMap { expression, bounds } => {
                let (set, slots, tuple, scope) = self.counted_bound(bounds, &inner)?;
                let expression = self.compile(*expression, &scope)?;
                let footprint = set
                    .footprint
                    .merge(&expression.footprint.without_slots(&slots));
                let (set, expression) = (set.eval, expression.eval);
                leaf(
                    eval(move |machine| {
                        let id = set(machine)?;
                        let mut values = Vec::new();
                        for position in 0..machine.store.size_of(id) {
                            let element = machine.store.element_at(id, position);
                            assign_bound(machine, &slots, tuple, element)?;
                            values.push(expression(machine)?);
                        }
                        machine.store.set_of(&values)
                    }),
                    footprint,
                )
            }
            NodeKind::FunctionConstruction {
                bounds,
                body,
                is_recursive: false,
            } => {
                // TLC builds it at once (`FcnLambdaValue.toFcnRcd`), counting each of its
                // values into its own cost model, where the domain is a set or an interval.
                let (set, slots, tuple, scope) = self.counted_bound(bounds, &inner)?;
                if tuple {
                    return decline("a function of a tuple of names");
                }
                let body = self.compile(*body, &scope)?;
                let footprint = set.footprint.merge(&body.footprint.without_slots(&slots));
                let (set, body) = (set.eval, body.eval);
                self.is_lambda_built = true;
                leaf(
                    eval(move |machine| {
                        let id = set(machine)?;
                        let size = machine.store.size_of(id);
                        let mut values = Vec::with_capacity(size as usize);
                        for position in 0..size {
                            machine.locals[slots[0] as usize] =
                                machine.store.element_at(id, position);
                            values.push(body(machine)?);
                        }
                        machine.coverage.secondary[wrapper as usize] += u64::from(size);
                        let function = machine.store.function_over_set(id, &values);
                        Ok(machine.store.mark_built_as_function(function))
                    }),
                    footprint,
                )
            }
            NodeKind::FunctionApplication { function, args } => {
                let [argument] = &args[..] else {
                    return decline("a function applied to several arguments");
                };
                if !self.is_strict_function(*function, context) {
                    return decline("a function TLC may keep lazy, applied");
                }
                let function = self.compile(*function, &inner)?;
                let argument = self.compile(*argument, &inner)?;
                let footprint = function.footprint.merge(&argument.footprint);
                let (function, argument) = (function.eval, argument.eval);
                leaf(
                    eval(move |machine| {
                        let value = function(machine)?;
                        let key = argument(machine)?;
                        machine.store.apply(value, key)
                    }),
                    footprint,
                )
            }
            NodeKind::FieldAccess { record, .. } => {
                let record = self.compile(*record, &inner)?;
                self.compile_field(node, record)?
            }
            NodeKind::Identifier(name) => self.compile_counted_identifier(node, name, &inner)?,
            NodeKind::Apply { name, args } => {
                let first = self.cell_count;
                let compiled = match name.resolution {
                    Resolution::Builtin(index) if !name.is_local => {
                        let builtin = self.builtin_name(index);
                        self.check_builtin(builtin, args, &inner)?;
                        let compiled = self.compile_node(node, &inner)?;
                        self.guard_builtin(builtin, args, &inner, compiled)?
                    }
                    Resolution::Definition(index)
                        if !name.is_local
                            && self.definition(self.ir.definitions[index as usize]).flags
                                & Definition::RECURSIVE
                                != 0 =>
                    {
                        return decline("a RECURSIVE operator");
                    }
                    _ => self.compile_node(node, &inner)?,
                };
                // TLC binds the arguments to lazy values as it evaluates the application.
                resetting(compiled, first..self.cell_count)
            }
            NodeKind::Record(fields) => {
                // Each field's value is evaluated under its `$Pair`'s wrapper.
                let pairs = self.plan().nodes[sany as usize].args.clone();
                let mut compiled = Vec::new();
                for (&(name, value), pair) in fields.iter().zip(pairs) {
                    let pair = self.wrapper(wrapper, pair.expect("a field"))?;
                    let units = self.units(name);
                    let key = self.store.str(&units);
                    let value = self.compile(
                        value,
                        &Context {
                            cm: pair,
                            ..context.clone()
                        },
                    )?;
                    compiled.push((key, value));
                }
                self.record_of(compiled)?
            }
            NodeKind::Except { function, updates } => {
                // Each update's path is evaluated under its `$Seq`'s wrapper, and its value under
                // its `$Pair`'s, with `@` bound to what it replaces.
                let pairs = self.plan().nodes[sany as usize].args.clone();
                let function = self.compile(*function, &inner)?;
                let mut compiled = Vec::new();
                for (update, pair) in updates.iter().zip(&pairs[1..]) {
                    let pair = pair.expect("an update");
                    let seq = self.plan().nodes[pair as usize].args[0].expect("a path");
                    let pair = self.wrapper(wrapper, pair)?;
                    let seq = self.wrapper(pair, seq)?;
                    let mut path = Vec::new();
                    for step in &update.path {
                        path.push(match step {
                            PathStep::Field(name) => {
                                let units = self.units(*name);
                                super::constant(self.store.str(&units))
                            }
                            PathStep::Index(args) => {
                                let [argument] = &args[..] else {
                                    return decline("an EXCEPT of a function of several arguments");
                                };
                                self.compile(
                                    *argument,
                                    &Context {
                                        cm: seq,
                                        ..context.clone()
                                    },
                                )?
                            }
                        });
                    }
                    let at_slot = self.allocate_slot();
                    let value_context = Context {
                        cm: pair,
                        ..context.with_scope(super::bind(
                            &context.scope,
                            self.at,
                            Binding::Slot(at_slot),
                        ))
                    };
                    let value = self.compile(update.value, &value_context)?;
                    let uses_at = value.footprint.slots.contains(&at_slot);
                    compiled.push((path, at_slot, value, uses_at));
                }
                Self::except_of(function, compiled)
            }
            NodeKind::SetEnumeration(_)
            | NodeKind::Tuple(_)
            | NodeKind::Prime(_)
            | NodeKind::Unchanged(_) => self.compile_node(node, &inner)?,
            _ => return decline(format!("expression {}", super::nodes::kind_name(kind))),
        };
        Ok(counting(&[wrapper], compiled))
    }

    // A field of a record, as the engine compiles it, from the record compiled to count: TLC
    // converts a tuple it selects a field of, which the variant doesn't follow.
    fn compile_field(&mut self, node: NodeId, record: Compiled) -> Compiling<Compiled> {
        let NodeKind::FieldAccess { field, .. } = self.node(node).1 else {
            unreachable!("a field access")
        };
        let units = self.units(*field);
        let key = self.store.str(&units);
        let evaluate = record.eval;
        Ok(leaf(
            eval(move |machine| {
                let value = evaluate(machine)?;
                if machine.store.kind_of(value) == KIND_TUPLE {
                    machine.abandon_coverage("a field of a tuple");
                }
                let mut hint = 0;
                machine.store.apply_field(value, key, &mut hint)
            }),
            record.footprint,
        ))
    }

    fn compile_counted_identifier(
        &mut self,
        node: NodeId,
        name: &tla_ir::Name,
        context: &Context,
    ) -> Compiling<Compiled> {
        if name.is_local
            && let Some(found) = lookup(&context.scope, name.text)
        {
            return match &found.binding {
                Binding::Argument(argument) => {
                    let argument = Rc::clone(argument);
                    self.compile_counted_argument(&argument, context)
                }
                Binding::Slot(_) => self.compile_node(node, context),
                Binding::Value { lazy: None, .. } => self.compile_node(node, context),
                _ => decline("a name bound to what the variant doesn't follow"),
            };
        }
        if let Resolution::Definition(index) = name.resolution {
            let definition = self.definition(self.ir.definitions[index as usize]);
            if !matches!(&definition.form, DefinitionForm::Operator(params) if params.is_empty()) {
                return decline("a function definition");
            }
            if self
                .startup_definitions
                .contains_key(&self.ir.definitions[index as usize])
            {
                return decline("a constant definition with effects");
            }
            if self.is_computed_at_startup(name.text, index) {
                // TLC computed it as it started, and evaluates nothing of it again.
                let quiet = Context {
                    cm: NO_CM,
                    ..context.clone()
                };
                return self.compile_node(node, &quiet);
            }
        }
        self.compile_node(node, context)
    }

    // A use of an operator's argument or a LET's definition, which TLC evaluates at its first use
    // and keeps for later uses in states that hold what it was evaluated in (`LazyValue`), unless
    // the use is in a next state only, where TLC evaluates it each time. A LET of a walk binds
    // nothing, so its definition is applied at each use.
    fn compile_counted_argument(
        &mut self,
        argument: &Rc<super::Argument>,
        context: &Context,
    ) -> Compiling<Compiled> {
        let is_primed = context.is_primed || argument.context.is_primed;
        let base = super::argument_context(argument).primed(is_primed);
        let Some(cell) = argument.cell else {
            let applied = Context {
                cm: context.cm,
                ..base
            };
            return self.compile(argument.expression, &applied);
        };
        let counted = self.compile(argument.expression, &base)?;
        if context.is_primed {
            return Ok(counted);
        }
        let quiet = self.compile(argument.expression, &Context { cm: NO_CM, ..base })?;
        let (counted_eval, quiet) = (counted.eval.clone(), quiet.eval);
        Ok(Compiled {
            eval: eval(move |machine| {
                if machine.is_cell_kept(cell) {
                    return quiet(machine);
                }
                let value = counted_eval(machine)?;
                machine.keep_cell(cell);
                Ok(value)
            }),
            ..strip(counted)
        })
    }

    // `\/` and `/\`: a bulleted list is one node, an infix chain as SANY nests it, the operands
    // of each prefix under its wrapper.
    fn compile_counted_junction(
        &mut self,
        sany: u32,
        operands: &[NodeId],
        is_and: bool,
        context: &Context,
    ) -> Compiling<Compiled> {
        let parents = self.junction_parents(sany, operands.len(), context.cm)?;
        let mut wrappers: Vec<Cm> = parents.clone();
        wrappers.dedup();
        let mut evaluators = Vec::new();
        let mut footprints = Vec::new();
        for (&operand, &parent) in operands.iter().zip(&parents) {
            let compiled = self.compile(
                operand,
                &Context {
                    cm: parent,
                    ..context.clone()
                },
            )?;
            footprints.push(compiled.footprint);
            evaluators.push(compiled.eval);
        }
        let compiled = Compiled {
            is_boolean: true,
            ..leaf(
                eval(move |machine| {
                    for evaluate in &evaluators {
                        if boolean(machine, evaluate)? != is_and {
                            return Ok(bool_id(!is_and));
                        }
                    }
                    Ok(bool_id(is_and))
                }),
                Footprint::merge_all(&footprints),
            )
        };
        // The outermost prefix first, as TLC enters them.
        wrappers.reverse();
        Ok(counting(&wrappers, compiled))
    }

    /// The wrapper each operand of a junction is evaluated under, the junction at `sany` under
    /// `cm`: all one node's for a bulleted list, the innermost prefix's for the first two of an
    /// infix chain and the next prefix's for each after.
    pub(super) fn junction_parents(&self, sany: u32, count: usize, cm: Cm) -> Compiling<Vec<Cm>> {
        let plan = self.plan();
        let outer = self.wrapper(cm, sany)?;
        if plan.nodes[sany as usize].args.len() == count {
            return Ok(vec![outer; count]);
        }
        // The prefixes from the outermost in, each with its wrapper.
        let mut prefixes = vec![outer];
        let mut node = sany;
        for _ in 2..count {
            node = plan.nodes[node as usize].args[0].expect("a prefix");
            let parent = *prefixes.last().expect("a prefix");
            prefixes.push(self.wrapper(parent, node)?);
        }
        let innermost = *prefixes.last().expect("a prefix");
        Ok((0..count)
            .map(|position| {
                if position < 2 {
                    innermost
                } else {
                    prefixes[count - position - 1]
                }
            })
            .collect())
    }

    // A bound whose set TLC enumerates in its normalized order: one name or tuple of names over a
    // set that carries no cost model, with its slots and the scope that binds them.
    pub(super) fn counted_bound(
        &mut self,
        bounds: &[Bound],
        context: &Context,
    ) -> Compiling<(Compiled, Vec<u32>, bool, Context)> {
        let [bound] = bounds else {
            return decline("several bounds");
        };
        let tag = self.tag_of(bound.set, context);
        if tag == Tag::Unknown {
            return decline("an enumeration of a value that may carry a cost model");
        }
        let set = self.compile(bound.set, context)?;
        if !set.is_normalized || set.may_be_infinite() {
            return decline("an enumeration of a set TLC keeps lazy");
        }
        let binder = self.bind_bound(&bound.pattern, context);
        if tag == Tag::Deep {
            self.deep_slots.extend(&binder.slots);
        }
        let set = Compiled {
            eval: {
                let evaluate = set.eval.clone();
                eval(move |machine| {
                    let id = evaluate(machine)?;
                    if machine.store.kind_of(id) != KIND_SET {
                        return Err(Bail("an enumeration of a non-set"));
                    }
                    Ok(id)
                })
            },
            ..set
        };
        Ok((set, binder.slots, binder.tuple, binder.context))
    }

    // What an expression's value may carry of TLC's cost model.
    pub(super) fn tag_of(&self, node: NodeId, context: &Context) -> Tag {
        let (_, kind) = self.node(node);
        match kind {
            NodeKind::Number(_) | NodeKind::String(_) => Tag::Deep,
            NodeKind::Label { body, .. } => self.tag_of(*body, context),
            NodeKind::Identifier(name) => {
                if name.is_local
                    && let Some(found) = lookup(&context.scope, name.text)
                {
                    return match &found.binding {
                        Binding::Slot(slot) if self.deep_slots.contains(slot) => Tag::Deep,
                        Binding::Value { lazy: None, .. } => Tag::Deep,
                        Binding::Argument(argument) => {
                            self.tag_of(argument.expression, &super::argument_context(argument))
                        }
                        _ => Tag::Unknown,
                    };
                }
                match name.resolution {
                    Resolution::Constant(_) | Resolution::Builtin(_) => Tag::Deep,
                    Resolution::Definition(index) => {
                        if self.is_computed_at_startup(name.text, index) {
                            Tag::Deep
                        } else {
                            Tag::Unknown
                        }
                    }
                    _ => Tag::Unknown,
                }
            }
            NodeKind::Apply { name, args } if !name.is_local => match name.resolution {
                Resolution::Builtin(index) => {
                    let builtin = self.builtin_name(index);
                    if ARITHMETIC.contains(&builtin)
                        || LOGICAL.contains(&builtin)
                        || EQUALITIES.contains(&builtin)
                        || MEMBERSHIPS.contains(&builtin)
                        || matches!(builtin, "Len" | "Cardinality" | "\\subseteq")
                    {
                        Tag::Deep
                    } else if builtin == "DOMAIN" {
                        if self.tag_of(args[0], context) == Tag::Deep {
                            Tag::Deep
                        } else {
                            Tag::Shallow
                        }
                    } else {
                        Tag::Unknown
                    }
                }
                _ => Tag::Unknown,
            },
            NodeKind::Forall { .. } | NodeKind::Exists { .. } => Tag::Deep,
            _ => Tag::Unknown,
        }
    }

    // Whether TLC evaluates the function an application applies to a value at once: one a state
    // holds, a constant or one computed at startup, a bound name, or one applied or selected out
    // of such, where a function constructed in place TLC keeps lazy (`EvalControl.KeepLazy`).
    fn is_strict_function(&self, node: NodeId, context: &Context) -> bool {
        match self.node(node).1 {
            NodeKind::Label { body, .. } => self.is_strict_function(*body, context),
            NodeKind::Prime(inner) => self.is_strict_function(*inner, context),
            NodeKind::FunctionApplication { function, .. } => {
                self.is_strict_function(*function, context)
            }
            NodeKind::FieldAccess { record, .. } => self.is_strict_function(*record, context),
            NodeKind::Except { .. } | NodeKind::Tuple(_) | NodeKind::Record(_) => true,
            NodeKind::Identifier(name) => {
                if name.is_local
                    && let Some(found) = lookup(&context.scope, name.text)
                {
                    return match &found.binding {
                        Binding::Slot(_) | Binding::Value { lazy: None, .. } => true,
                        Binding::Argument(argument) => self.is_strict_function(
                            argument.expression,
                            &super::argument_context(argument),
                        ),
                        _ => false,
                    };
                }
                match name.resolution {
                    Resolution::Variable(_) | Resolution::Constant(_) => true,
                    Resolution::Definition(index) => {
                        let definition = self.definition(self.ir.definitions[index as usize]);
                        self.is_computed_at_startup(name.text, index)
                            || matches!(&definition.form, DefinitionForm::Operator(params)
                                if params.is_empty())
                                && self.is_strict_function(definition.body, &Context::ROOT)
                    }
                    _ => false,
                }
            }
            _ => false,
        }
    }

    // Declines a builtin whose Java the variant doesn't follow, or one applied to what TLC would
    // enumerate counting into a cost model.
    pub(super) fn check_builtin(
        &self,
        builtin: &str,
        args: &[NodeId],
        context: &Context,
    ) -> Compiling<()> {
        if ARITHMETIC.contains(&builtin)
            || LOGICAL.contains(&builtin)
            || EQUALITIES.contains(&builtin)
            || SEQUENCES.contains(&builtin)
            || builtin == "DOMAIN"
        {
            return Ok(());
        }
        if MEMBERSHIPS.contains(&builtin) {
            let set = self.compile_shape_of(args[1], context);
            return if set {
                Ok(())
            } else {
                decline("a membership in a set TLC may keep lazy")
            };
        }
        // `S \cup T` enumerates T into its cost model, or is T where S is empty.
        if matches!(
            builtin,
            "Cardinality" | "\\cap" | "\\intersect" | "\\" | "\\subseteq" | "\\cup" | "\\union"
        ) && args
            .iter()
            .all(|&arg| self.tag_of(arg, context) != Tag::Unknown)
        {
            return Ok(());
        }
        decline(format!("the builtin {builtin}"))
    }

    // Whether TLC holds the value of a set expression as a set enumeration or an interval, which
    // its membership tests without counting.
    fn compile_shape_of(&self, node: NodeId, context: &Context) -> bool {
        match self.node(node).1 {
            NodeKind::Label { body, .. } => self.compile_shape_of(*body, context),
            NodeKind::SetEnumeration(_) | NodeKind::SetMap { .. } => true,
            NodeKind::Identifier(name) => {
                if name.is_local
                    && let Some(found) = lookup(&context.scope, name.text)
                {
                    return match &found.binding {
                        Binding::Argument(argument) => self.compile_shape_of(
                            argument.expression,
                            &super::argument_context(argument),
                        ),
                        Binding::Value { lazy: None, .. } => true,
                        _ => false,
                    };
                }
                match name.resolution {
                    Resolution::Constant(index) => matches!(
                        self.ir.constants[index as usize]
                            .value
                            .map(|value| &self.ir.values.list[value as usize]),
                        Some(Value::Set(_))
                    ),
                    Resolution::Definition(index) => {
                        let definition = self.definition(self.ir.definitions[index as usize]);
                        matches!(&definition.form, DefinitionForm::Operator(params)
                            if params.is_empty())
                            && self.compile_shape_of(definition.body, &Context::ROOT)
                    }
                    _ => false,
                }
            }
            NodeKind::Apply { name, .. } if !name.is_local => match name.resolution {
                Resolution::Builtin(index) => {
                    matches!(self.builtin_name(index), ".." | "DOMAIN")
                }
                _ => false,
            },
            _ => false,
        }
    }
}

/// What a value may hold that TLC converts into a cost model.
type Check = fn(&Machine<'_>, Id) -> bool;

/// The fields of a compiled expression another may read in place of evaluating it, which would
/// skip what it counts.
fn strip(compiled: Compiled) -> Compiled {
    Compiled {
        shape: super::Shape::Other,
        predicate: None,
        member: None,
        parts: None,
        interval: None,
        filter: None,
        reference: None,
        unsorted_first: None,
        element_references: None,
        subset_base: None,
        is_constant: false,
        is_costly: false,
        ..compiled
    }
}

// Counts into each wrapper, then evaluates.
fn counting(wrappers: &[Cm], compiled: Compiled) -> Compiled {
    let inner = compiled.eval.clone();
    let evaluate = match *wrappers {
        [wrapper] => eval(move |machine| {
            machine.count(wrapper);
            inner(machine)
        }),
        _ => {
            let wrappers = wrappers.to_vec();
            eval(move |machine| {
                for &wrapper in &wrappers {
                    machine.count(wrapper);
                }
                inner(machine)
            })
        }
    };
    Compiled {
        eval: evaluate,
        ..strip(compiled)
    }
}

// Forgets the lazy values of an application's arguments or a LET's definitions as it starts.
fn resetting(compiled: Compiled, cells: Range<usize>) -> Compiled {
    if cells.is_empty() {
        return strip(compiled);
    }
    let inner = compiled.eval.clone();
    Compiled {
        eval: eval(move |machine| {
            for cell in cells.clone() {
                machine.coverage.cells[cell].is_kept = false;
            }
            inner(machine)
        }),
        ..strip(compiled)
    }
}

impl Compiler<'_> {
    // A builtin's value, abandoning the count where TLC would convert what it is applied to into
    // a cost model the variant doesn't know: `toTuple` of a function TLC built, the comparison or
    // membership of functions of classes the store doesn't tell apart. The operands it checks are
    // evaluated again without counting.
    pub(super) fn guard_builtin(
        &mut self,
        builtin: &str,
        args: &[NodeId],
        context: &Context,
        compiled: Compiled,
    ) -> Compiling<Compiled> {
        let (checked, check): (&[NodeId], Check) = if EQUALITIES.contains(&builtin) {
            (args, holds_function)
        } else if MEMBERSHIPS.contains(&builtin) {
            (&args[..1], holds_function)
        } else if builtin == "\\o" {
            (args, |machine, id| machine.store.is_built_as_function(id))
        } else if SEQUENCES.contains(&builtin) {
            (&args[..1], |machine, id| {
                machine.store.is_built_as_function(id)
            })
        } else {
            return Ok(compiled);
        };
        let quiet = Context {
            cm: NO_CM,
            ..context.clone()
        };
        let operands = checked
            .iter()
            .map(|&arg| self.compile(arg, &quiet).map(|operand| operand.eval))
            .collect::<Compiling<Vec<Eval>>>()?;
        let inner = compiled.eval.clone();
        Ok(Compiled {
            eval: eval(move |machine| {
                for operand in &operands {
                    if let Ok(value) = operand(machine)
                        && check(machine, value)
                    {
                        machine.abandon_coverage("a function TLC may convert between classes");
                    }
                }
                inner(machine)
            }),
            ..strip(compiled)
        })
    }
}

fn boolean(machine: &mut Machine<'_>, evaluate: &Eval) -> Outcome<bool> {
    match evaluate(machine)? {
        TRUE => Ok(true),
        FALSE => Ok(false),
        _ => Err(Bail("expected a boolean")),
    }
}

/// Whether a value holds a function anywhere, which TLC may hold as a tuple, a record or a
/// function, and compare or convert by class.
pub(crate) fn holds_function(machine: &Machine<'_>, id: Id) -> bool {
    match machine.store.kind_of(id) {
        KIND_FUNCTION | KIND_TUPLE => true,
        KIND_SET => (0..machine.store.size_of(id))
            .any(|position| holds_function(machine, machine.store.element_at(id, position))),
        _ => false,
    }
}
