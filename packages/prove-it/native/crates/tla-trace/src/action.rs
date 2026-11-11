//! The initial predicate and the actions, walked as TLC's Tool walks them (`walker.rs` in the
//! engine, `action.ts` in TypeScript): conjunctions left to right, a variable assigned at its first
//! conjunct of the form `x' = e` or `x' \in S` and tested at the others, disjunctions and `\E` in
//! order, operators expanded, and every other conjunct evaluated as a guard. Once every variable
//! has a value, TLC evaluates the rest of a conjunction as guards, in the initial predicate and,
//! with warnings on, in an action.

use std::collections::HashSet;

use tla_values::random::JavaRandom;

use tla_ir::{Bound, Definition, DefinitionForm, Name, NodeId, NodeKind, PathStep, Resolution};

use crate::eval::{Context, Demand, Evaluator, PRIMED_UNASSIGNED, StackFrame, bound_expression};
use crate::print::format_value;
use crate::sets::is_member;
use crate::value::{
    Evaluated, Lazy, TlcMessage, Value, elements, equals, fail, fail_runtime, fail_with, is_same,
};

/// What a walk calls for each state it completes; it returns false to stop the walk.
pub type Visit<'v, 'ir> = dyn FnMut(&mut Evaluator<'ir>) -> Evaluated<bool> + 'v;

const MAXIMUM_DEPTH: u32 = 50;

impl<'ir> Evaluator<'ir> {
    fn targets(&mut self, is_init: bool) -> &mut Vec<Option<Value>> {
        if is_init {
            &mut self.current
        } else {
            &mut self.next
        }
    }

    fn is_complete(&mut self, is_init: bool) -> bool {
        self.targets(is_init).iter().all(Option::is_some)
    }

    // Whether TLC evaluates what is left of a conjunction as guards, every variable having a
    // value: in the initial predicate (`getInitStates`), and in an action with warnings on
    // (`getNextStatesAllAssigned`), but not in ENABLED, whose `enabled` walks on.
    fn is_assigned_shortcut(&mut self, is_init: bool) -> bool {
        !self.is_enabling
            && (is_init || self.ir.model.is_warning_enabled)
            && self.is_complete(is_init)
    }

    /// Walks an action (or, `is_init`, the initial predicate), calling `visit` with each state it
    /// completes, until `visit` returns false; returns whether the walk ran to its end.
    pub fn walk_action(
        &mut self,
        node: NodeId,
        context: &Context,
        is_init: bool,
        visit: &mut Visit<'_, 'ir>,
    ) -> Evaluated<bool> {
        self.walk(node, context, is_init, &mut |evaluator| {
            if !evaluator.is_complete(is_init) {
                if is_init && let Some(stack) = &mut evaluator.call_stack {
                    stack.incomplete = Some(
                        evaluator
                            .current
                            .iter()
                            .map(|value| value.as_ref().map_or("null".into(), format_value))
                            .collect(),
                    );
                }
                return fail(if is_init {
                    "an initial state that isn't complete"
                } else {
                    "a successor that isn't complete"
                });
            }
            visit(evaluator)
        })
    }

    // Assigns a variable for the rest of the walk, or tests the value it has.
    fn assign(
        &mut self,
        variable: u32,
        value: Value,
        is_init: bool,
        then: &mut Visit<'_, 'ir>,
    ) -> Evaluated<bool> {
        let index = variable as usize;
        if let Some(target) = &self.target
            && !is_same(&target[index], &value)
        {
            return Ok(true);
        }
        if let Some(known) = &self.targets(is_init)[index] {
            return if equals(known, &value)? {
                then(self)
            } else {
                Ok(true)
            };
        }
        self.targets(is_init)[index] = Some(value);
        let result = then(self);
        self.targets(is_init)[index] = None;
        result
    }

    // The variable an expression such as x' (or x in the initial predicate) assigns, following
    // operator arguments and zero-arity definitions.
    fn assignable(
        &mut self,
        node: NodeId,
        context: &Context,
        is_primed: bool,
        depth: u32,
    ) -> Evaluated<Option<u32>> {
        if depth > MAXIMUM_DEPTH {
            return Ok(None);
        }
        let name = match self.kind(node) {
            NodeKind::Prime(inner) if is_primed => {
                return self.assignable(*inner, context, false, depth + 1);
            }
            NodeKind::Identifier(name) => *name,
            _ => return Ok(None),
        };
        if !name.is_local
            && let Resolution::Variable(index) = name.resolution
        {
            return Ok((!is_primed).then_some(index));
        }
        match self.resolve_action(node, context)? {
            Some((body, inner)) => self.assignable(body, &inner, is_primed, depth + 1),
            None => Ok(None),
        }
    }

    fn guard(
        &mut self,
        node: NodeId,
        context: &Context,
        is_init: bool,
        then: &mut Visit<'_, 'ir>,
    ) -> Evaluated<bool> {
        self.guard_as(node, context, Demand::Guard { is_init }, then)
    }

    fn guard_as(
        &mut self,
        node: NodeId,
        context: &Context,
        demand: Demand,
        then: &mut Visit<'_, 'ir>,
    ) -> Evaluated<bool> {
        let holds = self.boolean_as(node, context, demand);
        // `Tool`'s getInitStates and getNextStates test themselves that a guard is a boolean,
        // outside the methods of the value, where the call stack freezes.
        if holds.is_err()
            && let Some(stack) = &mut self.call_stack
        {
            stack.is_frozen = true;
        }
        if !holds? {
            return Ok(true);
        }
        then(self)
    }

    // A function's value the walk tests, which `OPCODE_fa` words apart from a guard's.
    fn applied(
        &mut self,
        node: NodeId,
        context: &Context,
        is_init: bool,
        then: &mut Visit<'_, 'ir>,
    ) -> Evaluated<bool> {
        let outer = self
            .walked_application
            .replace((self.resolved(node), is_init));
        let holds = self.boolean_as(node, context, Demand::Applied { is_init });
        self.walked_application = outer;
        if holds? { then(self) } else { Ok(true) }
    }

    /// Whether TLC computes a definition as it starts (`processConstantDefns`), which it does to
    /// one of constant level whose evaluation then succeeds. One that reads TLC's registers, its
    /// counterexample or the _POSSIBLE counts fails then, so TLC keeps it; any other one of
    /// constant level may be computed, so this says yes for it.
    pub(crate) fn is_precomputed(&mut self, definition: NodeId) -> bool {
        !self.may_reach(
            definition,
            &["TLCGet", "TLCSet", "CounterExample", "_Counts"],
        )
    }

    /// Whether an expression may read the state or apply one of these builtins.
    pub(crate) fn may_reach(&mut self, node: NodeId, builtins: &'static [&'static str]) -> bool {
        self.state_builtins = builtins;
        let reads = self.can_read(node, &Context::default());
        self.state_builtins = &[];
        reads
    }

    /// Whether an expression may read the state or apply one of these builtins, as TLC bounds the
    /// level of a definition it computes as it starts (`getLevelBound`).
    pub(crate) fn may_reach_bound(
        &mut self,
        node: NodeId,
        builtins: &'static [&'static str],
    ) -> bool {
        self.is_level_bound = true;
        let reads = self.may_reach(node, builtins);
        self.is_level_bound = false;
        reads
    }

    /// Whether an expression may read the state, as `getLevel` finds it above constant level.
    pub(crate) fn can_read(&self, node: NodeId, context: &Context) -> bool {
        self.can_read_state(node, context, &mut HashSet::new())
    }

    // Whether an expression may read the state, as an expression above constant level, which
    // `getLevel` finds: a variable, a prime, UNCHANGED or ENABLED in it or in a definition it names.
    // A form the check doesn't follow counts as one that may.
    fn can_read_state(
        &self,
        node: NodeId,
        context: &Context,
        visited: &mut HashSet<NodeId>,
    ) -> bool {
        let any = |nodes: &[NodeId], visited: &mut HashSet<NodeId>| {
            nodes
                .iter()
                .any(|&inner| self.can_read_state(inner, context, visited))
        };
        let bounds = |bounds: &[Bound]| bounds.iter().map(|bound| bound.set).collect::<Vec<_>>();
        match self.kind(node) {
            NodeKind::Number(_)
            | NodeKind::WideNumber(_)
            | NodeKind::Decimal(_)
            | NodeKind::String(_)
            | NodeKind::ExceptAt => false,
            // `getLevelBound` gives an operator passed as an argument level 0, whatever it reads.
            NodeKind::Lambda { .. } | NodeKind::OperatorReference(_) if self.is_level_bound => {
                false
            }
            NodeKind::Identifier(name) | NodeKind::OperatorReference(name) => {
                self.can_name_read_state(name, context, visited)
            }
            NodeKind::Apply { name, args } => {
                self.can_name_read_state(name, context, visited) || any(args, visited)
            }
            NodeKind::Lambda { body, .. }
            | NodeKind::UnboundedQuantifier { body, .. }
            | NodeKind::Label { body, .. } => self.can_read_state(*body, context, visited),
            NodeKind::And(nodes)
            | NodeKind::Or(nodes)
            | NodeKind::SetEnumeration(nodes)
            | NodeKind::Tuple(nodes)
            | NodeKind::Bracket(nodes)
            | NodeKind::Product(nodes) => any(nodes, visited),
            NodeKind::If {
                condition,
                consequent,
                alternative,
            } => any(&[*condition, *consequent, *alternative], visited),
            NodeKind::Case { arms, other } => {
                arms.iter()
                    .any(|&(condition, body)| any(&[condition, body], visited))
                    || other.is_some_and(|other| self.can_read_state(other, context, visited))
            }
            NodeKind::Let {
                definitions, body, ..
            } => any(definitions, visited) || self.can_read_state(*body, context, visited),
            NodeKind::Forall { bounds: list, body }
            | NodeKind::Exists { bounds: list, body }
            | NodeKind::FunctionConstruction {
                bounds: list, body, ..
            } => any(&bounds(list), visited) || self.can_read_state(*body, context, visited),
            NodeKind::SetMap {
                expression,
                bounds: list,
            } => any(&bounds(list), visited) || self.can_read_state(*expression, context, visited),
            NodeKind::Choose { set, body, .. } => {
                set.is_some_and(|set| self.can_read_state(set, context, visited))
                    || self.can_read_state(*body, context, visited)
            }
            NodeKind::SetFilter { bound, predicate } => any(&[bound.set, *predicate], visited),
            NodeKind::FunctionSet { domain, range } => any(&[*domain, *range], visited),
            NodeKind::Record(fields) | NodeKind::RecordSet(fields) => fields
                .iter()
                .any(|&(_, value)| self.can_read_state(value, context, visited)),
            NodeKind::Except { function, updates } => {
                self.can_read_state(*function, context, visited)
                    || updates.iter().any(|update| {
                        self.can_read_state(update.value, context, visited)
                            || update.path.iter().any(|step| match step {
                                PathStep::Field(_) => false,
                                PathStep::Index(indices) => any(indices, visited),
                            })
                    })
            }
            NodeKind::FunctionApplication { function, args } => {
                self.can_read_state(*function, context, visited) || any(args, visited)
            }
            NodeKind::FieldAccess { record, .. } => self.can_read_state(*record, context, visited),
            NodeKind::Definition(definition) => {
                let sets = match &definition.form {
                    DefinitionForm::Function(list) => bounds(list),
                    DefinitionForm::Operator(_) => Vec::new(),
                };
                visited.insert(node)
                    && sets
                        .into_iter()
                        .chain([definition.body])
                        .any(|inner| self.can_read_state(inner, context, visited))
            }
            _ => true,
        }
    }

    // Whether a name may read the state: a variable, a definition whose body may, or a LET
    // definition or operator argument whose expression may in the scope that binds it.
    fn can_name_read_state(
        &self,
        name: &Name,
        context: &Context,
        visited: &mut HashSet<NodeId>,
    ) -> bool {
        if name.is_local {
            return bound_expression(context, name.text).is_some_and(|(node, inner)| {
                // A definition checks its own visit, in the Definition arm.
                (matches!(self.kind(node), NodeKind::Definition(_)) || visited.insert(node))
                    && self.can_read_state(node, &inner, visited)
            });
        }
        match name.resolution {
            Resolution::Variable(_) => true,
            Resolution::Builtin(index) => self
                .state_builtins
                .contains(&&*self.ir.texts[self.ir.builtins[index as usize].name as usize]),
            Resolution::Definition(index) => self.can_read_state(
                self.ir.definitions[index as usize],
                &Context::default(),
                visited,
            ),
            _ => false,
        }
    }

    // Walks a node in its frame of the call stack, as `visit` in `tlc/replay.ts` does.
    pub(crate) fn walk(
        &mut self,
        node: NodeId,
        context: &Context,
        is_init: bool,
        then: &mut Visit<'_, 'ir>,
    ) -> Evaluated<bool> {
        if self.call_stack.is_none() {
            return self.walk_node(node, context, is_init, then);
        }
        let frame = StackFrame::Node(self.resolved(node));
        self.in_frame(frame, &mut |evaluator| {
            evaluator.walk_node(node, context, is_init, then)
        })
    }

    // The first `count` operands of an infix conjunction, as SANY's node of that prefix: the
    // prefix of one fewer, then the last.
    fn conjunction_prefix(
        &mut self,
        node: NodeId,
        operands: &[NodeId],
        count: usize,
        context: &Context,
        is_init: bool,
        then: &mut Visit<'_, 'ir>,
    ) -> Evaluated<bool> {
        if self.is_walked_whole(node, count) {
            return self.conjunction(&operands[..count], true, context, is_init, then);
        }
        let last = operands[count - 1];
        let frame = StackFrame::Prefix(self.resolved(node), count - 1);
        self.in_frame(frame, &mut |evaluator| {
            evaluator.conjunction_prefix(
                node,
                operands,
                count - 1,
                context,
                is_init,
                &mut |evaluator| evaluator.conjunction(&[last], false, context, is_init, then),
            )
        })
    }

    // The first `count` operands of an infix disjunction, as `conjunction_prefix` nests them.
    fn disjunction_prefix(
        &mut self,
        node: NodeId,
        operands: &[NodeId],
        count: usize,
        context: &Context,
        is_init: bool,
        then: &mut Visit<'_, 'ir>,
    ) -> Evaluated<bool> {
        if self.is_walked_whole(node, count) {
            return self.disjunction(&operands[..count], context, is_init, then);
        }
        let frame = StackFrame::Prefix(self.resolved(node), count - 1);
        if !self.in_frame(frame, &mut |evaluator| {
            evaluator.disjunction_prefix(node, operands, count - 1, context, is_init, then)
        })? {
            return Ok(false);
        }
        self.choose(count as u32 - 1, true, &mut |evaluator| {
            evaluator.walk(operands[count - 1], context, is_init, then)
        })
    }

    fn walk_node(
        &mut self,
        node: NodeId,
        context: &Context,
        is_init: bool,
        then: &mut Visit<'_, 'ir>,
    ) -> Evaluated<bool> {
        match self.kind(node) {
            NodeKind::And(operands) => {
                self.conjunction_prefix(node, operands, operands.len(), context, is_init, then)
            }
            NodeKind::Or(operands) => {
                self.disjunction_prefix(node, operands, operands.len(), context, is_init, then)
            }
            NodeKind::Exists { bounds, body } => {
                let mut is_in_order = true;
                for bound in bounds {
                    is_in_order &= self.is_in_normalized_order(bound.set, context, 0)?;
                }
                let mut position = 0;
                self.for_each_binding(bounds, context, &mut |evaluator, inner| {
                    position += 1;
                    evaluator.choose(position, is_in_order, &mut |evaluator| {
                        evaluator.walk(*body, inner, is_init, then)
                    })
                })
            }
            NodeKind::Forall { bounds, body } => {
                // TLC walks the conjunction of the body over the bindings: the first, then the
                // others in reverse, as `getNextStates` queues them.
                let mut contexts = Vec::new();
                self.for_each_binding(bounds, context, &mut |_, inner| {
                    contexts.push(inner.clone());
                    Ok(true)
                })?;
                if contexts.len() > 1 {
                    contexts[1..].reverse();
                }
                self.walk_each(*body, &contexts, is_init, then)
            }
            NodeKind::If {
                condition,
                consequent,
                alternative,
            } => {
                let branch =
                    if self.boolean_as(*condition, context, Demand::WalkedIf { node, is_init })? {
                        *consequent
                    } else {
                        *alternative
                    };
                self.walk(branch, context, is_init, then)
            }
            NodeKind::Case { arms, other } => {
                for &(condition, body) in arms {
                    if self.boolean_as(condition, context, Demand::WalkedCase { body, is_init })? {
                        return self.walk(body, context, is_init, then);
                    }
                }
                match other {
                    Some(other) => self.walk(*other, context, is_init, then),
                    None => fail_runtime(
                        "no CASE arm holds",
                        format!(
                            "In computing {}, TLC encountered a CASE with no conditions true.\n{}",
                            self.computing(is_init),
                            self.describe_range(node)
                        ),
                    ),
                }
            }
            NodeKind::Let {
                definitions, body, ..
            } => {
                let inner = self.bind_let(definitions, context)?;
                self.walk(*body, &inner, is_init, then)
            }
            NodeKind::Unchanged(expression) => {
                if is_init {
                    return fail("UNCHANGED in the initial predicate");
                }
                self.walk_unchanged(*expression, context, then)
            }
            NodeKind::AngleAction { action, subscript } => {
                let subscript = *subscript;
                self.walk(*action, context, is_init, &mut |evaluator| {
                    let now = evaluator.evaluate(subscript, context)?;
                    // TLC's `Tool#enabled` names the fairness condition where A leaves a variable
                    // of v unassigned (`toUnspecifiedSubscriptError`), unlike TLC 1.7.4.
                    let after = evaluator
                        .evaluate(subscript, &context.primed(true))
                        .or_else(|error| {
                            match error.reason.strip_prefix(PRIMED_UNASSIGNED) {
                                Some(variable) if evaluator.is_enabling && !evaluator.is_174() => {
                                    fail_with(
                                        error.reason.clone(),
                                        TlcMessage {
                                            text: format!(
                                            "The action formula A appearing in a WF_v(A) or SF_v(A) operator does not specify the primed value of the variable {variable} occurring in the state formula v.\n"
                                        ),
                                            code: Some(2148),
                                            is_eval_exception: false,
                                        },
                                    )
                                }
                                _ => Err(error),
                            }
                        })?;
                    if equals(&now, &after)? {
                        Ok(true)
                    } else {
                        then(evaluator)
                    }
                })
            }
            NodeKind::BoxAction { action, subscript } => {
                let action = *action;
                let subscript = *subscript;
                if !self.choose(0, true, &mut |evaluator| {
                    evaluator.walk(action, context, is_init, then)
                })? {
                    return Ok(false);
                }
                self.choose(1, true, &mut |evaluator| {
                    evaluator.walk_unchanged(subscript, context, then)
                })
            }
            NodeKind::Label { body, .. } => self.walk(*body, context, is_init, then),
            NodeKind::FunctionApplication { function, args } if args.len() == 1 => {
                let Some((bound, body, base)) = self.walked_function(*function, context)? else {
                    return self.applied(node, context, is_init, then);
                };
                // `getInitStates` evaluates the function, which TLC builds unless it keeps it lazy
                // (`EvalControl.Init`), and applies it; it walks the body of a lazy one only.
                if is_init && !self.is_enabling {
                    let value = self.evaluate(*function, context)?;
                    if !matches!(value, Value::Lambda(_)) {
                        let argument = self.evaluate(args[0], context)?;
                        return match self.apply_checked(&value, &argument)? {
                            Value::Bool(true) => then(self),
                            Value::Bool(false) => Ok(true),
                            other => self.non_boolean(node, &other, Demand::Applied { is_init }),
                        };
                    }
                }
                // The function first, its domain in its frame, as TLC builds the FcnLambdaValue;
                // then the argument once, and the body walked at it.
                let frame = StackFrame::Node(self.resolved(*function));
                let set =
                    self.in_frame(frame, &mut |evaluator| evaluator.evaluate(bound.set, &base));
                // A function a LET or a definition defines is built in the frame of its
                // definition too, which the replay doesn't record.
                if set.is_err()
                    && matches!(self.kind(*function), NodeKind::Identifier(_))
                    && let Some(stack) = &mut self.call_stack
                {
                    stack
                        .unfollowed
                        .get_or_insert("the domain of a function a definition defines");
                }
                let set = set?;
                let argument = self.evaluate(args[0], context)?;
                if !is_member(&argument, &set)? {
                    return self.walked_outside(*function, bound, body, &base, &set, &argument);
                }
                let inner = self.bind_pattern(&bound.pattern, &argument, &base)?;
                self.walk(body, &inner, is_init, then)
            }
            NodeKind::FunctionApplication { .. } => self.applied(node, context, is_init, then),
            NodeKind::Identifier(_) => match self.resolve_action(node, context)? {
                Some((body, inner)) => self.walk(body, &inner, is_init, then),
                None => self.guard(node, context, is_init, then),
            },
            NodeKind::Apply { name, args } => {
                let operator = if name.is_local {
                    ""
                } else {
                    self.name(name.text)
                };
                let variable = if matches!(operator, "=" | "\\in" | "\\subseteq") && args.len() == 2
                {
                    self.assignable(args[0], context, !is_init, 0)?
                } else {
                    None
                };
                if let Some(variable) = variable {
                    // A variable assigned already is tested: against the value of x' = e, as
                    // `proceedWithValue` does, and otherwise as the conjunct's value.
                    if operator != "=" && self.targets(is_init)[variable as usize].is_some() {
                        return self.guard(node, context, is_init, then);
                    }
                    return match operator {
                        "=" => {
                            let value = self.evaluate(args[1], context)?;
                            self.assign(variable, value, is_init, then)
                        }
                        "\\in" => {
                            let set = self.evaluate(args[1], context)?;
                            // TLC enumerates a set that is `Enumerable` alone.
                            if let Value::Lazy(lazy) = &set
                                && lazy.is_overridden()
                            {
                                let range = self.describe_range(node);
                                return fail_runtime(
                                    "enumerated an infinite set",
                                    if self.is_enabling {
                                        format!(
                                            "The right side of \\IN is not enumerable.\n{range}"
                                        )
                                    } else {
                                        format!(
                                            "In computing {}, the right side of \\IN is not enumerable.\n{range}",
                                            self.computing(is_init)
                                        )
                                    },
                                );
                            }
                            let is_in_order = self.is_in_normalized_order(args[1], context, 0)?;
                            let effects = self.effects();
                            for (position, element) in elements(&set)?.iter().enumerate() {
                                let chosen =
                                    self.choose(position as u32, is_in_order, &mut |evaluator| {
                                        evaluator.assign(variable, element.clone(), is_init, then)
                                    });
                                // What the walk prints, draws or does to a register comes in
                                // the order TLC streams the set in, which is its own for a set
                                // it keeps lazy.
                                if !is_in_order
                                    && matches!(set, Value::Lazy(_))
                                    && self.effects() != effects
                                {
                                    return fail(
                                        "an effect under an assignment from a set TLC streams",
                                    );
                                }
                                if chosen.is_err()
                                    && !is_in_order
                                    && let Some(stack) = &mut self.call_stack
                                {
                                    stack
                                        .unfollowed
                                        .get_or_insert("an assignment from a set TLC streams");
                                }
                                if !chosen? {
                                    return Ok(false);
                                }
                            }
                            Ok(true)
                        }
                        _ => fail("x' \\subseteq S"),
                    };
                }
                match operator {
                    "=>" if args.len() == 2 => {
                        if self.boolean(args[0], context)? {
                            self.walk(args[1], context, is_init, then)
                        } else {
                            then(self)
                        }
                    }
                    "/\\" => self.conjunction(args, true, context, is_init, then),
                    "\\/" => self.disjunction(args, context, is_init, then),
                    _ => match self.resolve_action(node, context)? {
                        Some((body, inner)) => self.walk(body, &inner, is_init, then),
                        None => self.guard(node, context, is_init, then),
                    },
                }
            }
            _ => self.guard(node, context, is_init, then),
        }
    }

    fn disjunction(
        &mut self,
        operands: &[NodeId],
        context: &Context,
        is_init: bool,
        then: &mut Visit<'_, 'ir>,
    ) -> Evaluated<bool> {
        for (position, &operand) in operands.iter().enumerate() {
            if !self.choose(position as u32, true, &mut |evaluator| {
                evaluator.walk(operand, context, is_init, then)
            })? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    // Walks a body at each context in turn, as a conjunction. In the initial predicate, once
    // every variable has a value, the body at the contexts left is evaluated as a guard, as the
    // engine's `WalkedForall` and `successors.ts` do.
    fn walk_each(
        &mut self,
        body: NodeId,
        contexts: &[Context],
        is_init: bool,
        then: &mut Visit<'_, 'ir>,
    ) -> Evaluated<bool> {
        let Some((first, rest)) = contexts.split_first() else {
            return then(self);
        };
        self.walk(body, first, is_init, &mut |evaluator| {
            // TLC puts the other bindings at the front of the conjuncts left, so the shortcut past
            // assigned conjuncts applies to them as it does to a conjunction's.
            if !rest.is_empty() && evaluator.is_assigned_shortcut(is_init) {
                for context in rest {
                    if !evaluator.boolean_as(body, context, Demand::Remaining { is_init })? {
                        return Ok(true);
                    }
                }
                return then(evaluator);
            }
            evaluator.walk_each(body, rest, is_init, then)
        })
    }

    // What tells whether the walk printed, drew or read or set a register.
    fn effects(&self) -> (usize, usize, usize, Option<u64>) {
        (
            self.printed.len(),
            self.register_reads,
            self.register_writes,
            self.random.as_ref().map(JavaRandom::state),
        )
    }

    // Walks on with a choice made, at a position in TLC's order or, `!is_in_order`, in this
    // evaluator's.
    fn choose(
        &mut self,
        position: u32,
        is_in_order: bool,
        then: &mut Visit<'_, 'ir>,
    ) -> Evaluated<bool> {
        let depth = self.choices.len();
        self.choices.push((position, is_in_order));
        let result = then(self);
        self.choices.truncate(depth);
        result
    }

    // Whether TLC enumerates the set an expression gives in normalized order, as this evaluator
    // does: a set enumeration, an interval, a variable of the current state (whose values TLC
    // normalized when it fingerprinted the state), a constant or a definition TLC evaluates at
    // startup and deep-normalizes (`processConstantDefns`). TLC streams any other set, such as a
    // union or SUBSET built during the walk, in an order of its own.
    fn is_in_normalized_order(
        &mut self,
        node: NodeId,
        context: &Context,
        depth: u32,
    ) -> Evaluated<bool> {
        if depth > MAXIMUM_DEPTH {
            return Ok(false);
        }
        match self.kind(node) {
            NodeKind::SetEnumeration(_) => return Ok(true),
            NodeKind::Apply { name, args }
                if !name.is_local && args.len() == 2 && self.name(name.text) == ".." =>
            {
                return Ok(true);
            }
            // TLC streams [S -> T] over S normalized, the last argument varying fastest through
            // T's own order, which is the order of the functions where T's is.
            NodeKind::FunctionSet { range, .. } => {
                return self.is_in_normalized_order(*range, context, depth + 1);
            }
            // The domain of a variable's value, which TLC normalized as it fingerprinted the state.
            NodeKind::Apply { name, args }
                if !name.is_local && args.len() == 1 && self.name(name.text) == "DOMAIN" =>
            {
                if let NodeKind::Identifier(operand) = self.kind(args[0])
                    && !operand.is_local
                    && matches!(operand.resolution, Resolution::Variable(_))
                {
                    return Ok(!context.is_primed);
                }
            }
            // What holds a set TLC keeps lazy streams it in that set's own order.
            NodeKind::Identifier(name) if !name.is_local => match name.resolution {
                Resolution::Variable(_) => {
                    return Ok(!context.is_primed && self.is_held_normalized(node, context)?);
                }
                Resolution::Constant(_) => return self.is_held_normalized(node, context),
                Resolution::Definition(index)
                    if self.ir.model.startup.definitions.contains(&index)
                        || self.definition(self.ir.definitions[index as usize]).flags
                            & Definition::NORMALIZED
                            != 0 =>
                {
                    return self.is_held_normalized(node, context);
                }
                _ => {}
            },
            _ => {}
        }
        match self.resolve_action(node, context)? {
            Some((body, inner)) => self.is_in_normalized_order(body, &inner, depth + 1),
            None => Ok(false),
        }
    }

    fn is_held_normalized(&mut self, node: NodeId, context: &Context) -> Evaluated<bool> {
        is_streamed_normalized(&self.evaluate(node, context)?)
    }

    fn conjunction(
        &mut self,
        operands: &[NodeId],
        is_first: bool,
        context: &Context,
        is_init: bool,
        then: &mut Visit<'_, 'ir>,
    ) -> Evaluated<bool> {
        let Some((&first, rest)) = operands.split_first() else {
            return then(self);
        };
        // Once every variable has a value, TLC evaluates the rest of the conjunction as guards.
        if !is_first && self.is_assigned_shortcut(is_init) {
            for &operand in operands {
                if !self.boolean_as(operand, context, Demand::Remaining { is_init })? {
                    return Ok(true);
                }
            }
            return then(self);
        }
        self.walk(first, context, is_init, &mut |evaluator| {
            evaluator.conjunction(rest, false, context, is_init, then)
        })
    }

    // UNCHANGED e, as TLC's `processUnchanged` takes it, each part in its frame: a variable assigned
    // its current value or tested, a tuple element by element, a name through what it's bound to,
    // and anything else compared with its value in the next state.
    fn walk_unchanged(
        &mut self,
        expression: NodeId,
        context: &Context,
        then: &mut Visit<'_, 'ir>,
    ) -> Evaluated<bool> {
        let frame = StackFrame::Node(self.resolved(expression));
        self.in_frame(frame, &mut |evaluator| {
            evaluator.unchanged_node(expression, context, then)
        })
    }

    fn unchanged_node(
        &mut self,
        expression: NodeId,
        context: &Context,
        then: &mut Visit<'_, 'ir>,
    ) -> Evaluated<bool> {
        if let Some(variable) = self.assignable(expression, context, false, 0)? {
            let Some(value) = self.current[variable as usize].clone() else {
                return fail("variable not assigned");
            };
            return self.assign(variable, value, false, then);
        }
        match self.kind(expression) {
            NodeKind::Tuple(items) => self.unchanged_items(items, context, then),
            NodeKind::Identifier(_) => match self.resolve_action(expression, context)? {
                Some((body, inner)) => self.walk_unchanged(body, &inner, then),
                None => self.unchanged_value(expression, context, then),
            },
            _ => self.unchanged_value(expression, context, then),
        }
    }

    fn unchanged_items(
        &mut self,
        items: &[NodeId],
        context: &Context,
        then: &mut Visit<'_, 'ir>,
    ) -> Evaluated<bool> {
        let Some((&first, rest)) = items.split_first() else {
            return then(self);
        };
        self.walk_unchanged(first, context, &mut |evaluator| {
            evaluator.unchanged_items(rest, context, then)
        })
    }

    fn unchanged_value(
        &mut self,
        expression: NodeId,
        context: &Context,
        then: &mut Visit<'_, 'ir>,
    ) -> Evaluated<bool> {
        let now = self.evaluate(expression, context)?;
        let after = self.evaluate(expression, &context.primed(true))?;
        if equals(&now, &after)? {
            then(self)
        } else {
            Ok(true)
        }
    }
}

// Whether TLC enumerates a set a name holds in normalized order: a set it normalized, a set of
// functions, records or tuples of such sets, which it enumerates part by part, or a union of
// such sets whose elements, the first operand's then the second's own, come in that order. Any
// other set TLC keeps lazy it streams in an order of its own.
fn is_streamed_normalized(set: &Value) -> Evaluated<bool> {
    let Value::Lazy(lazy) = set else {
        return Ok(!matches!(set, Value::Unsorted(_)));
    };
    let is_normalized = |part: &Value| !matches!(part, Value::Lazy(_) | Value::Unsorted(_));
    Ok(match &**lazy {
        Lazy::FunctionSet(domain, range) => is_normalized(domain) && is_normalized(range),
        Lazy::RecordSet(fields, _) => fields.iter().all(|(_, part)| is_normalized(part)),
        Lazy::Product(parts) => parts.iter().all(is_normalized),
        Lazy::Cup(left, right)
            if is_streamed_normalized(left)? && is_streamed_normalized(right)? =>
        {
            let mut streamed = elements(left)?.to_vec();
            for element in elements(right)?.iter() {
                if !is_member(element, left)? {
                    streamed.push(element.clone());
                }
            }
            let normalized = elements(set)?;
            streamed.len() == normalized.len()
                && streamed.iter().zip(normalized.iter()).try_fold(
                    true,
                    |is_same_order, (streamed, normalized)| {
                        Ok(is_same_order && equals(streamed, normalized)?)
                    },
                )?
        }
        _ => false,
    })
}
