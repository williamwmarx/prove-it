//! The initial predicate and the actions, walked as TLC's Tool walks them (`walker.rs` in the
//! engine, `action.ts` in TypeScript): conjunctions left to right, a variable assigned at its first
//! conjunct of the form `x' = e` or `x' \in S` and tested at the others, disjunctions and `\E` in
//! order, operators expanded, and every other conjunct evaluated as a guard. Once every variable
//! has a value, TLC evaluates the rest of a conjunction as guards, in the initial predicate and,
//! with warnings on, in an action.

use std::collections::HashSet;

use tla_ir::{Bound, DefinitionForm, Name, NodeId, NodeKind, PathStep, Resolution, Startup};

use crate::eval::{Context, Evaluator, StackFrame, bound_expression};
use crate::sets::is_member;
use crate::value::{Evaluated, Value, elements, equals, fail, is_same};

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
        then: &mut Visit<'_, 'ir>,
    ) -> Evaluated<bool> {
        if self.boolean(node, context)? {
            then(self)
        } else {
            Ok(true)
        }
    }

    /// TLC's actions of a next-state relation, as `Tool.getActions` splits it: each disjunct, the
    /// body of an operator whose arguments are constant, a LET's or a label's body, and `\\E` at each of its
    /// bindings; anything else, and an `\\E` of no bindings or one TLC fails to enumerate, is an
    /// action.
    pub fn split_actions(
        &mut self,
        node: NodeId,
        context: &Context,
        actions: &mut Vec<(NodeId, Context)>,
    ) -> Evaluated<()> {
        match self.kind(node) {
            NodeKind::Or(operands) => {
                for &operand in operands {
                    self.split_actions(operand, context, actions)?;
                }
                return Ok(());
            }
            NodeKind::Let {
                instances,
                definitions,
                body,
            } => {
                let inner = self.bind_let(*instances, definitions, context)?;
                return self.split_actions(*body, &inner, actions);
            }
            NodeKind::Label { body, .. } => return self.split_actions(*body, context, actions),
            NodeKind::Exists { bounds, body } => {
                let mut contexts = Vec::new();
                let enumerated = self.for_each_binding(bounds, context, &mut |_, inner| {
                    contexts.push(inner.clone());
                    Ok(true)
                });
                if enumerated.is_err() || contexts.is_empty() {
                    actions.push((node, context.clone()));
                    return Ok(());
                }
                for inner in contexts {
                    self.split_actions(*body, &inner, actions)?;
                }
                return Ok(());
            }
            NodeKind::Identifier(_) | NodeKind::Apply { .. }
                if self.has_constant_arguments(node, context) =>
            {
                if let Some((body, inner)) = self.resolve_action(node, context)? {
                    return self.split_actions(body, &inner, actions);
                }
            }
            _ => {}
        }
        actions.push((node, context.clone()));
        Ok(())
    }

    // Whether the arguments of an operator application are constant, as `getActionsAppl` asks of
    // them before it splits the operator's body: here, whether none can read the state, and each
    // evaluates without it.
    fn has_constant_arguments(&mut self, node: NodeId, context: &Context) -> bool {
        let NodeKind::Apply { args, .. } = self.kind(node) else {
            return true;
        };
        let mut visited = HashSet::new();
        if args
            .iter()
            .any(|&argument| self.can_read_state(argument, context, &mut visited))
        {
            return false;
        }
        let width = self.current.len();
        let current = std::mem::replace(&mut self.current, vec![None; width]);
        let next = std::mem::replace(&mut self.next, vec![None; width]);
        let is_constant = args
            .iter()
            .all(|&argument| self.evaluate(argument, context).is_ok());
        self.current = current;
        self.next = next;
        is_constant
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
                let branch = if self.boolean(*condition, context)? {
                    *consequent
                } else {
                    *alternative
                };
                self.walk(branch, context, is_init, then)
            }
            NodeKind::Case { arms, other } => {
                for &(condition, body) in arms {
                    if self.boolean(condition, context)? {
                        return self.walk(body, context, is_init, then);
                    }
                }
                match other {
                    Some(other) => self.walk(*other, context, is_init, then),
                    None => fail("no CASE arm holds"),
                }
            }
            NodeKind::Let {
                instances,
                definitions,
                body,
            } => {
                let inner = self.bind_let(*instances, definitions, context)?;
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
                    let after = evaluator.evaluate(subscript, &context.primed(true))?;
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
                    return self.guard(node, context, then);
                };
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
                    return fail("applied a function outside its domain");
                }
                let inner = self.bind_pattern(&bound.pattern, &argument, &base)?;
                self.walk(body, &inner, is_init, then)
            }
            NodeKind::Identifier(_) => match self.resolve_action(node, context)? {
                Some((body, inner)) => self.walk(body, &inner, is_init, then),
                None => self.guard(node, context, then),
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
                        return self.guard(node, context, then);
                    }
                    return match operator {
                        "=" => {
                            let value = self.evaluate(args[1], context)?;
                            self.assign(variable, value, is_init, then)
                        }
                        "\\in" => {
                            let set = self.evaluate(args[1], context)?;
                            let is_in_order = self.is_in_normalized_order(args[1], context, 0)?;
                            for (position, element) in elements(&set)?.iter().enumerate() {
                                let chosen =
                                    self.choose(position as u32, is_in_order, &mut |evaluator| {
                                        evaluator.assign(variable, element.clone(), is_init, then)
                                    });
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
                        None => self.guard(node, context, then),
                    },
                }
            }
            _ => self.guard(node, context, then),
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
            if (is_init || evaluator.ir.model.is_warning_enabled)
                && !rest.is_empty()
                && evaluator.is_complete(is_init)
            {
                for context in rest {
                    if !evaluator.boolean(body, context)? {
                        return Ok(true);
                    }
                }
                return then(evaluator);
            }
            evaluator.walk_each(body, rest, is_init, then)
        })
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
    // startup (which it normalizes). TLC streams any other set, such as a union or SUBSET built
    // during the walk, in an order of its own.
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
            NodeKind::Identifier(name) if !name.is_local => match name.resolution {
                Resolution::Variable(_) => return Ok(!context.is_primed),
                Resolution::Constant(_) => return Ok(true),
                Resolution::Definition(index) => {
                    let definition = self.definition(self.ir.definitions[index as usize]);
                    if !matches!(definition.startup, Startup::None) {
                        return Ok(true);
                    }
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
        // Once every variable has a value, TLC evaluates the rest of the conjunction as guards:
        // in the initial predicate, and in an action with warnings on (`isAssignedShortcut`).
        if !is_first && (is_init || self.ir.model.is_warning_enabled) && self.is_complete(is_init) {
            for &operand in operands {
                if !self.boolean(operand, context)? {
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
