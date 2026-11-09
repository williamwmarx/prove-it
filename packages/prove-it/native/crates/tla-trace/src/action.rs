//! The initial predicate and the actions, walked as TLC's Tool walks them (`walker.rs` in the
//! engine, `action.ts` in TypeScript): conjunctions left to right, a variable assigned at its first
//! conjunct of the form `x' = e` or `x' \in S` and tested at the others, disjunctions and `\E` in
//! order, operators expanded, and every other conjunct evaluated as a guard. Once every variable
//! has a value, TLC evaluates the rest of a conjunction as guards.

use tla_ir::{NodeId, NodeKind, Resolution};

use crate::eval::{Context, Evaluator};
use crate::value::{Evaluated, Value, elements, equals, fail};

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

    // The variables UNCHANGED e names, following names to what they're bound to.
    fn unchanged_variables(
        &mut self,
        node: NodeId,
        context: &Context,
        depth: u32,
    ) -> Evaluated<Option<Vec<u32>>> {
        if depth > MAXIMUM_DEPTH {
            return Ok(None);
        }
        match self.kind(node) {
            NodeKind::Tuple(items) => {
                let mut variables = Vec::new();
                for &item in items {
                    match self.unchanged_variables(item, context, depth + 1)? {
                        Some(found) => variables.extend(found),
                        None => return Ok(None),
                    }
                }
                Ok(Some(variables))
            }
            NodeKind::Identifier(name) => {
                if !name.is_local
                    && let Resolution::Variable(index) = name.resolution
                {
                    return Ok(Some(vec![index]));
                }
                match self.resolve_action(node, context)? {
                    Some((body, inner)) => self.unchanged_variables(body, &inner, depth + 1),
                    None => Ok(None),
                }
            }
            _ => Ok(None),
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

    fn walk(
        &mut self,
        node: NodeId,
        context: &Context,
        is_init: bool,
        then: &mut Visit<'_, 'ir>,
    ) -> Evaluated<bool> {
        match self.kind(node) {
            NodeKind::And(operands) => self.conjunction(operands, true, context, is_init, then),
            NodeKind::Or(operands) => self.disjunction(operands, context, is_init, then),
            NodeKind::Exists { bounds, body } => {
                self.for_each_binding(bounds, context, &mut |evaluator, inner| {
                    evaluator.walk(*body, inner, is_init, then)
                })
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
                if !self.walk(*action, context, is_init, then)? {
                    return Ok(false);
                }
                self.walk_unchanged(*subscript, context, then)
            }
            NodeKind::Label { body, .. } => self.walk(*body, context, is_init, then),
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
                if matches!(operator, "=" | "\\in" | "\\subseteq") && args.len() == 2 {
                    if let Some(variable) = self.assignable(args[0], context, !is_init, 0)? {
                        return match operator {
                            "=" => {
                                if self.targets(is_init)[variable as usize].is_some() {
                                    return self.guard(node, context, then);
                                }
                                let value = self.evaluate(args[1], context)?;
                                self.assign(variable, value, is_init, then)
                            }
                            "\\in" => {
                                if self.targets(is_init)[variable as usize].is_some() {
                                    return self.guard(node, context, then);
                                }
                                let set = self.evaluate(args[1], context)?;
                                for element in elements(&set)?.iter() {
                                    if !self.assign(variable, element.clone(), is_init, then)? {
                                        return Ok(false);
                                    }
                                }
                                Ok(true)
                            }
                            _ => fail("x' \\subseteq S"),
                        };
                    }
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
        for &operand in operands {
            if !self.walk(operand, context, is_init, then)? {
                return Ok(false);
            }
        }
        Ok(true)
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
        if !is_first && self.is_complete(is_init) {
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

    // UNCHANGED e: each variable of e assigned its current value or tested, or e' = e as a guard.
    fn walk_unchanged(
        &mut self,
        expression: NodeId,
        context: &Context,
        then: &mut Visit<'_, 'ir>,
    ) -> Evaluated<bool> {
        let Some(variables) = self.unchanged_variables(expression, context, 0)? else {
            let now = self.evaluate(expression, context)?;
            let after = self.evaluate(expression, &context.primed(true))?;
            return if equals(&now, &after)? {
                then(self)
            } else {
                Ok(true)
            };
        };
        self.unchanged_from(&variables, then)
    }

    fn unchanged_from(&mut self, variables: &[u32], then: &mut Visit<'_, 'ir>) -> Evaluated<bool> {
        let Some((&first, rest)) = variables.split_first() else {
            return then(self);
        };
        let Some(value) = self.current[first as usize].clone() else {
            return fail("variable not assigned");
        };
        self.assign(first, value, false, &mut |evaluator| {
            evaluator.unchanged_from(rest, then)
        })
    }

}
