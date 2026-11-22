//! `x' \in [D -> T]` followed in its conjunction by guards and then `\A j \in E : x'[j] = e`, as
//! CCF's `ExtendAxiom` writes it: TLC binds x' to each function of [D -> T] in turn and abandons
//! it at the first guard that is FALSE (`Tool.getNextStates`, OPCODE_in), so only the functions
//! with `f[j] = e` at every j of E reach past the quantifier. The walk enumerates only those, where
//! it can show that every other function would have been abandoned before then without an error
//! or an effect, so that the successors, their order and every failure are TLC's.
//!
//! What shows it, each time the membership is reached (`Pruning::survivors`):
//! - The guards have no effect, and read x' only as `x'[k]`, with k read of names bound outside
//!   the conjunction (checked as compiled). Each such k is a key outside E, so a guard holds of a
//!   function as it holds of any other with its values at the keys outside E.
//! - The quantifier's body, `x'[j] = e`, with e not reading x', is evaluated for each j of E and
//!   each value of T, without an error, and holds for exactly one value of each j.
//! - The guards are evaluated for each assignment of values to the keys outside E, with the keys
//!   in E at the values the body holds for, without an error.
//!
//! Any failure, effect or surprise in these leaves the enumeration whole, as it was.

use std::collections::HashSet;

use tla_ir::{Bound, NodeId, NodeKind, Pattern, Resolution};
use tla_values::Id;
use tla_values::store::{FALSE, Outcome, TRUE, is_function_kind};

use super::walker::{Ordered, element_at};
use super::{
    Binding, Compiler, Compiling, Context, SEARCH_SLOTS, WARNING_SLOT, argument_context, lookup,
};
use crate::footprint::Footprint;
use crate::machine::{Eval, Machine, Step, UNASSIGNED};

/// What the walk of `x' \in [D -> T]` evaluates to find the functions that reach past the guards
/// and the quantifier after it.
pub(super) struct Pruning {
    /// The walk of the conjuncts between the membership and the quantifier, which reaches its
    /// end once for each way through them.
    prefix: Step,
    /// The keys at which the guards read x'.
    keys: Vec<Eval>,
    /// The quantifier's set, E, and the slot its name is bound to.
    bound: Ordered,
    slot: u32,
    /// The quantifier's body, `x'[j] = e`.
    body: Eval,
}

/// Whether a builtin's value is the same wherever the walk evaluates it with the same arguments:
/// not `\cdot`, an action, and none that reads or changes what TLC keeps beside the state, which
/// can change between two functions of the enumeration (TLC's registers and caches, its counts
/// and level, files, the environment, random draws, the trace, the successor's history).
pub(super) fn is_steady_builtin(name: &str) -> bool {
    const PREFIXES: [&str; 9] = [
        "TLC",
        "IO",
        "Random",
        "CSV",
        "Json",
        "ndJson",
        "Serialize",
        "Deserialize",
        "_",
    ];
    const NAMES: [&str; 11] = [
        "\\cdot",
        "Print",
        "PrintT",
        "Assert",
        "AssertEq",
        "AssertError",
        "TestRandomSetOfSubsets",
        "CounterExample",
        "Trace",
        "PickSuccessor",
        "JavaTime",
    ];
    !NAMES.contains(&name) && !PREFIXES.iter().any(|prefix| name.starts_with(prefix))
}

/// Whether a compiled expression reads nothing of TLC's search and keeps no slot for a print or
/// a warning, so that it has one value for the state and the names it reads.
fn is_steady(footprint: &Footprint) -> bool {
    footprint
        .slots
        .iter()
        .all(|slot| !SEARCH_SLOTS.contains(slot) && *slot != WARNING_SLOT)
}

/// The integer r with r to the power `width` equal to `size`, if there is one.
fn root(size: u32, width: u32) -> Option<u32> {
    let estimate = f64::from(size).powf(1.0 / f64::from(width)).round() as u32;
    [estimate.saturating_sub(1), estimate, estimate + 1]
        .into_iter()
        .find(|&base| base.checked_pow(width) == Some(size))
}

impl<'a> Compiler<'a> {
    /// The position, among the conjuncts after `variable' \\in set` in its conjunction, of the
    /// quantifier its pruning stops at, and the keys at which the conjuncts before it read x';
    /// none where they don't have the shape the module describes.
    pub(super) fn get_pruned_prefix(
        &self,
        variable: u32,
        set: NodeId,
        following: &[NodeId],
        context: &Context,
    ) -> Option<(usize, Vec<NodeId>)> {
        if !matches!(self.node(set).1, NodeKind::FunctionSet { .. }) {
            return None;
        }
        let mut keys = Vec::new();
        for (position, &node) in following.iter().enumerate() {
            if self.may_have_effect_in(node, context, &mut HashSet::new()) {
                return None;
            }
            if self.constraint_of(node, variable, context).is_some() {
                return Some((position, keys));
            }
            if !self.reads_next_at_keys(node, context, variable, &mut Some(&mut keys)) {
                return None;
            }
        }
        None
    }

    /// The pruning whose conjuncts before the quantifier `constraint`, `prefix_nodes`, walk as
    /// `prefix`, reading x' at `keys`; none where any of them, the quantifier's set or its body
    /// reads what TLC keeps beside the state.
    pub(super) fn compile_pruning(
        &mut self,
        prefix: Step,
        prefix_nodes: &[NodeId],
        keys: &[NodeId],
        constraint: NodeId,
        variable: u32,
        context: &Context,
    ) -> Compiling<Option<Pruning>> {
        let Some((bound, body)) = self.constraint_of(constraint, variable, context) else {
            return Ok(None);
        };
        let mut evals = Vec::with_capacity(keys.len());
        for &key in keys {
            let compiled = self.compile(key, context)?;
            if !is_steady(&compiled.footprint) {
                return Ok(None);
            }
            evals.push(compiled.eval);
        }
        for &conjunct in prefix_nodes {
            if !is_steady(&self.compile(conjunct, context)?.footprint) {
                return Ok(None);
            }
        }
        let compiled = self.compile(bound.set, context)?;
        if !is_steady(&compiled.footprint) {
            return Ok(None);
        }
        let ordered = self
            .order(compiled.clone(), bound.set, context, false)?
            .checked(compiled);
        let binder = self.bind_bound(&bound.pattern, context);
        let body = self.compile(body, &binder.context)?;
        if !is_steady(&body.footprint) {
            return Ok(None);
        }
        let body = body.eval;
        Ok(Some(Pruning {
            prefix,
            keys: evals,
            bound: ordered,
            slot: binder.slots[0],
            body,
        }))
    }

    // `\A j \in E : x'[j] = e`, with E and e not reading the next state: its bound and its body.
    fn constraint_of(
        &self,
        node: NodeId,
        variable: u32,
        context: &Context,
    ) -> Option<(&'a Bound, NodeId)> {
        let NodeKind::Forall { bounds, body } = self.node(node).1 else {
            return None;
        };
        let [
            bound @ Bound {
                pattern: Pattern::Name(name),
                ..
            },
        ] = bounds.as_slice()
        else {
            return None;
        };
        let NodeKind::Apply { name: equal, args } = self.node(*body).1 else {
            return None;
        };
        if equal.is_local
            || !matches!(equal.resolution,
                Resolution::Builtin(index) if self.builtin_name(index) == "=")
        {
            return None;
        }
        let [left, right] = args.as_slice() else {
            return None;
        };
        let NodeKind::FunctionApplication { function, args } = self.node(*left).1 else {
            return None;
        };
        let is_name = matches!(args.as_slice(), [key]
            if matches!(self.node(*key).1, NodeKind::Identifier(key) if key.is_local && key.text == *name));
        (is_name
            && self.is_next_variable(*function, variable)
            && self.reads_next_at_keys(*right, context, variable, &mut None)
            && self.reads_next_at_keys(bound.set, context, variable, &mut None))
        .then_some((bound, *body))
    }

    // `x'`, the variable primed.
    fn is_next_variable(&self, node: NodeId, variable: u32) -> bool {
        matches!(self.node(node).1, NodeKind::Prime(inner)
            if matches!(self.node(*inner).1, NodeKind::Identifier(name)
                if !name.is_local && name.resolution == Resolution::Variable(variable)))
    }

    // Whether evaluating an expression in `context` reads the next state only as `x'[k]`, x the
    // variable and k an expression of names bound outside it, each k pushed to `keys`; or, where
    // `keys` is none, not at all. Anything it can't tell, such as an operator passed as an
    // argument, reads it.
    fn reads_next_at_keys(
        &self,
        node: NodeId,
        context: &Context,
        variable: u32,
        keys: &mut Option<&mut Vec<NodeId>>,
    ) -> bool {
        let kind = self.node(node).1;
        match kind {
            NodeKind::FunctionApplication { function, args }
                if keys.is_some() && self.is_next_variable(*function, variable) =>
            {
                let [key] = args.as_slice() else {
                    return false;
                };
                if !self.is_outer(*key, context) {
                    return false;
                }
                if let Some(keys) = keys {
                    keys.push(*key);
                }
                return true;
            }
            NodeKind::Prime(_)
            | NodeKind::Unchanged(_)
            | NodeKind::Enabled(_)
            | NodeKind::Always(_)
            | NodeKind::Eventually(_)
            | NodeKind::BoxAction { .. }
            | NodeKind::AngleAction { .. }
            | NodeKind::WeakFairness { .. }
            | NodeKind::StrongFairness { .. }
            | NodeKind::Subexpression(_) => return false,
            NodeKind::Identifier(name)
            | NodeKind::OperatorReference(name)
            | NodeKind::Apply { name, .. } => {
                let is_clear = if name.is_local {
                    let scope = lookup(&context.scope, name.text);
                    match scope.as_ref().map(|scope| &scope.binding) {
                        // A name bound inside the expression, by a quantifier or a LET it holds.
                        None | Some(Binding::Slot(_)) => true,
                        Some(Binding::Argument(argument)) => self.reads_next_at_keys(
                            argument.expression,
                            &argument_context(argument),
                            variable,
                            &mut None,
                        ),
                        Some(_) => false,
                    }
                } else {
                    match name.resolution {
                        Resolution::Definition(index) => {
                            let body = self.definition(self.ir.definitions[index as usize]).body;
                            self.is_next_free(body, &mut HashSet::new())
                        }
                        Resolution::Builtin(index) => is_steady_builtin(self.builtin_name(index)),
                        Resolution::Variable(_) | Resolution::Constant(_) | Resolution::None => {
                            true
                        }
                    }
                };
                if !is_clear {
                    return false;
                }
            }
            _ => {}
        }
        kind.children()
            .into_iter()
            .chain(match kind {
                NodeKind::SetFilter { bound, .. } => Some(bound.set),
                _ => None,
            })
            .all(|child| self.reads_next_at_keys(child, context, variable, keys))
    }

    // Whether a definition's body, and those it names, read nothing of the next state: no prime,
    // no action and no temporal operator, and no operator it doesn't know.
    fn is_next_free(&self, node: NodeId, seen: &mut HashSet<NodeId>) -> bool {
        if !seen.insert(node) {
            return true;
        }
        let kind = self.node(node).1;
        let is_clear = match kind {
            NodeKind::Prime(_)
            | NodeKind::Unchanged(_)
            | NodeKind::Enabled(_)
            | NodeKind::Always(_)
            | NodeKind::Eventually(_)
            | NodeKind::BoxAction { .. }
            | NodeKind::AngleAction { .. }
            | NodeKind::WeakFairness { .. }
            | NodeKind::StrongFairness { .. }
            | NodeKind::Subexpression(_) => false,
            NodeKind::Identifier(name)
            | NodeKind::OperatorReference(name)
            | NodeKind::Apply { name, .. }
                if !name.is_local =>
            {
                match name.resolution {
                    Resolution::Definition(index) => {
                        let body = self.definition(self.ir.definitions[index as usize]).body;
                        self.is_next_free(body, seen)
                    }
                    Resolution::Builtin(index) => is_steady_builtin(self.builtin_name(index)),
                    _ => true,
                }
            }
            _ => true,
        };
        is_clear
            && kind
                .children()
                .into_iter()
                .chain(match kind {
                    NodeKind::SetFilter { bound, .. } => Some(bound.set),
                    _ => None,
                })
                .all(|child| self.is_next_free(child, seen))
    }

    // Whether an expression reads nothing of the next state and only names bound around
    // `context`, so that its value is the same wherever the conjunction evaluates it.
    fn is_outer(&self, node: NodeId, context: &Context) -> bool {
        if !self.reads_next_at_keys(node, context, u32::MAX, &mut None) {
            return false;
        }
        let mut nodes = vec![node];
        while let Some(node) = nodes.pop() {
            let kind = self.node(node).1;
            match kind {
                NodeKind::Identifier(name) | NodeKind::Apply { name, .. }
                    if name.is_local && lookup(&context.scope, name.text).is_none() =>
                {
                    return false;
                }
                NodeKind::Let { .. }
                | NodeKind::Lambda { .. }
                | NodeKind::Forall { .. }
                | NodeKind::Exists { .. }
                | NodeKind::UnboundedQuantifier { .. }
                | NodeKind::Choose { .. }
                | NodeKind::SetFilter { .. }
                | NodeKind::SetMap { .. }
                | NodeKind::FunctionConstruction { .. } => return false,
                _ => {}
            }
            nodes.extend(kind.children());
        }
        true
    }
}

impl Pruning {
    /// The positions in `set`, the `size` functions of [D -> T] in the order the walk takes them,
    /// of those that reach past the guards and the quantifier, in that order; none where the
    /// module's conditions don't hold, so that the walk takes them all. x' is unassigned.
    pub(super) fn survivors(
        &self,
        machine: &mut Machine<'_>,
        index: usize,
        set: Id,
        size: u32,
    ) -> Option<Vec<u32>> {
        if size < 2 || machine.generate.is_some() || machine.assigned_shapes.is_some() {
            return None;
        }
        let printed = machine.output.len();
        let slot = self.slot as usize;
        let bound = machine.locals[slot];
        machine.assigned += 1;
        let survivors = self.find(machine, index, set, size);
        machine.assigned -= 1;
        machine.next[index] = UNASSIGNED;
        machine.locals[slot] = bound;
        if machine.output.len() != printed {
            machine.output.truncate(printed);
            return None;
        }
        survivors.ok().flatten()
    }

    fn find(
        &self,
        machine: &mut Machine<'_>,
        index: usize,
        set: Id,
        size: u32,
    ) -> Outcome<Option<Vec<u32>>> {
        let first = element_at(machine, set, 0);
        if !is_function_kind(machine.store.kind_of(first)) {
            return Ok(None);
        }
        let width = machine.store.size_of(first);
        let Some(range) = (width > 0).then(|| root(size, width)).flatten() else {
            return Ok(None);
        };
        let width = width as usize;
        let keys: Vec<Id> = (0..width as u32)
            .map(|key| machine.store.get_key(first, key))
            .collect();
        // TLC's enumeration of [D -> T] varies the last key fastest, over T in its order.
        let choices: Vec<Id> = (0..range)
            .map(|choice| {
                let function = element_at(machine, set, choice);
                machine.store.get_range_value(function, width as u32 - 1)
            })
            .collect();
        let mut distinct = choices.clone();
        distinct.sort_unstable();
        distinct.dedup();
        if distinct.len() != choices.len() {
            return Ok(None);
        }
        // The function whose value at each key is the choice its digit names, checked to be the
        // one at that position of the set.
        let function_at = |machine: &mut Machine<'_>, digits: &[u32]| -> Option<(u32, Id)> {
            let position = digits
                .iter()
                .fold(0, |position, &digit| position * range + digit);
            let function = element_at(machine, set, position);
            let store = &mut machine.store;
            let is_it = is_function_kind(store.kind_of(function))
                && store.size_of(function) as usize == width
                && digits.iter().enumerate().all(|(key, &digit)| {
                    store.get_key(function, key as u32) == keys[key]
                        && store.get_range_value(function, key as u32) == choices[digit as usize]
                });
            is_it.then_some((position, function))
        };
        // The value the body holds for at each key of E.
        let mut fixed: Vec<Option<u32>> = vec![None; width];
        let bound = (self.bound.eval)(machine)?;
        for position in 0..self.bound.size(machine, bound)? {
            let element = element_at(machine, bound, position);
            let Some(key) = keys.iter().position(|&key| key == element) else {
                return Ok(None);
            };
            if fixed[key].is_some() {
                return Ok(None);
            }
            machine.locals[self.slot as usize] = element;
            let mut holding = None;
            for choice in 0..range {
                let mut digits = vec![0; width];
                digits[key] = choice;
                let Some((_, function)) = function_at(machine, &digits) else {
                    return Ok(None);
                };
                machine.next[index] = function;
                match (self.body)(machine)? {
                    TRUE if holding.is_none() => holding = Some(choice),
                    FALSE => {}
                    _ => return Ok(None),
                }
            }
            let Some(choice) = holding else {
                return Ok(None);
            };
            fixed[key] = Some(choice);
        }
        for key in &self.keys {
            let key = key(machine)?;
            match keys.iter().position(|&found| found == key) {
                Some(position) if fixed[position].is_none() => {}
                _ => return Ok(None),
            }
        }
        // Each assignment of the keys outside E, in the order the walk takes them, with the keys
        // in E at their values.
        let free: Vec<usize> = (0..width).filter(|&key| fixed[key].is_none()).collect();
        let mut digits: Vec<u32> = fixed.iter().map(|choice| choice.unwrap_or(0)).collect();
        let mut survivors = Vec::new();
        loop {
            let Some((position, function)) = function_at(machine, &digits) else {
                return Ok(None);
            };
            machine.next[index] = function;
            let mut is_reached = false;
            (self.prefix)(machine, &mut |_| {
                is_reached = true;
                Ok(())
            })?;
            if is_reached {
                survivors.push(position);
            }
            let Some(&last) = free.iter().rev().find(|&&key| digits[key] + 1 < range) else {
                break;
            };
            digits[last] += 1;
            for &key in free.iter().filter(|&&key| key > last) {
                digits[key] = 0;
            }
        }
        Ok(Some(survivors))
    }
}
