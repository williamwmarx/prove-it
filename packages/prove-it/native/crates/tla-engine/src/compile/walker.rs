//! Walks the initial predicate and the next-state relation in the order TLC does, as `action.ts`
//! (and `codegen.ts`, which writes the same walk out as code) does. It walks conjunctions,
//! disjunctions, quantifiers and operators as TLC's Tool does, assigning a variable at its first
//! conjunct of the form x' = e or x' \in S, and evaluating every other conjunct as a guard.
//!
//! A walk is a [`Step`]: it calls its continuation once for each state it completes. A branch of a
//! conjunction goes on through the conjuncts after it, so the continuation a branch gets runs the
//! rest of the conjunction, then the conjunction's own continuation.

use std::cell::RefCell;
use std::collections::HashSet;
use std::rc::Rc;
use std::sync::Arc;

use tla_ir::{Index, NodeId, NodeKind, Pattern, Resolution, ScopeBinding};
use tla_values::store::{FALSE, KIND_SET, KIND_TUPLE, Outcome, TRUE};
use tla_values::{Bail, Id};

use super::{
    Binding, CompileError, Compiled, Compiler, Compiling, Context, Definition, DefinitionForm,
    OperatorBody, SEARCH_SLOTS, Scope, decline, eval, leaf, lookup, unsupported,
};
use crate::footprint::Footprint;
use crate::machine::{Continue, Eval, Machine, Member, Step, UNASSIGNED};

/// What ENABLED's walk stops with at its first successor (`FOUND` in `action.ts`).
const FOUND: &str = "ENABLED found a successor";

fn is_found(bail: &Bail) -> bool {
    bail.0 == FOUND
}

/// How the walk treats a conjunction once every variable has a value.
#[derive(Clone, Copy, Debug)]
pub(crate) struct WalkOptions {
    /// Whether the walk is of the initial predicate, which assigns unprimed variables.
    pub is_init: bool,
    /// TLC evaluates the conjuncts left once every variable has a value, rather than walking
    /// them: for the initial predicate always, and for the next-state relation with warnings on.
    pub is_shortcut: bool,
}

/// How an action is walked: as the initial predicate, with TLC's shortcut once every variable is
/// assigned, and whether what it prints is printed, which only a search that hands over no more
/// than the state it was expanding allows.
#[derive(Clone, Copy, Debug)]
pub struct ActionOptions {
    pub is_init: bool,
    pub is_shortcut: bool,
    pub can_print: bool,
}

/// What a compile that may only be needed as the walk runs left: its value, or why it failed,
/// which stops the walk only if the walk needs it.
type Deferred = Result<Eval, Bail>;

// A compile error, as the reason a walk stops at run time. The reasons are few and kept for the
// run, as the TypeScript engine throws them where it compiles lazily.
fn deferred(compiled: Compiling<Compiled>) -> Deferred {
    compiled.map(|compiled| compiled.eval).map_err(|error| {
        let reason = match error {
            CompileError::Bail(reason) | CompileError::Decline(reason) => reason,
        };
        Bail(Box::leak(reason.into_boxed_str()))
    })
}

fn run_deferred(machine: &mut Machine<'_>, deferred: &Deferred) -> Outcome<Id> {
    match deferred {
        Ok(evaluate) => evaluate(machine),
        Err(bail) => Err(*bail),
    }
}

fn step(
    walk: impl Fn(&mut Machine<'_>, &mut Continue<'_>) -> Outcome<()> + Send + Sync + 'static,
) -> Step {
    Arc::new(walk)
}

// The variables a walk assigns: the current state's in the initial predicate, else the next's.
fn target<'m>(machine: &'m mut Machine<'_>, is_init: bool) -> &'m mut Vec<Id> {
    if is_init {
        &mut machine.cur
    } else {
        &mut machine.next
    }
}

// The element at a position of a set, or of the tuple a walk of a universal quantifier also takes.
fn element_at(machine: &Machine<'_>, id: Id, position: u32) -> Id {
    if machine.store.kind_of(id) == KIND_SET {
        machine.store.element_at(id, position)
    } else {
        machine.store.get_range_value(id, position)
    }
}

fn expect_set_size(machine: &Machine<'_>, id: Id) -> Outcome<u32> {
    if machine.store.kind_of(id) == KIND_SET {
        Ok(machine.store.size_of(id))
    } else {
        Err(Bail("an action quantified over a non-set"))
    }
}

enum Conjunct {
    Guard(Eval),
    Assign { variable: u32, value: Eval },
    Unchanged(Vec<u32>),
    Branch(Step),
}

struct Conjunction {
    conjuncts: Vec<Conjunct>,
    // Each conjunct as a guard, from the second on, for the shortcut.
    guards: Vec<Option<Deferred>>,
    // Whether a conjunct from each on is walked, so the shortcut passes a walk.
    walked_from: Vec<bool>,
    options: WalkOptions,
    width: u32,
}

// Runs a conjunction from a conjunct on, unassigning on the way out what it assigned.
fn run_from(
    conjunction: &Conjunction,
    machine: &mut Machine<'_>,
    start: usize,
    on_complete: &mut Continue<'_>,
) -> Outcome<()> {
    let mark = machine.undo.len();
    let count = conjunction.conjuncts.len();
    let is_init = conjunction.options.is_init;
    let mut index = start;
    while index < count {
        if index > 0 && conjunction.options.is_shortcut && machine.assigned == conjunction.width {
            if conjunction.walked_from[index] {
                machine.is_past_walk = true;
            }
            let mut holds = true;
            for guard in &conjunction.guards[index..] {
                let value =
                    run_deferred(machine, guard.as_ref().expect("a guard for the shortcut"))?;
                if value == FALSE {
                    holds = false;
                    break;
                }
                if value != TRUE {
                    return Err(Bail("a conjunct that isn't a boolean"));
                }
            }
            if holds {
                on_complete(machine)?;
            }
            break;
        }
        match &conjunction.conjuncts[index] {
            Conjunct::Guard(evaluate) => {
                let value = evaluate(machine)?;
                if value == FALSE {
                    break;
                }
                if value != TRUE {
                    return Err(Bail("a conjunct that isn't a boolean"));
                }
            }
            Conjunct::Assign { variable, value } => {
                let value = value(machine)?;
                let current = target(machine, is_init)[*variable as usize];
                if current == UNASSIGNED {
                    target(machine, is_init)[*variable as usize] = value;
                    machine.assigned += 1;
                    machine.undo.push(*variable);
                } else if current != value && !machine.store.equals(current, value)? {
                    break;
                }
            }
            Conjunct::Unchanged(variables) => {
                let mut holds = true;
                for &variable in variables {
                    let now = machine.cur[variable as usize];
                    let current = machine.next[variable as usize];
                    if current == UNASSIGNED {
                        machine.next[variable as usize] = now;
                        machine.assigned += 1;
                        machine.undo.push(variable);
                    } else if current != now && !machine.store.equals(current, now)? {
                        holds = false;
                        break;
                    }
                }
                if !holds {
                    break;
                }
            }
            Conjunct::Branch(branch) => {
                branch(machine, &mut |machine: &mut Machine<'_>| {
                    run_from(conjunction, machine, index + 1, on_complete)
                })?;
                break;
            }
        }
        index += 1;
    }
    if index == count {
        on_complete(machine)?;
    }
    for position in (mark..machine.undo.len()).rev() {
        let variable = machine.undo[position] as usize;
        target(machine, is_init)[variable] = UNASSIGNED;
    }
    machine.assigned -= (machine.undo.len() - mark) as u32;
    machine.undo.truncate(mark);
    Ok(())
}

// A walk of a universal quantifier whose body assigns or branches, as TLC walks the conjunction of
// its body over the bindings: the first binding, then the others in reverse.
struct WalkedForall {
    levels: Vec<(Eval, u32)>,
    body: Step,
    // The body as a guard, for the shortcut of the initial predicate.
    guard: Option<Deferred>,
    is_init: bool,
    width: u32,
}

// A run of a walked universal quantifier: each level's set, its stride and the slot's value
// before, and the number of bindings.
struct ForallRun {
    sets: Vec<(Id, u32, Id)>,
    count: u32,
}

impl WalkedForall {
    // Binds the names for binding `index`, numbered with the first name varying fastest.
    fn bind(&self, run: &ForallRun, machine: &mut Machine<'_>, index: u32) {
        let binding = if index == 0 { 0 } else { run.count - index };
        for (level, &(set, stride, _)) in run.sets.iter().enumerate() {
            let size = machine.store.size_of(set);
            let element = element_at(machine, set, (binding / stride) % size);
            machine.locals[self.levels[level].1 as usize] = element;
        }
    }

    fn restore(&self, run: &ForallRun, machine: &mut Machine<'_>) {
        for (level, &(_, _, saved)) in run.sets.iter().enumerate() {
            machine.locals[self.levels[level].1 as usize] = saved;
        }
    }

    fn visit(
        &self,
        run: &ForallRun,
        machine: &mut Machine<'_>,
        index: u32,
        on_complete: &mut Continue<'_>,
    ) -> Outcome<()> {
        if index == run.count {
            self.restore(run, machine);
            return on_complete(machine);
        }
        if index > 0 && self.is_init && machine.assigned == self.width {
            let guard = self.guard.as_ref().expect("a guard for the shortcut");
            for rest in index..run.count {
                self.bind(run, machine, rest);
                let value = run_deferred(machine, guard)?;
                if value == FALSE {
                    return Ok(());
                }
                if value != TRUE {
                    return Err(Bail("a conjunct that isn't a boolean"));
                }
            }
            self.restore(run, machine);
            return on_complete(machine);
        }
        self.bind(run, machine, index);
        // The rest of the conjunction rebinds the names for the next binding, so this binding's
        // walk gets them back once the rest returns.
        (self.body)(machine, &mut |machine: &mut Machine<'_>| {
            self.visit(run, machine, index + 1, on_complete)?;
            self.bind(run, machine, index);
            Ok(())
        })
    }

    fn run(&self, machine: &mut Machine<'_>, on_complete: &mut Continue<'_>) -> Outcome<()> {
        let mut sets = Vec::with_capacity(self.levels.len());
        let mut bindings = 1u32;
        for (set, slot) in &self.levels {
            let id = set(machine)?;
            let kind = machine.store.kind_of(id);
            if kind != KIND_SET && kind != KIND_TUPLE {
                return Err(Bail("an action quantified over a non-set"));
            }
            sets.push((id, bindings, machine.locals[*slot as usize]));
            bindings = bindings.wrapping_mul(machine.store.size_of(id));
        }
        let run = ForallRun {
            sets,
            count: bindings,
        };
        self.visit(&run, machine, 0, on_complete)
    }
}

/// What a lazily kept function applied in an action walks: its body at the argument.
struct LazyApplication {
    pattern: Pattern,
    set: NodeId,
    body: NodeId,
    base: Context,
    is_recursive: bool,
}

// The slots bound in a scope and the scopes its bindings close over, which ENABLED may read.
fn get_bound_slots(scope: &Option<Rc<Scope>>, slots: &mut Vec<u32>, seen: &mut HashSet<usize>) {
    let mut current = scope.clone();
    while let Some(node) = current {
        if !seen.insert(Rc::as_ptr(&node) as usize) {
            return;
        }
        match &node.binding {
            Binding::Slot(slot) => slots.push(*slot),
            Binding::Argument(argument) => {
                get_bound_slots(&super::argument_context(argument).scope, slots, seen)
            }
            Binding::Operator(operator) => {
                get_bound_slots(&super::operator_context(operator).scope, slots, seen)
            }
            _ => {}
        }
        current = node.parent.clone();
    }
}

impl<'a> Compiler<'a> {
    fn walk_depth(&mut self) -> Compiling<()> {
        if self.depth > super::MAXIMUM_EXPANSION {
            return unsupported("expansion too deep");
        }
        Ok(())
    }

    fn operator_text(&self, node: NodeId) -> Option<(&'a str, &'a [NodeId], bool)> {
        match self.node(node).1 {
            NodeKind::Apply { name, args } => Some((self.text(name.text), args, name.is_local)),
            _ => None,
        }
    }

    // --- what the walk needs to know about an expression ---

    /// What an expression that may be an action names: a user-defined operator expanded with its
    /// arguments, or a binding of an argument that is itself an action (`resolveAction`).
    pub(crate) fn resolve_action(
        &mut self,
        node: NodeId,
        context: &Context,
    ) -> Compiling<Option<(NodeId, Context)>> {
        match self.node(node).1 {
            NodeKind::Identifier(name) => {
                if name.is_local
                    && let Some(found) = lookup(&context.scope, name.text)
                {
                    return Ok(match &found.binding {
                        Binding::Argument(argument) => Some((
                            argument.expression,
                            super::argument_context(argument)
                                .primed(argument.context.is_primed || context.is_primed),
                        )),
                        _ => None,
                    });
                }
                let Resolution::Definition(index) = name.resolution else {
                    return Ok(None);
                };
                let definition = self.definition(self.ir.definitions[index as usize]);
                Ok(match (&definition.form, &definition.startup) {
                    (DefinitionForm::Operator(params), tla_ir::Startup::None)
                        if params.is_empty() =>
                    {
                        Some((definition.body, context.global(context.can_print)))
                    }
                    _ => None,
                })
            }
            NodeKind::Apply { name, args } => {
                if name.is_local
                    && let Some(found) = lookup(&context.scope, name.text)
                {
                    let Binding::Operator(operator) = &found.binding else {
                        return Ok(None);
                    };
                    let OperatorBody::Node(body) = operator.body else {
                        return Ok(None);
                    };
                    if operator.is_recursive {
                        return Ok(None);
                    }
                    let operator = Rc::clone(operator);
                    let base = super::operator_context(&operator)
                        .primed(context.is_primed || operator.context.is_primed);
                    let callee = self.bind_arguments(&operator.params, args, context, base)?;
                    return Ok(Some((body, callee)));
                }
                let Resolution::Definition(index) = name.resolution else {
                    return Ok(None);
                };
                let definition = self.definition(self.ir.definitions[index as usize]);
                let DefinitionForm::Operator(params) = &definition.form else {
                    return Ok(None);
                };
                if definition.flags & Definition::RECURSIVE != 0 {
                    return Ok(None);
                }
                let callee =
                    self.bind_arguments(params, args, context, context.global(context.can_print))?;
                Ok(Some((definition.body, callee)))
            }
            _ => Ok(None),
        }
    }

    // For f[e] where TLC keeps f lazy, a LET's function or a function constructor: the body of f
    // walked at e (`resolveLazyApplication`).
    fn resolve_lazy_application(
        &mut self,
        node: NodeId,
        context: &Context,
    ) -> Compiling<Option<LazyApplication>> {
        let NodeKind::FunctionApplication { function, args } = self.node(node).1 else {
            return Ok(None);
        };
        let (bounds, body, base, is_recursive) = match self.node(*function).1 {
            NodeKind::FunctionConstruction { bounds, body, .. } => {
                (bounds, *body, context.clone(), false)
            }
            NodeKind::Identifier(name) if name.is_local => {
                let Some(found) = lookup(&context.scope, name.text) else {
                    return Ok(None);
                };
                match &found.binding {
                    Binding::Recursive { definition } => {
                        let definition = self.definition(*definition);
                        let DefinitionForm::Function(bounds) = &definition.form else {
                            return Ok(None);
                        };
                        (
                            bounds,
                            definition.body,
                            context.with_scope(Some(Rc::clone(&found))),
                            true,
                        )
                    }
                    Binding::Value {
                        lazy: Some(lazy), ..
                    } => {
                        let definition = self.definition(lazy.definition);
                        let DefinitionForm::Function(bounds) = &definition.form else {
                            return Ok(None);
                        };
                        (
                            bounds,
                            definition.body,
                            context.with_scope(lazy.context.scope.clone()),
                            false,
                        )
                    }
                    _ => return Ok(None),
                }
            }
            _ => return Ok(None),
        };
        let [bound] = &bounds[..] else {
            return unsupported("walking a lazy function of several arguments");
        };
        if !matches!(bound.pattern, Pattern::Name(_)) || args.len() != 1 {
            return unsupported("walking a lazy function of several arguments");
        }
        Ok(Some(LazyApplication {
            pattern: bound.pattern.clone(),
            set: bound.set,
            body,
            base,
            is_recursive,
        }))
    }

    // The variable an expression such as x' (or x in the initial predicate) assigns, following
    // operator arguments and zero-arity definitions.
    fn get_assignable(
        &mut self,
        node: NodeId,
        context: &Context,
        is_primed: bool,
        depth: u32,
    ) -> Compiling<Option<u32>> {
        if depth > 50 {
            return Ok(None);
        }
        let name = match self.node(node).1 {
            NodeKind::Prime(inner) if is_primed => {
                return self.get_assignable(*inner, context, false, depth + 1);
            }
            NodeKind::Identifier(name) => *name,
            _ => return Ok(None),
        };
        if name.is_local {
            return match self.resolve_action(node, context)? {
                Some((body, inner)) => self.get_assignable(body, &inner, is_primed, depth + 1),
                None => Ok(None),
            };
        }
        if let Resolution::Variable(index) = name.resolution {
            return Ok(if is_primed { None } else { Some(index) });
        }
        match self.resolve_action(node, context)? {
            Some((body, inner)) => self.get_assignable(body, &inner, is_primed, depth + 1),
            None => Ok(None),
        }
    }

    fn get_assignable_index(
        &mut self,
        node: NodeId,
        context: &Context,
        is_init: bool,
    ) -> Compiling<Option<u32>> {
        self.get_assignable(node, context, !is_init, 0)
    }

    fn get_unchanged_indices(
        &mut self,
        node: NodeId,
        context: &Context,
        depth: u32,
    ) -> Compiling<Option<Vec<u32>>> {
        if depth > 50 {
            return Ok(None);
        }
        match self.node(node).1 {
            NodeKind::Tuple(elements) => {
                let mut indices = Vec::new();
                for &element in elements {
                    match self.get_unchanged_indices(element, context, depth + 1)? {
                        Some(found) => indices.extend(found),
                        None => return Ok(None),
                    }
                }
                Ok(Some(indices))
            }
            NodeKind::Identifier(name) => {
                if !name.is_local
                    && let Resolution::Variable(index) = name.resolution
                {
                    return Ok(Some(vec![index]));
                }
                match self.resolve_action(node, context)? {
                    Some((body, inner)) => self.get_unchanged_indices(body, &inner, depth + 1),
                    None => Ok(None),
                }
            }
            _ => Ok(None),
        }
    }

    // The engine follows names to what they're bound to as it compiles, so only a target under a
    // LET may assign a variable it can't find. TLC finds such a target as it runs.
    fn is_possibly_assignable(&self, node: NodeId) -> bool {
        matches!(self.node(node).1, NodeKind::Let { .. })
    }

    // Whether an expression is a guard, which TLC evaluates rather than walks.
    fn is_guard(&mut self, node: NodeId, context: &Context, is_init: bool) -> Compiling<bool> {
        match self.node(node).1 {
            NodeKind::Label { .. }
            | NodeKind::And(_)
            | NodeKind::Or(_)
            | NodeKind::Exists { .. }
            | NodeKind::Forall { .. }
            | NodeKind::If { .. }
            | NodeKind::Case { .. }
            | NodeKind::Let { .. }
            | NodeKind::Unchanged(_)
            | NodeKind::BoxAction { .. }
            | NodeKind::AngleAction { .. }
            | NodeKind::FunctionApplication { .. } => Ok(false),
            NodeKind::Identifier(_) => Ok(self.resolve_action(node, context)?.is_none()),
            NodeKind::Apply { name, args } => {
                let operator = self.text(name.text);
                if operator == "=>" {
                    return Ok(false);
                }
                if matches!(operator, "=" | "\\in" | "\\subseteq") && !args.is_empty() {
                    if self
                        .get_assignable_index(args[0], context, is_init)?
                        .is_some()
                    {
                        return Ok(false);
                    }
                    if self.is_possibly_assignable(args[0]) {
                        return Ok(false);
                    }
                }
                Ok(self.resolve_action(node, context)?.is_none())
            }
            _ => Ok(true),
        }
    }

    // The expressions directly inside one, as `collectChildren` finds them.
    fn children(&self, node: NodeId) -> Vec<NodeId> {
        let mut children = Vec::new();
        match self.node(node).1 {
            NodeKind::Number(_)
            | NodeKind::WideNumber(_)
            | NodeKind::Decimal(_)
            | NodeKind::String(_)
            | NodeKind::Identifier(_)
            | NodeKind::OperatorReference(_)
            | NodeKind::ExceptAt
            | NodeKind::Reference(_) => {}
            NodeKind::Apply { args, .. } => children.extend(args),
            NodeKind::Lambda { body, .. } => children.push(*body),
            NodeKind::And(operands)
            | NodeKind::Or(operands)
            | NodeKind::SetEnumeration(operands)
            | NodeKind::Tuple(operands)
            | NodeKind::Bracket(operands)
            | NodeKind::Product(operands) => children.extend(operands),
            NodeKind::Prime(inner)
            | NodeKind::Unchanged(inner)
            | NodeKind::Enabled(inner)
            | NodeKind::Always(inner)
            | NodeKind::Eventually(inner) => children.push(*inner),
            NodeKind::If {
                condition,
                consequent,
                alternative,
            } => children.extend([*condition, *consequent, *alternative]),
            NodeKind::Case { arms, other } => {
                for (condition, body) in arms {
                    children.extend([*condition, *body]);
                }
                children.extend(other);
            }
            NodeKind::Let {
                definitions, body, ..
            } => {
                children.extend(definitions);
                children.push(*body);
            }
            NodeKind::Forall { bounds, body }
            | NodeKind::Exists { bounds, body }
            | NodeKind::FunctionConstruction { bounds, body, .. } => {
                children.extend(bounds.iter().map(|bound| bound.set));
                children.push(*body);
            }
            NodeKind::SetMap { expression, bounds } => {
                children.push(*expression);
                children.extend(bounds.iter().map(|bound| bound.set));
            }
            NodeKind::UnboundedQuantifier { body, .. } => children.push(*body),
            NodeKind::Choose { set, body, .. } => {
                children.extend(set);
                children.push(*body);
            }
            NodeKind::SetFilter { predicate, .. } => children.push(*predicate),
            NodeKind::FunctionSet { domain, range } => children.extend([*domain, *range]),
            NodeKind::Record(fields) | NodeKind::RecordSet(fields) => {
                children.extend(fields.iter().map(|(_, value)| *value))
            }
            NodeKind::Except { function, updates } => {
                children.push(*function);
                for update in updates {
                    for step in &update.path {
                        if let tla_ir::PathStep::Index(indices) = step {
                            children.extend(indices);
                        }
                    }
                    children.push(update.value);
                }
            }
            NodeKind::FunctionApplication { function, args } => {
                children.push(*function);
                children.extend(args);
            }
            NodeKind::FieldAccess { record, .. } => children.push(*record),
            NodeKind::BoxAction { action, subscript }
            | NodeKind::AngleAction { action, subscript } => children.extend([*action, *subscript]),
            NodeKind::WeakFairness {
                subscript,
                action,
                enabled,
            }
            | NodeKind::StrongFairness {
                subscript,
                action,
                enabled,
            } => {
                children.extend([*subscript, *action]);
                children.extend(enabled);
            }
            NodeKind::Label { body, .. } => children.push(*body),
            NodeKind::Subexpression(selectors) => {
                for selector in selectors {
                    match selector {
                        tla_ir::Selector::Name { args, .. } | tla_ir::Selector::Bound(args) => {
                            children.extend(args)
                        }
                        _ => {}
                    }
                }
            }
            NodeKind::Definition(definition) => {
                if let DefinitionForm::Function(bounds) = &definition.form {
                    children.extend(bounds.iter().map(|bound| bound.set));
                }
                children.push(definition.body);
            }
        }
        children
    }

    // Whether an expression has a disjunction or an existential, for each of which TLC generates
    // a successor when it walks the expression; or, with `is_assigning`, whether walking it may
    // assign a variable.
    fn has_walk(
        &mut self,
        node: NodeId,
        context: &Context,
        is_assigning: bool,
        depth: u32,
    ) -> Compiling<bool> {
        if depth > 30 {
            return Ok(true);
        }
        let kind = self.node(node).1;
        let is_found = if is_assigning {
            matches!(kind, NodeKind::Prime(_) | NodeKind::Unchanged(_))
        } else {
            matches!(kind, NodeKind::Or(_) | NodeKind::Exists { .. })
        };
        if is_found {
            return Ok(true);
        }
        if matches!(kind, NodeKind::Apply { .. } | NodeKind::Identifier(_))
            && let Some((body, inner)) = self.resolve_action(node, context)?
            && self.has_walk(body, &inner, is_assigning, depth + 1)?
        {
            return Ok(true);
        }
        if matches!(kind, NodeKind::FunctionApplication { .. })
            && let Some(lazy) = self.resolve_lazy_application(node, context)?
            && self.has_walk(lazy.body, &lazy.base, is_assigning, depth + 1)?
        {
            return Ok(true);
        }
        for child in self.children(node) {
            if self.has_walk(child, context, is_assigning, depth + 1)? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn is_walked_body(&mut self, node: NodeId, context: &Context) -> Compiling<bool> {
        Ok(self.has_walk(node, context, true, 0)? || self.has_walk(node, context, false, 0)?)
    }

    // The elements of a set in the order TLC enumerates them where an action quantifies over the
    // set or assigns a variable from it: the set itself when TLC normalizes it. A set TLC keeps
    // lazy is the interpreter's to enumerate, so the TypeScript engine takes the model.
    fn compile_ordered(&mut self, node: NodeId, context: &Context) -> Compiling<Compiled> {
        let set = self.compile(node, context)?;
        if set.is_normalized {
            return Ok(set);
        }
        let line = self.ir.nodes.arena[node as usize].line;
        decline(format!(
            "enumerating a set TLC keeps lazy ({} at line {line})",
            self.describe_set(node, context)
        ))
    }

    fn describe_set(&self, node: NodeId, context: &Context) -> String {
        match self.node(node).1 {
            NodeKind::Identifier(name) => {
                if name.is_local
                    && let Some(found) = lookup(&context.scope, name.text)
                {
                    if let Binding::Argument(argument) = &found.binding {
                        return self
                            .describe_set(argument.expression, &super::argument_context(argument));
                    }
                    return self.text(name.text).to_string();
                }
                if let Resolution::Definition(index) = name.resolution {
                    let definition = self.definition(self.ir.definitions[index as usize]);
                    if matches!(&definition.form, DefinitionForm::Operator(params) if params.is_empty())
                    {
                        return format!(
                            "{}: {}",
                            self.text(name.text),
                            self.describe_set(definition.body, &Context::ROOT)
                        );
                    }
                }
                self.text(name.text).to_string()
            }
            NodeKind::Apply { name, .. } => self.text(name.text).to_string(),
            kind => super::nodes::kind_name(kind).to_string(),
        }
    }

    // --- the walk ---

    /// Compiles the walk of an action, or of the initial predicate.
    pub(crate) fn compile_step(
        &mut self,
        node: NodeId,
        context: &Context,
        options: WalkOptions,
    ) -> Compiling<Step> {
        self.depth += 1;
        let result = self
            .walk_depth()
            .and_then(|()| self.compile_step_kind(node, context, options));
        self.depth -= 1;
        result
    }

    fn guard_step(&mut self, node: NodeId, context: &Context) -> Compiling<Step> {
        let evaluate = self.compile(node, context)?.eval;
        Ok(step(move |machine, on_complete| {
            let value = evaluate(machine)?;
            if value == TRUE {
                on_complete(machine)
            } else if value == FALSE {
                Ok(())
            } else {
                Err(Bail("a guard that isn't a boolean"))
            }
        }))
    }

    fn compile_step_kind(
        &mut self,
        node: NodeId,
        context: &Context,
        options: WalkOptions,
    ) -> Compiling<Step> {
        let is_init = options.is_init;
        match self.node(node).1 {
            NodeKind::And(operands) => self.compile_conjunction(operands, context, options),
            NodeKind::Or(operands) => self.compile_disjunction(operands, context, options),
            NodeKind::Exists { bounds, body } => {
                let mut inner = context.clone();
                let mut levels = Vec::new();
                for bound in bounds {
                    if !matches!(bound.pattern, Pattern::Name(_)) {
                        return unsupported("a tuple pattern in an action's \\E");
                    }
                    let set = self.compile_ordered(bound.set, &inner)?;
                    let binder = self.bind_bound(&bound.pattern, &inner);
                    inner = binder.context;
                    levels.push((set.eval, binder.slots[0]));
                }
                let body = self.compile_step(*body, &inner, options)?;
                Ok(exists_step(levels, body))
            }
            NodeKind::Forall { bounds, body } => {
                if !self.is_walked_body(*body, context)? {
                    return self.guard_step(node, context);
                }
                let mut inner = context.clone();
                let mut levels = Vec::new();
                for bound in bounds {
                    if !matches!(bound.pattern, Pattern::Name(_)) {
                        return unsupported("a tuple pattern in an action's \\A");
                    }
                    let set = self.compile_ordered(bound.set, &inner)?;
                    let binder = self.bind_bound(&bound.pattern, &inner);
                    inner = binder.context;
                    levels.push((set.eval, binder.slots[0]));
                }
                let walk = self.compile_step(*body, &inner, options)?;
                let guard = is_init.then(|| deferred(self.compile(*body, &inner)));
                let forall = Arc::new(WalkedForall {
                    levels,
                    body: walk,
                    guard,
                    is_init,
                    width: self.ir.variables.len() as u32,
                });
                Ok(step(move |machine, on_complete| {
                    forall.run(machine, on_complete)
                }))
            }
            NodeKind::If {
                condition,
                consequent,
                alternative,
            } => {
                let condition = self.compile(*condition, context)?.eval;
                let consequent = self.compile_step(*consequent, context, options)?;
                let alternative = self.compile_step(*alternative, context, options)?;
                Ok(step(move |machine, on_complete| {
                    let value = condition(machine)?;
                    if value == TRUE {
                        consequent(machine, on_complete)
                    } else if value == FALSE {
                        alternative(machine, on_complete)
                    } else {
                        Err(Bail("an IF condition that isn't a boolean"))
                    }
                }))
            }
            NodeKind::Case { arms, other } => {
                let mut compiled = Vec::with_capacity(arms.len());
                for &(condition, body) in arms {
                    let condition = self.compile(condition, context)?.eval;
                    compiled.push((condition, self.compile_step(body, context, options)?));
                }
                let other = match other {
                    Some(other) => Some(self.compile_step(*other, context, options)?),
                    None => None,
                };
                Ok(step(move |machine, on_complete| {
                    for (condition, body) in &compiled {
                        let value = condition(machine)?;
                        if value == TRUE {
                            return body(machine, on_complete);
                        }
                        if value != FALSE {
                            return Err(Bail("a CASE condition that isn't a boolean"));
                        }
                    }
                    match &other {
                        Some(other) => other(machine, on_complete),
                        None => Err(Bail("no CASE arm holds")),
                    }
                }))
            }
            NodeKind::Let {
                instances,
                definitions,
                body,
            } => {
                let inner = self.bind_let_definitions(*instances, definitions, context)?;
                self.compile_step(*body, &inner, options)
            }
            NodeKind::Unchanged(expression) => {
                if is_init {
                    return unsupported("UNCHANGED in the initial predicate");
                }
                self.compile_unchanged_step(*expression, context, options)
            }
            NodeKind::AngleAction { action, subscript } => {
                let body = self.compile_step(*action, context, options)?;
                let subscript = *subscript;
                let unchanged = self
                    .wrap_compile(|compiler| compiler.compile_unchanged(subscript, context))?
                    .eval;
                Ok(step(move |machine, on_complete| {
                    body(machine, &mut |machine: &mut Machine<'_>| {
                        if unchanged(machine)? == FALSE {
                            on_complete(machine)
                        } else {
                            Ok(())
                        }
                    })
                }))
            }
            NodeKind::BoxAction { action, subscript } => {
                let action = self.compile_step(*action, context, options)?;
                let unchanged = self.compile_unchanged_step(*subscript, context, options)?;
                Ok(step(move |machine, on_complete| {
                    action(machine, on_complete)?;
                    unchanged(machine, on_complete)
                }))
            }
            NodeKind::Label { body, .. } => self.compile_step(*body, context, options),
            NodeKind::FunctionApplication { args, .. } => {
                let Some(lazy) = self.resolve_lazy_application(node, context)? else {
                    return self.guard_step(node, context);
                };
                if !self.is_walked_body(lazy.body, &lazy.base)? {
                    return self.guard_step(node, context);
                }
                if lazy.is_recursive {
                    return unsupported("walking a recursive function in an action");
                }
                let argument = self.compile(args[0], context)?.eval;
                let set = self.compile(lazy.set, &lazy.base)?;
                let member: Member = self.member_test(&set);
                let binder = self.bind_bound(&lazy.pattern, &lazy.base);
                let slot = binder.slots[0];
                let walk = self.compile_step(lazy.body, &binder.context, options)?;
                Ok(step(move |machine, on_complete| {
                    let value = argument(machine)?;
                    if !member(machine, value)? {
                        return Err(Bail("applied a function outside its domain"));
                    }
                    let value = argument(machine)?;
                    machine.locals[slot as usize] = value;
                    walk(machine, on_complete)
                }))
            }
            NodeKind::Identifier(_) => match self.resolve_action(node, context)? {
                Some((body, inner)) => self.compile_step(body, &inner, options),
                None => self.guard_step(node, context),
            },
            NodeKind::Apply { name, args } => {
                let operator = self.text(name.text);
                if !name.is_local && matches!(operator, "=" | "\\in" | "\\subseteq") {
                    if let Some(variable) = self.get_assignable_index(args[0], context, is_init)? {
                        return match operator {
                            "=" => self.compile_conjunction(&[node], context, options),
                            "\\subseteq" => unsupported("x' \\subseteq S"),
                            _ => self.compile_membership(variable, args[1], node, context, options),
                        };
                    }
                    if self.is_possibly_assignable(args[0]) {
                        let line = self.ir.nodes.arena[node as usize].line;
                        return unsupported(format!(
                            "an assignment the engine can't resolve statically at line {line}"
                        ));
                    }
                }
                if !name.is_local && operator == "=>" {
                    let condition = self.compile(args[0], context)?.eval;
                    let right = self.compile_step(args[1], context, options)?;
                    return Ok(step(move |machine, on_complete| {
                        let value = condition(machine)?;
                        if value == FALSE {
                            on_complete(machine)
                        } else if value == TRUE {
                            right(machine, on_complete)
                        } else {
                            Err(Bail("the left side of => isn't a boolean"))
                        }
                    }));
                }
                if !name.is_local && operator == "/\\" {
                    return self.compile_conjunction(args, context, options);
                }
                if !name.is_local && operator == "\\/" {
                    return self.compile_disjunction(args, context, options);
                }
                match self.resolve_action(node, context)? {
                    Some((body, inner)) => self.compile_step(body, &inner, options),
                    None => self.guard_step(node, context),
                }
            }
            _ => self.guard_step(node, context),
        }
    }

    fn compile_disjunction(
        &mut self,
        operands: &[NodeId],
        context: &Context,
        options: WalkOptions,
    ) -> Compiling<Step> {
        let branches = operands
            .iter()
            .map(|&operand| self.compile_step(operand, context, options))
            .collect::<Compiling<Vec<Step>>>()?;
        Ok(step(move |machine, on_complete| {
            for branch in &branches {
                branch(machine, on_complete)?;
            }
            Ok(())
        }))
    }

    // UNCHANGED e as a step: an assignment or test of each variable of e, or a guard.
    fn compile_unchanged_step(
        &mut self,
        expression: NodeId,
        context: &Context,
        options: WalkOptions,
    ) -> Compiling<Step> {
        if let Some(indices) = self.get_unchanged_indices(expression, context, 0)? {
            let conjunction = Arc::new(Conjunction {
                conjuncts: vec![Conjunct::Unchanged(indices)],
                guards: vec![None],
                walked_from: vec![false],
                options,
                width: self.ir.variables.len() as u32,
            });
            return Ok(step(move |machine, on_complete| {
                run_from(&conjunction, machine, 0, on_complete)
            }));
        }
        let evaluate = self
            .wrap_compile(|compiler| compiler.compile_unchanged(expression, context))?
            .eval;
        Ok(step(move |machine, on_complete| {
            let value = evaluate(machine)?;
            if value == TRUE {
                on_complete(machine)
            } else if value == FALSE {
                Ok(())
            } else {
                Err(Bail("a guard that isn't a boolean"))
            }
        }))
    }

    fn conjunct_of(
        &mut self,
        operand: NodeId,
        context: &Context,
        options: WalkOptions,
    ) -> Compiling<Conjunct> {
        if let Some(("=", args, false)) = self.operator_text(operand)
            && let Some(variable) = self.get_assignable_index(args[0], context, options.is_init)?
        {
            let value = self.compile(args[1], context)?.eval;
            return Ok(Conjunct::Assign { variable, value });
        }
        if !options.is_init
            && let NodeKind::Unchanged(expression) = self.node(operand).1
            && let Some(indices) = self.get_unchanged_indices(*expression, context, 0)?
        {
            return Ok(Conjunct::Unchanged(indices));
        }
        if self.is_guard(operand, context, options.is_init)? {
            return Ok(Conjunct::Guard(self.compile(operand, context)?.eval));
        }
        Ok(Conjunct::Branch(
            self.compile_step(operand, context, options)?,
        ))
    }

    fn compile_conjunction(
        &mut self,
        operands: &[NodeId],
        context: &Context,
        options: WalkOptions,
    ) -> Compiling<Step> {
        let conjuncts = operands
            .iter()
            .map(|&operand| self.conjunct_of(operand, context, options))
            .collect::<Compiling<Vec<Conjunct>>>()?;
        let guards = conjuncts
            .iter()
            .enumerate()
            .map(|(index, conjunct)| match conjunct {
                _ if index == 0 || !options.is_shortcut => None,
                Conjunct::Guard(evaluate) => Some(Ok(evaluate.clone())),
                _ => Some(deferred(self.compile(operands[index], context))),
            })
            .collect();
        let walked_from = (0..conjuncts.len())
            .map(|index| {
                !options.is_init
                    && conjuncts[index..]
                        .iter()
                        .any(|conjunct| matches!(conjunct, Conjunct::Branch(_)))
            })
            .collect();
        let conjunction = Arc::new(Conjunction {
            conjuncts,
            guards,
            walked_from,
            options,
            width: self.ir.variables.len() as u32,
        });
        Ok(step(move |machine, on_complete| {
            run_from(&conjunction, machine, 0, on_complete)
        }))
    }

    fn compile_membership(
        &mut self,
        variable: u32,
        set: NodeId,
        guard: NodeId,
        context: &Context,
        options: WalkOptions,
    ) -> Compiling<Step> {
        let set = self.compile_ordered(set, context)?.eval;
        let guard = self.compile(guard, context)?.eval;
        let is_init = options.is_init;
        let index = variable as usize;
        Ok(step(move |machine, on_complete| {
            if target(machine, is_init)[index] != UNASSIGNED {
                let value = guard(machine)?;
                return if value == TRUE {
                    on_complete(machine)
                } else if value == FALSE {
                    Ok(())
                } else {
                    Err(Bail("a guard that isn't a boolean"))
                };
            }
            let id = set(machine)?;
            let size = expect_set_size(machine, id)?;
            machine.assigned += 1;
            for position in 0..size {
                let element = machine.store.element_at(id, position);
                target(machine, is_init)[index] = element;
                on_complete(machine)?;
            }
            target(machine, is_init)[index] = UNASSIGNED;
            machine.assigned -= 1;
            Ok(())
        }))
    }

    // --- ENABLED ---

    // Whether A has a successor depends only on what A reads of the current state and the names
    // bound around it. The footprint of A as a predicate says what that is; if the engine can't
    // compile it so, ENABLED reads everything.
    fn get_enabled_footprint(&mut self, action: NodeId, context: &Context) -> Compiling<Footprint> {
        match self.compile(action, &context.primed(false)) {
            Ok(compiled) => Ok(Footprint {
                vars: compiled.footprint.vars,
                primes: Vec::new(),
                slots: compiled.footprint.slots,
            }),
            Err(CompileError::Bail(_)) => {
                let mut slots = Vec::new();
                get_bound_slots(&context.scope, &mut slots, &mut HashSet::new());
                slots.sort_unstable();
                slots.dedup();
                Ok(Footprint {
                    vars: (0..self.ir.variables.len() as u32).collect(),
                    primes: Vec::new(),
                    slots,
                })
            }
            Err(decline) => Err(decline),
        }
    }

    /// ENABLED A runs A from the current state until its first successor, on a next state of its
    /// own, as TLC's ENABLED does: without the shortcut once every variable is assigned.
    pub(crate) fn compile_enabled(
        &mut self,
        action: NodeId,
        context: &Context,
    ) -> Compiling<Compiled> {
        if context.is_primed || context.is_init {
            return unsupported("expression Enabled");
        }
        let walk = self.compile_step(
            action,
            context,
            WalkOptions {
                is_init: false,
                is_shortcut: false,
            },
        )?;
        let footprint = self.get_enabled_footprint(action, context)?;
        if footprint
            .slots
            .iter()
            .any(|slot| SEARCH_SLOTS.contains(slot))
        {
            return unsupported("ENABLED of an action that reads TLCGet");
        }
        let width = self.ir.variables.len();
        Ok(Compiled {
            is_costly: true,
            is_boolean: true,
            ..leaf(
                eval(move |machine| {
                    let mut next = machine.spare_states.pop().unwrap_or_default();
                    next.clear();
                    next.resize(width, UNASSIGNED);
                    let outer = std::mem::replace(&mut machine.next, next);
                    let assigned = std::mem::replace(&mut machine.assigned, 0);
                    let mark = machine.undo.len();
                    let result = walk(machine, &mut |_: &mut Machine<'_>| Err(Bail(FOUND)));
                    let inner = std::mem::replace(&mut machine.next, outer);
                    machine.spare_states.push(inner);
                    machine.assigned = assigned;
                    machine.undo.truncate(mark);
                    match result {
                        Ok(()) => Ok(FALSE),
                        Err(bail) if is_found(&bail) => Ok(TRUE),
                        Err(bail) => Err(bail),
                    }
                }),
                footprint,
            )
        })
    }
}

fn exists_step(levels: Vec<(Eval, u32)>, body: Step) -> Step {
    if let [(set, slot)] = &levels[..] {
        let (set, slot) = (set.clone(), *slot as usize);
        return step(move |machine, on_complete| {
            let id = set(machine)?;
            let size = expect_set_size(machine, id)?;
            for position in 0..size {
                machine.locals[slot] = machine.store.element_at(id, position);
                body(machine, on_complete)?;
            }
            Ok(())
        });
    }
    // TLC's ContextEnumerator varies the first bound fastest: the last bound is the outer loop.
    step(move |machine, on_complete| {
        let mut sets = Vec::with_capacity(levels.len());
        let mut is_empty = false;
        for (set, _) in &levels {
            let id = set(machine)?;
            if expect_set_size(machine, id)? == 0 {
                is_empty = true;
            }
            sets.push(id);
        }
        if is_empty {
            return Ok(());
        }
        let mut positions = vec![0u32; levels.len()];
        loop {
            for (level, &(_, slot)) in levels.iter().enumerate() {
                machine.locals[slot as usize] =
                    machine.store.element_at(sets[level], positions[level]);
            }
            body(machine, on_complete)?;
            let mut level = 0;
            while level < levels.len() {
                positions[level] += 1;
                if positions[level] < machine.store.size_of(sets[level]) {
                    break;
                }
                positions[level] = 0;
                level += 1;
            }
            if level == levels.len() {
                return Ok(());
            }
        }
    })
}

impl<'a> Compiler<'a> {
    /// The context an instance's scope stands for, or `None` for one that binds what the engine
    /// can't translate, such as a builtin (`contextFromScope`).
    fn context_from_scope(&mut self, scope: Option<Index>) -> Compiling<Option<Context>> {
        let Some(index) = scope else {
            return Ok(Some(Context::ROOT));
        };
        if let Some(known) = self.scope_contexts.get(&index) {
            return Ok(known.clone());
        }
        let translated = self.translate_scope(index)?;
        self.scope_contexts.insert(index, translated.clone());
        Ok(translated)
    }

    fn translate_scope(&mut self, index: Index) -> Compiling<Option<Context>> {
        let ir = self.ir;
        let scope = &ir.scopes[index as usize];
        let Some(parent) = self.context_from_scope(scope.parent)? else {
            return Ok(None);
        };
        // A closure or thunk in the reference may close over the scope that binds it, so a binding
        // whose scope is its own node reaches the scope that binds it once that exists.
        let mut own_scope: Option<&RefCell<std::rc::Weak<Scope>>> = None;
        let binding = match &scope.binding {
            ScopeBinding::Value(Some(value)) => Binding::Value {
                compiled: Box::new(super::constant(self.intern_value(*value)?)),
                lazy: None,
            },
            ScopeBinding::Value(None) => {
                return decline("a value in an instance's scope the IR can't hold");
            }
            ScopeBinding::Thunk { expression, scope } => {
                let context = if *scope == Some(index) {
                    parent.clone()
                } else {
                    match self.context_from_scope(*scope)? {
                        Some(context) => context,
                        None => return Ok(None),
                    }
                };
                Binding::Argument(Rc::new(super::Argument {
                    expression: *expression,
                    context,
                    compiled: RefCell::new([None, None]),
                    own_scope: RefCell::new(std::rc::Weak::new()),
                }))
            }
            ScopeBinding::Closure {
                params,
                body,
                scope,
                ..
            } => {
                let context = if *scope == Some(index) {
                    parent.clone()
                } else {
                    match self.context_from_scope(*scope)? {
                        Some(context) => context,
                        None => return Ok(None),
                    }
                };
                Binding::Operator(super::Operator::new(
                    params.clone(),
                    OperatorBody::Node(*body),
                    context,
                ))
            }
            ScopeBinding::Opaque => return Ok(None),
        };
        let is_self = matches!(
            &scope.binding,
            ScopeBinding::Thunk { scope: inner, .. } | ScopeBinding::Closure { scope: inner, .. }
                if *inner == Some(index)
        );
        let bound = super::bind(&parent.scope, scope.name, binding);
        if is_self && let Some(node) = &bound {
            match &node.binding {
                Binding::Argument(argument) => own_scope = Some(&argument.own_scope),
                Binding::Operator(operator) => own_scope = Some(&operator.own_scope),
                _ => {}
            }
            if let Some(own) = own_scope {
                *own.borrow_mut() = Rc::downgrade(node);
            }
        }
        Ok(Some(parent.with_scope(bound)))
    }

    /// Compiles the walk of the initial predicate (`is_init`) or of an action in the scope of an
    /// instance, as `buildStep` does in `context.ts`.
    pub fn compile_action(
        &mut self,
        node: NodeId,
        scope: Option<Index>,
        options: ActionOptions,
        what: &str,
    ) -> Result<Step, CompileError> {
        let Some(context) = self.context_from_scope(scope)? else {
            return unsupported(format!("{what} scope the engine can't translate"));
        };
        let (is_init, is_shortcut) = (options.is_init, options.is_shortcut);
        let context = Context {
            is_init,
            can_print: options.can_print,
            ..context
        };
        self.compile_step(
            node,
            &context,
            WalkOptions {
                is_init,
                is_shortcut,
            },
        )
    }

    /// Compiles an expression in the scope of an instance, or `None` when the engine can't
    /// translate the scope.
    pub fn compile_in_scope(
        &mut self,
        node: NodeId,
        scope: Option<Index>,
    ) -> Result<Option<Compiled>, CompileError> {
        let Some(context) = self.context_from_scope(scope)? else {
            return Ok(None);
        };
        self.compile(node, &context).map(Some)
    }
}

impl<'a> Compiler<'a> {
    /// Compiles ENABLED of an action in the scope of an instance, as the liveness checker's
    /// ENABLED atoms are compiled, or `None` when the engine can't translate the scope.
    pub fn compile_enabled_in_scope(
        &mut self,
        action: NodeId,
        scope: Option<Index>,
    ) -> Result<Option<Compiled>, CompileError> {
        let Some(context) = self.context_from_scope(scope)? else {
            return Ok(None);
        };
        self.compile_enabled(action, &context).map(Some)
    }
}
