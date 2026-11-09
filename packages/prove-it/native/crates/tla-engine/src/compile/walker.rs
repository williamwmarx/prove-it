//! Walks the initial predicate and the next-state relation in the order TLC does, as `action.ts`
//! (and `codegen.ts`, which writes the same walk out as code) does. It walks conjunctions,
//! disjunctions, quantifiers and operators as TLC's Tool does, assigning a variable at its first
//! conjunct of the form x' = e or x' \in S, and evaluating every other conjunct as a guard.
//!
//! A walk is a [`Step`]: it calls its continuation once for each state it completes. It is compiled
//! path by path, as `codegen.ts` writes it out: a branch of a conjunction is compiled with the
//! conjuncts after it as its rest, and each conjunct knows which variables its path has assigned,
//! so it assigns or tests without checking, and only where a path can't know does it check at run
//! time.

use std::cell::RefCell;
use std::collections::HashSet;
use std::rc::Rc;
use std::sync::Arc;

use tla_ir::{Index, NodeId, NodeKind, Pattern, Resolution, ScopeBinding};
use tla_values::store::{FALSE, KIND_SET, KIND_TUPLE, Outcome, TRUE};
use tla_values::{Bail, Id};

use super::nodes::assign_bound;
use super::predicate::{self, Leaf, Predicate, Test};
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

/// The set an action enumerates: a set, or the tuple of a lazy set's elements in TLC's order.
#[derive(Clone)]
struct Ordered {
    eval: Eval,
    is_ordered: bool,
}

impl Ordered {
    fn size(&self, machine: &Machine<'_>, id: Id) -> Outcome<u32> {
        if self.is_ordered || machine.store.kind_of(id) == KIND_SET {
            Ok(machine.store.size_of(id))
        } else {
            Err(Bail("an action quantified over a non-set"))
        }
    }
}

/// What a walk does once a conjunct is done: a step, or, for `None`, the walk's own continuation.
/// The walk is compiled path by path, as `codegen.ts` writes it out: each conjunct knows the step
/// after it, so nothing at run time builds a continuation or keeps an undo stack.
type Rest = Option<Step>;

#[inline(always)]
fn run_rest(rest: &Rest, machine: &mut Machine<'_>, on_complete: &mut Continue<'_>) -> Outcome<()> {
    match rest {
        Some(step) => step(machine, on_complete),
        None => on_complete(machine),
    }
}

// Whether a variable is unassigned, assigned, or either, on the path being compiled (`UNASSIGNED`,
// `ASSIGNED` and `UNKNOWN` in `codegen.ts`).
const UNSET: u8 = 0;
const SET: u8 = 1;
const EITHER: u8 = 2;

/// What the walk knows of each variable on a path, the variables past `states` being `beyond`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Known {
    states: Vec<u8>,
    beyond: u8,
}

/// Whether TLC's shortcut past the rest of a conjunction applies on a path, which it does where
/// every variable has a value (`registers.assigned` equals the width).
enum Shortcut {
    Never,
    Always,
    Maybe,
}

impl Known {
    /// A walk starts with every variable unassigned.
    fn start() -> Known {
        Known {
            states: Vec::new(),
            beyond: UNSET,
        }
    }

    /// Nothing known, which is right on every path.
    fn unknown() -> Known {
        Known {
            states: Vec::new(),
            beyond: EITHER,
        }
    }

    fn get(&self, variable: u32) -> u8 {
        self.states
            .get(variable as usize)
            .copied()
            .unwrap_or(self.beyond)
    }

    fn with(&self, variable: u32, state: u8) -> Known {
        let mut known = self.clone();
        let index = variable as usize;
        if known.states.len() <= index {
            known.states.resize(index + 1, known.beyond);
        }
        known.states[index] = state;
        known
    }

    /// After a walk the compiler doesn't follow: what was assigned still is, and the rest may be.
    fn opaque(&self) -> Known {
        Known {
            states: self
                .states
                .iter()
                .map(|&state| if state == SET { SET } else { EITHER })
                .collect(),
            beyond: EITHER,
        }
    }

    // How many variables are assigned at least, and how many more may be.
    fn shortcut(&self, width: u32) -> Shortcut {
        let assigned = self.states.iter().filter(|&&state| state == SET).count() as u64;
        let either = if self.beyond == EITHER {
            u64::MAX
        } else {
            self.states.iter().filter(|&&state| state == EITHER).count() as u64
        };
        let width = u64::from(width);
        if either == 0 {
            if assigned == width {
                Shortcut::Always
            } else {
                Shortcut::Never
            }
        } else if assigned > width || assigned.saturating_add(either) < width {
            Shortcut::Never
        } else {
            Shortcut::Maybe
        }
    }
}

/// The continuation a compile of a walk takes: given what is known on a path, the rest of the walk
/// after it. It may be asked for several paths, so callers that branch share it through
/// [`Shared`].
type Then<'t, 'a> = dyn FnMut(&mut Compiler<'a>, &Known) -> Compiling<Rest> + 't;

/// A continuation compiled once for each thing known on the paths that reach it: a few, and past
/// those once for nothing known, so a walk compiles in time linear in its size. Each compile of a
/// branching conjunct shares its own continuation, so the walk as a whole also has a budget:
/// independent branches would otherwise compile the rest of the walk once per combination of
/// them.
struct Shared<'s, 't, 'a> {
    then: &'s mut Then<'t, 'a>,
    compiled: Vec<(Known, Rest)>,
}

const SHARED_PATHS: usize = 4;

const WALK_SPECIALISATIONS: usize = 256;

impl<'s, 't, 'a> Shared<'s, 't, 'a> {
    fn new(then: &'s mut Then<'t, 'a>) -> Self {
        Shared {
            then,
            compiled: Vec::new(),
        }
    }

    fn call(&mut self, compiler: &mut Compiler<'a>, known: &Known) -> Compiling<Rest> {
        let known = if (self.compiled.len() >= SHARED_PATHS
            || compiler.specialisations >= WALK_SPECIALISATIONS)
            && !self.compiled.iter().any(|(seen, _)| seen == known)
        {
            Known::unknown()
        } else {
            known.clone()
        };
        if let Some((_, rest)) = self.compiled.iter().find(|(seen, _)| *seen == known) {
            return Ok(rest.clone());
        }
        compiler.specialisations += 1;
        let rest = (self.then)(compiler, &known)?;
        self.compiled.push((known, rest.clone()));
        Ok(rest)
    }
}

/// What an assignment assigns: an expression's value, or the variable's current value, as
/// UNCHANGED assigns it.
#[derive(Clone)]
enum Source {
    Value(Eval),
    Current,
}

/// One conjunct, or one variable of an UNCHANGED, of a run of them the compiler knows the
/// assignments of on its path.
enum Op {
    /// A guard, or one conjunct of the rest TLC's shortcut evaluates, failing with its reason.
    Check(Eval, &'static str),
    /// A guard whose value is a fused predicate's, which is always a boolean.
    Holds(Test),
    /// An assignment of a variable unassigned on the path.
    Assign(u32, Source),
    /// An assignment of a variable assigned on the path: an equality test.
    Test(u32, Source),
    /// TLC's shortcut passes a conjunct it would walk (`shortcuts.isPastWalk`).
    PastWalk,
}

#[inline(always)]
fn read_source(machine: &mut Machine<'_>, source: &Source, variable: u32) -> Outcome<Id> {
    match source {
        Source::Value(value) => value(machine),
        Source::Current => Ok(machine.cur[variable as usize]),
    }
}

/// A run of conjuncts, then the rest of the walk. Its assignments are undone in reverse once the
/// rest returns, or once a conjunct stops it, as each conjunction of `action.ts` unassigns its own.
struct Segment<const IS_INIT: bool> {
    ops: Box<[Op]>,
    // The variables the ops assign, in order, for the undo.
    assigns: Box<[u32]>,
    rest: Rest,
}

impl<const IS_INIT: bool> Segment<IS_INIT> {
    // Applies one conjunct: whether the walk goes on past it.
    #[inline(always)]
    fn apply(&self, machine: &mut Machine<'_>, op: &Op) -> Outcome<bool> {
        match op {
            Op::Check(evaluate, reason) => match evaluate(machine)? {
                TRUE => Ok(true),
                FALSE => Ok(false),
                _ => Err(Bail(reason)),
            },
            Op::Holds(test) => test(machine),
            Op::Assign(variable, source) => {
                let value = read_source(machine, source, *variable)?;
                target(machine, IS_INIT)[*variable as usize] = value;
                machine.assigned += 1;
                Ok(true)
            }
            Op::Test(variable, source) => {
                let value = read_source(machine, source, *variable)?;
                let current = target(machine, IS_INIT)[*variable as usize];
                Ok(current == value || machine.store.equals(current, value)?)
            }
            Op::PastWalk => {
                machine.is_past_walk = true;
                Ok(true)
            }
        }
    }

    fn run(&self, machine: &mut Machine<'_>, on_complete: &mut Continue<'_>) -> Outcome<()> {
        let mut count = 0;
        let result = 'walk: {
            for op in &self.ops {
                match self.apply(machine, op) {
                    Ok(true) => count += usize::from(matches!(op, Op::Assign(..))),
                    Ok(false) => break 'walk Ok(()),
                    Err(bail) => break 'walk Err(bail),
                }
            }
            run_rest(&self.rest, machine, on_complete)
        };
        for &variable in self.assigns[..count].iter().rev() {
            target(machine, IS_INIT)[variable as usize] = UNASSIGNED;
        }
        machine.assigned -= count as u32;
        result
    }
}

// A guard, tested in place where it compiled to a fused predicate.
fn guard(compiled: Compiled) -> Op {
    match &compiled.predicate {
        Some(predicate) => Op::Holds(predicate.build()),
        None => Op::Check(compiled.eval, "a conjunct that isn't a boolean"),
    }
}

// A walk's first step, a guard `f[k] = c` or `f[k] # c`, with `f[k]` a variable applied to one
// bound name or, twice, to two.
#[derive(Clone, Copy)]
pub(crate) struct Leading {
    read: Read,
    constant: Id,
    is_equal: bool,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Read {
    Apply {
        variable: u32,
        slot: u32,
    },
    Apply2 {
        variable: u32,
        slot: u32,
        second: u32,
    },
}

impl Leading {
    fn of(compiled: &Compiled) -> Option<Leading> {
        let Predicate::Equal {
            left,
            right: Leaf::Constant(constant),
            is_equal,
        } = &**compiled.predicate.as_ref()?
        else {
            return None;
        };
        let read = match *left {
            Leaf::ApplyVar { variable, slot, .. } => Read::Apply { variable, slot },
            Leaf::ApplyVar2 {
                variable,
                slot,
                second,
            } => Read::Apply2 {
                variable,
                slot,
                second,
            },
            _ => return None,
        };
        Some(Leading {
            read,
            constant: *constant,
            is_equal: *is_equal,
        })
    }
}

impl Read {
    fn run(self, machine: &mut Machine<'_>) -> Outcome<Id> {
        match self {
            Read::Apply { variable, slot } => {
                let function = machine.read_current(variable)?;
                machine.store.apply(function, machine.locals[slot as usize])
            }
            Read::Apply2 {
                variable,
                slot,
                second,
            } => predicate::apply_var2(machine, variable, slot, second),
        }
    }
}

fn step_address(step: &Step) -> usize {
    Arc::as_ptr(step).cast::<()>() as usize
}

// A run of conjuncts before the rest, or the rest alone.
fn segment(ops: Vec<Op>, rest: Rest, is_init: bool) -> Rest {
    if ops.is_empty() {
        return rest;
    }
    let assigns = ops
        .iter()
        .filter_map(|op| match op {
            Op::Assign(variable, _) => Some(*variable),
            _ => None,
        })
        .collect();
    let ops = ops.into_boxed_slice();
    Some(if is_init {
        let segment = Segment::<true> { ops, assigns, rest };
        step(move |machine, on_complete| segment.run(machine, on_complete))
    } else {
        let segment = Segment::<false> { ops, assigns, rest };
        step(move |machine, on_complete| segment.run(machine, on_complete))
    })
}

// An assignment of a variable that may or may not be assigned on the path: it assigns or tests,
// as the run-time check decides.
fn either_step(variable: u32, source: Source, rest: Rest, is_init: bool) -> Step {
    let index = variable as usize;
    step(move |machine, on_complete| {
        let value = read_source(machine, &source, variable)?;
        let current = target(machine, is_init)[index];
        if current == UNASSIGNED {
            target(machine, is_init)[index] = value;
            machine.assigned += 1;
            let result = run_rest(&rest, machine, on_complete);
            target(machine, is_init)[index] = UNASSIGNED;
            machine.assigned -= 1;
            return result;
        }
        if current == value || machine.store.equals(current, value)? {
            return run_rest(&rest, machine, on_complete);
        }
        Ok(())
    })
}

// A deferred compile as an expression, which fails only once the walk evaluates it.
fn deferred_eval(deferred: Deferred) -> Eval {
    match deferred {
        Ok(evaluate) => evaluate,
        Err(bail) => Arc::new(move |_: &mut Machine<'_>| Err(bail)),
    }
}

/// A conjunct of a conjunction, as the walk treats it: assigning, an UNCHANGED of variables, a
/// guard, or walked.
#[derive(Clone)]
enum Shape {
    Assign(u32, NodeId),
    Unchanged(Rc<[u32]>),
    Guard,
    Branch,
}

#[derive(Clone)]
struct Item {
    node: NodeId,
    shape: Shape,
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
    sets: Vec<(Id, u64, Id)>,
    count: u64,
}

impl WalkedForall {
    // Binds the names for binding `index`, numbered with the first name varying fastest.
    fn bind(&self, run: &ForallRun, machine: &mut Machine<'_>, index: u64) {
        let binding = if index == 0 { 0 } else { run.count - index };
        for (level, &(set, stride, _)) in run.sets.iter().enumerate() {
            let size = u64::from(machine.store.size_of(set));
            // Below the set's size, so it fits the store's u32 positions.
            let position = ((binding / stride) % size) as u32;
            let element = element_at(machine, set, position);
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
        index: u64,
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
        // The TS engine counts the bindings in a double, so they never wrap; a count past u64 can't
        // be walked anyway, and hands over.
        let mut bindings = 1u64;
        for (set, slot) in &self.levels {
            let id = set(machine)?;
            let kind = machine.store.kind_of(id);
            if kind != KIND_SET && kind != KIND_TUPLE {
                return Err(Bail("an action quantified over a non-set"));
            }
            sets.push((id, bindings, machine.locals[*slot as usize]));
            bindings = bindings
                .checked_mul(u64::from(machine.store.size_of(id)))
                .ok_or(Bail(
                    "an action quantified over more bindings than the engine counts",
                ))?;
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
            if is_primed {
                return Ok(None);
            }
            self.note_variable(index)?;
            return Ok(Some(index));
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
    // set or assigns a variable from it (streamed): the set itself when TLC normalizes it, else a
    // tuple of its elements in the interpreter's order, cached like any other value.
    fn compile_ordered(
        &mut self,
        node: NodeId,
        context: &Context,
        is_streamed: bool,
    ) -> Compiling<Ordered> {
        let set = self.compile(node, context)?;
        if set.is_normalized {
            return Ok(Ordered {
                eval: set.eval,
                is_ordered: false,
            });
        }
        let Some(reference) = super::reference_of(&set) else {
            let line = self.ir.nodes.arena[node as usize].line;
            return unsupported(format!(
                "enumerating a set TLC keeps lazy ({} at line {line})",
                self.describe_set(node, context)
            ));
        };
        let ordered = Compiled {
            is_costly: true,
            ..leaf(
                eval(move |machine| {
                    let lazy = reference(machine)?;
                    let elements = if is_streamed {
                        lazy.stream(machine)?
                    } else {
                        lazy.enumerate(machine)?
                    };
                    Ok(machine.store.tuple_of(&elements))
                }),
                set.footprint,
            )
        };
        Ok(Ordered {
            eval: self.cached(ordered).eval,
            is_ordered: true,
        })
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

    /// Compiles the walk of an action, or of the initial predicate, from a state with no variable
    /// assigned.
    pub(crate) fn compile_step(
        &mut self,
        node: NodeId,
        context: &Context,
        options: WalkOptions,
    ) -> Compiling<Step> {
        // ENABLED compiles a walk of its own inside another's.
        let outer = std::mem::replace(&mut self.specialisations, 0);
        let step = self.compile_step_from(node, context, options, &Known::start());
        self.specialisations = outer;
        step
    }

    // A walk with its own continuation, from a path where `known` holds.
    fn compile_step_from(
        &mut self,
        node: NodeId,
        context: &Context,
        options: WalkOptions,
        known: &Known,
    ) -> Compiling<Step> {
        let rest = self.walk(node, context, options, known, &mut |_, _| Ok(None))?;
        Ok(rest.unwrap_or_else(|| step(|machine, on_complete| on_complete(machine))))
    }

    // Compiles the walk of an expression on a path where `known` holds, followed by `then`.
    fn walk(
        &mut self,
        node: NodeId,
        context: &Context,
        options: WalkOptions,
        known: &Known,
        then: &mut Then<'_, 'a>,
    ) -> Compiling<Rest> {
        self.depth += 1;
        let result = self
            .walk_depth()
            .and_then(|()| self.walk_kind(node, context, options, known, then));
        self.depth -= 1;
        result
    }

    fn guard_step(
        &mut self,
        node: NodeId,
        context: &Context,
        known: &Known,
        then: &mut Then<'_, 'a>,
    ) -> Compiling<Rest> {
        let evaluate = self.compile(node, context)?.eval;
        let rest = then(self, known)?;
        Ok(Some(step(move |machine, on_complete| {
            let value = evaluate(machine)?;
            if value == TRUE {
                run_rest(&rest, machine, on_complete)
            } else if value == FALSE {
                Ok(())
            } else {
                Err(Bail("a guard that isn't a boolean"))
            }
        })))
    }

    fn walk_kind(
        &mut self,
        node: NodeId,
        context: &Context,
        options: WalkOptions,
        known: &Known,
        then: &mut Then<'_, 'a>,
    ) -> Compiling<Rest> {
        let is_init = options.is_init;
        match self.node(node).1 {
            NodeKind::And(operands) => {
                self.walk_conjunction(operands, context, options, known, then)
            }
            NodeKind::Or(operands) => {
                self.walk_disjunction(operands, context, options, known, then)
            }
            NodeKind::Exists { bounds, body } => {
                let mut inner = context.clone();
                let mut levels = Vec::new();
                for bound in bounds {
                    let set = self.compile_ordered(bound.set, &inner, false)?;
                    let binder = self.bind_bound(&bound.pattern, &inner);
                    inner = binder.context;
                    levels.push((set, binder.slots, binder.tuple));
                }
                let body = self.walk(*body, &inner, options, known, then)?;
                Ok(Some(exists_step(levels, body)))
            }
            NodeKind::Forall { bounds, body } => {
                if !self.is_walked_body(*body, context)? {
                    return self.guard_step(node, context, known, then);
                }
                let mut inner = context.clone();
                let mut levels = Vec::new();
                for bound in bounds {
                    if !matches!(bound.pattern, Pattern::Name(_)) {
                        return unsupported("a tuple pattern in an action's \\A");
                    }
                    let set = self.compile_ordered(bound.set, &inner, false)?;
                    let binder = self.bind_bound(&bound.pattern, &inner);
                    inner = binder.context;
                    levels.push((set.eval, binder.slots[0]));
                }
                // Each binding's walk starts where the last left off, which the compiler doesn't
                // follow, so it knows only what was assigned before.
                let after = known.opaque();
                let walk = self.compile_step_from(*body, &inner, options, &after)?;
                let guard = is_init.then(|| deferred(self.compile(*body, &inner)));
                let forall = WalkedForall {
                    levels,
                    body: walk,
                    guard,
                    is_init,
                    width: self.ir.variables.len() as u32,
                };
                let rest = then(self, &after)?;
                Ok(Some(step(move |machine, on_complete| {
                    forall.run(machine, &mut |machine: &mut Machine<'_>| {
                        run_rest(&rest, machine, on_complete)
                    })
                })))
            }
            NodeKind::If {
                condition,
                consequent,
                alternative,
            } => {
                let condition = self.compile(*condition, context)?.eval;
                let mut shared = Shared::new(then);
                let mut then =
                    |compiler: &mut Compiler<'a>, known: &Known| shared.call(compiler, known);
                let consequent = self.walk(*consequent, context, options, known, &mut then)?;
                let alternative = self.walk(*alternative, context, options, known, &mut then)?;
                Ok(Some(step(move |machine, on_complete| {
                    let value = condition(machine)?;
                    if value == TRUE {
                        run_rest(&consequent, machine, on_complete)
                    } else if value == FALSE {
                        run_rest(&alternative, machine, on_complete)
                    } else {
                        Err(Bail("an IF condition that isn't a boolean"))
                    }
                })))
            }
            NodeKind::Case { arms, other } => {
                let mut shared = Shared::new(then);
                let mut then =
                    |compiler: &mut Compiler<'a>, known: &Known| shared.call(compiler, known);
                let mut compiled = Vec::with_capacity(arms.len());
                for &(condition, body) in arms {
                    let condition = self.compile(condition, context)?.eval;
                    compiled.push((
                        condition,
                        self.walk(body, context, options, known, &mut then)?,
                    ));
                }
                let other = match other {
                    Some(other) => Some(self.walk(*other, context, options, known, &mut then)?),
                    None => None,
                };
                Ok(Some(step(move |machine, on_complete| {
                    for (condition, body) in &compiled {
                        let value = condition(machine)?;
                        if value == TRUE {
                            return run_rest(body, machine, on_complete);
                        }
                        if value != FALSE {
                            return Err(Bail("a CASE condition that isn't a boolean"));
                        }
                    }
                    match &other {
                        Some(other) => run_rest(other, machine, on_complete),
                        None => Err(Bail("no CASE arm holds")),
                    }
                })))
            }
            NodeKind::Let {
                instances,
                definitions,
                body,
            } => {
                let inner = self.bind_let_definitions(*instances, definitions, context)?;
                self.walk(*body, &inner, options, known, then)
            }
            NodeKind::Unchanged(expression) => {
                if is_init {
                    return unsupported("UNCHANGED in the initial predicate");
                }
                self.walk_unchanged(*expression, context, options, known, then)
            }
            NodeKind::AngleAction { action, subscript } => {
                // TLC evaluates the subscript as an expression, which the engine doesn't evaluate
                // as TLC does, so a Print in it is the interpreter's.
                let subscript = *subscript;
                let unchanged = self
                    .wrap_compile(|compiler| {
                        compiler.compile_unchanged(subscript, &context.without_print())
                    })?
                    .eval;
                let mut shared = Shared::new(then);
                let mut then = |compiler: &mut Compiler<'a>, known: &Known| {
                    let rest = shared.call(compiler, known)?;
                    let unchanged = unchanged.clone();
                    Ok(Some(step(move |machine, on_complete| {
                        if unchanged(machine)? == FALSE {
                            run_rest(&rest, machine, on_complete)
                        } else {
                            Ok(())
                        }
                    })))
                };
                let mut checked = Shared::new(&mut then);
                self.walk(*action, context, options, known, &mut |compiler, known| {
                    checked.call(compiler, known)
                })
            }
            NodeKind::BoxAction { action, subscript } => {
                let mut shared = Shared::new(then);
                let mut then =
                    |compiler: &mut Compiler<'a>, known: &Known| shared.call(compiler, known);
                let action = self.walk(*action, context, options, known, &mut then)?;
                let unchanged =
                    self.walk_unchanged(*subscript, context, options, known, &mut then)?;
                Ok(Some(step(move |machine, on_complete| {
                    run_rest(&action, machine, on_complete)?;
                    run_rest(&unchanged, machine, on_complete)
                })))
            }
            NodeKind::Label { body, .. } => self.walk(*body, context, options, known, then),
            NodeKind::FunctionApplication { args, .. } => {
                let Some(lazy) = self.resolve_lazy_application(node, context)? else {
                    return self.guard_step(node, context, known, then);
                };
                if !self.is_walked_body(lazy.body, &lazy.base)? {
                    return self.guard_step(node, context, known, then);
                }
                if lazy.is_recursive {
                    return unsupported("walking a recursive function in an action");
                }
                let argument = self.compile(args[0], context)?.eval;
                let set = self.compile(lazy.set, &lazy.base)?;
                let member: Member = self.member_test(&set);
                let binder = self.bind_bound(&lazy.pattern, &lazy.base);
                let slot = binder.slots[0];
                let walk = self.walk(lazy.body, &binder.context, options, known, then)?;
                Ok(Some(step(move |machine, on_complete| {
                    let value = argument(machine)?;
                    if !member(machine, value)? {
                        return Err(Bail("applied a function outside its domain"));
                    }
                    // The argument once, as the interpreter evaluates it: a Print in it prints once.
                    machine.locals[slot as usize] = value;
                    run_rest(&walk, machine, on_complete)
                })))
            }
            NodeKind::Identifier(_) => match self.resolve_action(node, context)? {
                Some((body, inner)) => self.walk(body, &inner, options, known, then),
                None => self.guard_step(node, context, known, then),
            },
            NodeKind::Apply { name, args } => {
                let operator = self.text(name.text);
                if !name.is_local && matches!(operator, "=" | "\\in" | "\\subseteq") {
                    if let Some(variable) = self.get_assignable_index(args[0], context, is_init)? {
                        return match operator {
                            "=" => self.walk_conjunction(&[node], context, options, known, then),
                            "\\subseteq" => unsupported("x' \\subseteq S"),
                            _ => self.walk_membership(
                                variable, args[1], node, context, options, known, then,
                            ),
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
                    let mut shared = Shared::new(then);
                    let mut then =
                        |compiler: &mut Compiler<'a>, known: &Known| shared.call(compiler, known);
                    let right = self.walk(args[1], context, options, known, &mut then)?;
                    let left = then(self, known)?;
                    return Ok(Some(step(move |machine, on_complete| {
                        let value = condition(machine)?;
                        if value == FALSE {
                            run_rest(&left, machine, on_complete)
                        } else if value == TRUE {
                            run_rest(&right, machine, on_complete)
                        } else {
                            Err(Bail("the left side of => isn't a boolean"))
                        }
                    })));
                }
                if !name.is_local && operator == "/\\" {
                    return self.walk_conjunction(args, context, options, known, then);
                }
                if !name.is_local && operator == "\\/" {
                    return self.walk_disjunction(args, context, options, known, then);
                }
                match self.resolve_action(node, context)? {
                    Some((body, inner)) => self.walk(body, &inner, options, known, then),
                    None => self.guard_step(node, context, known, then),
                }
            }
            _ => self.guard_step(node, context, known, then),
        }
    }

    fn walk_disjunction(
        &mut self,
        operands: &[NodeId],
        context: &Context,
        options: WalkOptions,
        known: &Known,
        then: &mut Then<'_, 'a>,
    ) -> Compiling<Rest> {
        let mut shared = Shared::new(then);
        let mut then = |compiler: &mut Compiler<'a>, known: &Known| shared.call(compiler, known);
        let branches = operands
            .iter()
            .map(|&operand| self.walk(operand, context, options, known, &mut then))
            .collect::<Compiling<Vec<Rest>>>()?;
        if let Some(switch) = self.switch(&branches) {
            return Ok(Some(switch));
        }
        Ok(Some(step(move |machine, on_complete| {
            for branch in &branches {
                run_rest(branch, machine, on_complete)?;
            }
            Ok(())
        })))
    }

    // Notes a walk whose first step is a guard `f[k] = c` of a variable and a bound name, keeping
    // the step alive so that its address names it alone.
    fn led(&mut self, rest: Rest, leading: Option<Leading>) -> Rest {
        if let (Some(step), Some(leading)) = (&rest, leading) {
            self.leading_guards
                .insert(step_address(step), (step.clone(), leading));
        }
        rest
    }

    // A disjunction each of whose walks starts with a guard `f[k] = c` of the same variable and
    // bound name, as PlusCal's `pc[self] = "label"` does: `f[k]` is read once, where the first
    // walk would read it, and each walk is entered only where its constant equals that value, in
    // order. Each walk still tests its own guard, so it finds and bails as it would have, and the
    // reads it saves are of a variable and a bound name, which can't differ or have effects.
    fn switch(&self, branches: &[Rest]) -> Option<Step> {
        let leads = branches
            .iter()
            .map(|branch| {
                let step = branch.as_ref()?;
                self.leading_guards
                    .get(&step_address(step))
                    .map(|(_, leading)| *leading)
            })
            .collect::<Option<Vec<Leading>>>()?;
        let read = leads.first()?.read;
        if leads.len() < 2 || leads.iter().any(|leading| leading.read != read) {
            return None;
        }
        let walks: Box<[(Id, bool, Step)]> = leads
            .iter()
            .zip(branches)
            .map(|(leading, branch)| {
                let walk = branch.clone().expect("a walk");
                (leading.constant, leading.is_equal, walk)
            })
            .collect();
        Some(step(move |machine, on_complete| {
            let value = read.run(machine)?;
            for (constant, is_equal, walk) in walks.iter() {
                if predicate::equals(machine, value, *constant)? == *is_equal {
                    walk(machine, on_complete)?;
                }
            }
            Ok(())
        }))
    }

    // UNCHANGED e as a step: an assignment or test of each variable of e, or a guard.
    fn walk_unchanged(
        &mut self,
        expression: NodeId,
        context: &Context,
        options: WalkOptions,
        known: &Known,
        then: &mut Then<'_, 'a>,
    ) -> Compiling<Rest> {
        if let Some(indices) = self.get_unchanged_indices(expression, context, 0)? {
            let items: Rc<[Item]> = Rc::new([Item {
                node: expression,
                shape: Shape::Unchanged(indices.into()),
            }]);
            return self.conjunction(&items, context, options, 0, 0, known.clone(), then);
        }
        let evaluate = self
            .wrap_compile(|compiler| {
                compiler.compile_unchanged(expression, &context.without_print())
            })?
            .eval;
        let rest = then(self, known)?;
        Ok(Some(step(move |machine, on_complete| {
            let value = evaluate(machine)?;
            if value == TRUE {
                run_rest(&rest, machine, on_complete)
            } else if value == FALSE {
                Ok(())
            } else {
                Err(Bail("a guard that isn't a boolean"))
            }
        })))
    }

    fn shape_of(
        &mut self,
        operand: NodeId,
        context: &Context,
        options: WalkOptions,
    ) -> Compiling<Shape> {
        if let Some(("=", args, false)) = self.operator_text(operand)
            && let Some(variable) = self.get_assignable_index(args[0], context, options.is_init)?
        {
            return Ok(Shape::Assign(variable, args[1]));
        }
        if !options.is_init
            && let NodeKind::Unchanged(expression) = self.node(operand).1
            && let Some(indices) = self.get_unchanged_indices(*expression, context, 0)?
        {
            return Ok(Shape::Unchanged(indices.into()));
        }
        if self.is_guard(operand, context, options.is_init)? {
            return Ok(Shape::Guard);
        }
        Ok(Shape::Branch)
    }

    fn walk_conjunction(
        &mut self,
        operands: &[NodeId],
        context: &Context,
        options: WalkOptions,
        known: &Known,
        then: &mut Then<'_, 'a>,
    ) -> Compiling<Rest> {
        let items = operands
            .iter()
            .map(|&operand| {
                Ok(Item {
                    node: operand,
                    shape: self.shape_of(operand, context, options)?,
                })
            })
            .collect::<Compiling<Rc<[Item]>>>()?;
        self.conjunction(&items, context, options, 0, 0, known.clone(), then)
    }

    // The conjuncts of a conjunction from one on (and, within an UNCHANGED, from one of its
    // variables on), as a segment of what the path knows, then the rest.
    #[allow(clippy::too_many_arguments)]
    fn conjunction(
        &mut self,
        items: &Rc<[Item]>,
        context: &Context,
        options: WalkOptions,
        start: usize,
        start_variable: usize,
        mut known: Known,
        then: &mut Then<'_, 'a>,
    ) -> Compiling<Rest> {
        let is_init = options.is_init;
        let width = self.ir.variables.len() as u32;
        let mut ops = Vec::new();
        let mut index = start;
        let mut first_variable = start_variable;
        let mut leading = None;
        while index < items.len() {
            if index > 0 && first_variable == 0 && options.is_shortcut {
                match known.shortcut(width) {
                    Shortcut::Never => {}
                    Shortcut::Always => {
                        ops.extend(self.shortcut_guards(items, context, options, index)?);
                        let rest = then(self, &known)?;
                        return Ok(self.led(segment(ops, rest, is_init), leading));
                    }
                    Shortcut::Maybe => {
                        let guards = self.shortcut_guards(items, context, options, index)?;
                        let mut shared = Shared::new(then);
                        let guarded = shared.call(self, &known)?;
                        let guarded = segment(guards, guarded, is_init);
                        let walked = self.conjunct(
                            items,
                            context,
                            options,
                            index,
                            0,
                            known,
                            &mut |compiler, known| shared.call(compiler, known),
                        )?;
                        let shortcut = step(move |machine, on_complete| {
                            if machine.assigned == width {
                                run_rest(&guarded, machine, on_complete)
                            } else {
                                run_rest(&walked, machine, on_complete)
                            }
                        });
                        return Ok(self.led(segment(ops, Some(shortcut), is_init), leading));
                    }
                }
            }
            let item = &items[index];
            match &item.shape {
                Shape::Guard => {
                    let compiled = self.compile(item.node, context)?;
                    if index == 0 && ops.is_empty() {
                        leading = Leading::of(&compiled);
                    }
                    ops.push(guard(compiled));
                }
                Shape::Assign(variable, value) => {
                    let variable = *variable;
                    let value = Source::Value(self.compile(*value, context)?.eval);
                    match known.get(variable) {
                        UNSET => {
                            ops.push(Op::Assign(variable, value));
                            known = known.with(variable, SET);
                        }
                        SET => ops.push(Op::Test(variable, value)),
                        _ => {
                            let after = known.with(variable, SET);
                            let rest = self.conjunction(
                                items,
                                context,
                                options,
                                index + 1,
                                0,
                                after,
                                then,
                            )?;
                            let either = either_step(variable, value, rest, is_init);
                            return Ok(self.led(segment(ops, Some(either), is_init), leading));
                        }
                    }
                }
                Shape::Unchanged(variables) => {
                    for (position, &variable) in variables.iter().enumerate().skip(first_variable) {
                        match known.get(variable) {
                            UNSET => {
                                ops.push(Op::Assign(variable, Source::Current));
                                known = known.with(variable, SET);
                            }
                            SET => ops.push(Op::Test(variable, Source::Current)),
                            _ => {
                                let after = known.with(variable, SET);
                                let rest = self.conjunction(
                                    items,
                                    context,
                                    options,
                                    index,
                                    position + 1,
                                    after,
                                    then,
                                )?;
                                let either = either_step(variable, Source::Current, rest, is_init);
                                return Ok(self.led(segment(ops, Some(either), is_init), leading));
                            }
                        }
                    }
                }
                Shape::Branch => {
                    let rest = self.conjunct(items, context, options, index, 0, known, then)?;
                    return Ok(self.led(segment(ops, rest, is_init), leading));
                }
            }
            first_variable = 0;
            index += 1;
        }
        let rest = then(self, &known)?;
        Ok(self.led(segment(ops, rest, is_init), leading))
    }

    // The walk of one conjunct that branches, or of the conjunction from it on, its rest the
    // conjuncts after it.
    #[allow(clippy::too_many_arguments)]
    fn conjunct(
        &mut self,
        items: &Rc<[Item]>,
        context: &Context,
        options: WalkOptions,
        index: usize,
        first_variable: usize,
        known: Known,
        then: &mut Then<'_, 'a>,
    ) -> Compiling<Rest> {
        if !matches!(items[index].shape, Shape::Branch) {
            return self.conjunction_from(
                items,
                context,
                options,
                index,
                first_variable,
                known,
                then,
            );
        }
        let mut rest = |compiler: &mut Compiler<'a>, known: &Known| {
            compiler.conjunction(items, context, options, index + 1, 0, known.clone(), then)
        };
        let mut shared = Shared::new(&mut rest);
        self.walk(
            items[index].node,
            context,
            options,
            &known,
            &mut |compiler, known| shared.call(compiler, known),
        )
    }

    // The conjunction from a conjunct on, past the shortcut's check, which its caller made.
    #[allow(clippy::too_many_arguments)]
    fn conjunction_from(
        &mut self,
        items: &Rc<[Item]>,
        context: &Context,
        options: WalkOptions,
        index: usize,
        first_variable: usize,
        known: Known,
        then: &mut Then<'_, 'a>,
    ) -> Compiling<Rest> {
        let unchecked = WalkOptions {
            is_shortcut: false,
            ..options
        };
        // The conjunct at `index` without the check, and the ones after it with it.
        let mut rest = |compiler: &mut Compiler<'a>, known: &Known| {
            compiler.conjunction(items, context, options, index + 1, 0, known.clone(), then)
        };
        let head: Rc<[Item]> = Rc::new([items[index].clone()]);
        self.conjunction(
            &head,
            context,
            unchecked,
            0,
            first_variable,
            known,
            &mut rest,
        )
    }

    // The conjuncts from one on, as the guards TLC's shortcut evaluates them as.
    fn shortcut_guards(
        &mut self,
        items: &Rc<[Item]>,
        context: &Context,
        options: WalkOptions,
        index: usize,
    ) -> Compiling<Vec<Op>> {
        let mut guards = Vec::with_capacity(items.len() - index + 1);
        if !options.is_init
            && items[index..]
                .iter()
                .any(|item| matches!(item.shape, Shape::Branch))
        {
            guards.push(Op::PastWalk);
        }
        for item in &items[index..] {
            // A conjunct that fails to compile as the walk would compile it fails the walk's
            // compile, even past the shortcut, as each conjunction compiles all of its conjuncts.
            match &item.shape {
                Shape::Assign(_, value) => {
                    self.compile(*value, context)?;
                }
                Shape::Branch => {
                    self.compile_step(item.node, context, options)?;
                }
                Shape::Guard | Shape::Unchanged(_) => {}
            }
            guards.push(match &item.shape {
                Shape::Guard => guard(self.compile(item.node, context)?),
                _ => Op::Check(
                    deferred_eval(deferred(self.compile(item.node, context))),
                    "a conjunct that isn't a boolean",
                ),
            });
        }
        Ok(guards)
    }

    #[allow(clippy::too_many_arguments)]
    fn walk_membership(
        &mut self,
        variable: u32,
        set: NodeId,
        guard: NodeId,
        context: &Context,
        options: WalkOptions,
        known: &Known,
        then: &mut Then<'_, 'a>,
    ) -> Compiling<Rest> {
        let is_init = options.is_init;
        let index = variable as usize;
        let state = known.get(variable);
        // The guard only where the variable is assigned already, as the TypeScript engine compiles
        // it only where it may be.
        if state == SET {
            let guard = deferred(self.compile(guard, context));
            let rest = then(self, known)?;
            return Ok(Some(step(
                move |machine, on_complete| match run_deferred(machine, &guard)? {
                    TRUE => run_rest(&rest, machine, on_complete),
                    FALSE => Ok(()),
                    _ => Err(Bail("a guard that isn't a boolean")),
                },
            )));
        }
        let set = self.compile_ordered(set, context, true)?;
        let guard = (state == EITHER).then(|| deferred(self.compile(guard, context)));
        let mut shared = Shared::new(then);
        let assigned = shared.call(self, &known.with(variable, SET))?;
        let guarded = match guard {
            Some(_) => shared.call(self, known)?,
            None => None,
        };
        Ok(Some(step(move |machine, on_complete| {
            if let Some(guard) = &guard
                && target(machine, is_init)[index] != UNASSIGNED
            {
                return match run_deferred(machine, guard)? {
                    TRUE => run_rest(&guarded, machine, on_complete),
                    FALSE => Ok(()),
                    _ => Err(Bail("a guard that isn't a boolean")),
                };
            }
            let id = (set.eval)(machine)?;
            let size = set.size(machine, id)?;
            machine.assigned += 1;
            for position in 0..size {
                let element = machine.store.element_at(id, position);
                target(machine, is_init)[index] = element;
                run_rest(&assigned, machine, on_complete)?;
            }
            target(machine, is_init)[index] = UNASSIGNED;
            machine.assigned -= 1;
            Ok(())
        })))
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
        self.enabled_depth += 1;
        let compiled = self
            .compile_step(
                action,
                context,
                WalkOptions {
                    is_init: false,
                    is_shortcut: false,
                },
            )
            .and_then(|walk| Ok((walk, self.get_enabled_footprint(action, context)?)));
        self.enabled_depth -= 1;
        let (walk, footprint) = compiled?;
        if footprint
            .slots
            .iter()
            .any(|slot| SEARCH_SLOTS.contains(slot))
        {
            return unsupported("ENABLED of an action that reads TLCGet");
        }
        let width = self.variable_extent;
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
                    let result = walk(machine, &mut |_: &mut Machine<'_>| Err(Bail(FOUND)));
                    let inner = std::mem::replace(&mut machine.next, outer);
                    machine.spare_states.push(inner);
                    machine.assigned = assigned;
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

// A bound of `\E`: its set, and the slots its name or tuple of names binds (`assign_bound`).
type Level = (Ordered, Vec<u32>, bool);

fn exists_step(levels: Vec<Level>, body: Rest) -> Step {
    if let [(set, slots, tuple)] = &levels[..] {
        let (set, slots, tuple) = (set.clone(), slots.clone(), *tuple);
        return step(move |machine, on_complete| {
            let id = (set.eval)(machine)?;
            let size = set.size(machine, id)?;
            for position in 0..size {
                let element = machine.store.element_at(id, position);
                assign_bound(machine, &slots, tuple, element)?;
                run_rest(&body, machine, on_complete)?;
            }
            Ok(())
        });
    }
    // TLC's ContextEnumerator varies the first bound fastest: the last bound is the outer loop.
    step(move |machine, on_complete| {
        let mut sets = Vec::with_capacity(levels.len());
        let mut is_empty = false;
        for (set, ..) in &levels {
            let id = (set.eval)(machine)?;
            if set.size(machine, id)? == 0 {
                is_empty = true;
            }
            sets.push(id);
        }
        if is_empty {
            return Ok(());
        }
        let mut positions = vec![0u32; levels.len()];
        loop {
            for (level, (_, slots, tuple)) in levels.iter().enumerate() {
                let element = machine.store.element_at(sets[level], positions[level]);
                assign_bound(machine, slots, *tuple, element)?;
            }
            run_rest(&body, machine, on_complete)?;
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
