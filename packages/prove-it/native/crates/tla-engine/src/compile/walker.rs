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
use std::sync::{Arc, OnceLock};

use tla_ir::{Bound, Index, NodeId, NodeKind, Param, Pattern, Resolution, ScopeBinding};
use tla_values::store::{FALSE, KIND_SET, KIND_TUPLE, Outcome, TRUE};
use tla_values::{Bail, Id};

use super::nodes::assign_bound;
use super::predicate::{Leaf, Predicate, Test};
use super::{
    Argument, Binding, CompileError, Compiled, Compiler, Compiling, Context, Definition,
    DefinitionForm, Operator, OperatorBody, SEARCH_SLOTS, Scope, bind, decline, eval, leaf, lookup,
    unsupported,
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
pub(super) struct Ordered {
    pub(super) eval: Eval,
    is_ordered: bool,
}

impl Ordered {
    pub(super) fn size(&self, machine: &Machine<'_>, id: Id) -> Outcome<u32> {
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

// A walk's first step, a guard `f[k] = c` of a variable and a bound name.
#[derive(Clone, Copy)]
pub(crate) struct Leading {
    variable: u32,
    slot: u32,
    constant: Id,
}

impl Leading {
    fn of(compiled: &Compiled) -> Option<Leading> {
        match &**compiled.predicate.as_ref()? {
            Predicate::Equal {
                left: Leaf::ApplyVar { variable, slot, .. },
                right: Leaf::Constant(constant),
                is_equal: true,
            } => Some(Leading {
                variable: *variable,
                slot: *slot,
                constant: *constant,
            }),
            _ => None,
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
/// The walk of a recursive function's body, compiled once for what the walk knows where an action
/// applies the function, and the slots from its argument's to the last the walk binds.
pub(crate) struct WalkedFunction {
    body: NodeId,
    // The scope the function's body closes over, kept so its address isn't reused.
    scope: Option<Rc<Scope>>,
    is_primed: bool,
    can_print: bool,
    is_init: bool,
    is_shortcut: bool,
    known: Known,
    slot: u32,
    walk: Arc<OnceLock<(Rest, u32)>>,
}

/// The walk of a RECURSIVE operator's body, compiled once for what the walk knows where an action
/// applies the operator and the variables its arguments name, and the slots from its first
/// parameter's to the last the walk binds.
pub(crate) struct WalkedOperator {
    key: usize,
    // The operator a LET defines, kept so its address isn't reused.
    operator: Option<Rc<Operator>>,
    variables: Vec<Option<(u32, bool)>>,
    is_primed: bool,
    can_print: bool,
    is_init: bool,
    is_shortcut: bool,
    known: Known,
    slots: Vec<Option<u32>>,
    start: u32,
    walk: Arc<OnceLock<(Rest, u32)>>,
}

struct RecursiveApplication {
    key: usize,
    operator: Option<Rc<Operator>>,
    params: Vec<Param>,
    body: NodeId,
    base: Context,
}

struct LazyApplication<'a> {
    bounds: &'a [Bound],
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
        self.resolve_operator(node, context, false)
    }

    // The body of an operator an expression applies, with its arguments bound, where the walk
    // goes into it: a recursive one only where `is_recursive_taken`.
    fn resolve_operator(
        &mut self,
        node: NodeId,
        context: &Context,
        is_recursive_taken: bool,
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
                // A definition TLC evaluates at startup keeps its value, so it isn't walked.
                Ok(match &definition.form {
                    DefinitionForm::Operator(params)
                        if params.is_empty()
                            && !self.ir.model.startup.definitions.contains(&index) =>
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
                    if operator.is_recursive && !is_recursive_taken {
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
                if definition.flags & Definition::RECURSIVE != 0 && !is_recursive_taken {
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
    ) -> Compiling<Option<LazyApplication<'a>>> {
        let NodeKind::FunctionApplication { function, .. } = self.node(node).1 else {
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
            // A function a definition gives, which TLC keeps lazy unless it evaluated it at
            // startup.
            NodeKind::Identifier(name) => {
                let Resolution::Definition(index) = name.resolution else {
                    return Ok(None);
                };
                let node = self.ir.definitions[index as usize];
                if self.startup_definitions.contains_key(&node) {
                    return Ok(None);
                }
                let definition = self.definition(node);
                let DefinitionForm::Function(bounds) = &definition.form else {
                    return Ok(None);
                };
                let is_recursive =
                    definition.flags & (Definition::RECURSIVE | Definition::SELF_REFERENTIAL) != 0;
                let scope = is_recursive.then(|| self.global_function_scope(node));
                (
                    bounds,
                    definition.body,
                    context.global(context.can_print).with_scope(scope),
                    is_recursive,
                )
            }
            _ => return Ok(None),
        };
        Ok(Some(LazyApplication {
            bounds,
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
            // TLC's getPrimedVar looks through a LET and a label to the primed variable.
            NodeKind::Let {
                definitions, body, ..
            } => {
                let inner = self.bind_let_definitions(definitions, *body, context)?;
                return self.get_assignable(*body, &inner, is_primed, depth + 1);
            }
            NodeKind::Label { body, .. } => {
                return self.get_assignable(*body, context, is_primed, depth + 1);
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
                Ok(self.resolve_action(node, context)?.is_none()
                    && !self.is_recursive_walk(node, context, is_init)?)
            }
            _ => Ok(true),
        }
    }

    // The expressions directly inside one, as `collectChildren` finds them.
    pub(super) fn children(&self, node: NodeId) -> Vec<NodeId> {
        self.node(node).1.children()
    }

    // Whether an expression has a disjunction or an existential, for each of which TLC generates
    // a successor when it walks the expression; or, with `is_assigning`, whether walking it may
    // assign a variable.
    fn has_walk(
        &mut self,
        node: NodeId,
        context: &Context,
        is_assigning: bool,
        is_init: bool,
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
        // The initial predicate assigns a variable unprimed, by x = e or x \in S.
        if is_assigning
            && is_init
            && let NodeKind::Apply { name, args } = kind
            && !name.is_local
            && matches!(self.text(name.text), "=" | "\\in")
            && self.get_assignable_index(args[0], context, true)?.is_some()
        {
            return Ok(true);
        }
        if matches!(kind, NodeKind::Apply { .. } | NodeKind::Identifier(_))
            && let Some((body, inner)) = self.resolve_action(node, context)?
            && self.has_walk(body, &inner, is_assigning, is_init, depth + 1)?
        {
            return Ok(true);
        }
        // TLC computes the initial states building a function at once, but a recursive one, so it
        // walks only a recursive function's body there.
        if matches!(kind, NodeKind::FunctionApplication { .. })
            && let Some(lazy) = self.resolve_lazy_application(node, context)?
            && (!is_init || lazy.is_recursive)
            && self.has_walk(lazy.body, &lazy.base, is_assigning, is_init, depth + 1)?
        {
            return Ok(true);
        }
        for child in self.children(node) {
            if self.has_walk(child, context, is_assigning, is_init, depth + 1)? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    // TLC walks the body of a function it keeps lazy where an action applies it (getNextStates),
    // the body of a recursive function too, which may apply the function again. The body's walk
    // is compiled once for what the walk knows, and runs at each application with a continuation
    // that goes on with the rest of the walk where the application is, the caller's slots back.
    fn walk_recursive_application(
        &mut self,
        lazy: &LazyApplication<'a>,
        args: &[NodeId],
        context: &Context,
        options: WalkOptions,
        known: &Known,
        then: &mut Then<'_, 'a>,
    ) -> Compiling<Rest> {
        let ([bound], [argument]) = (lazy.bounds, args) else {
            return unsupported("walking a recursive function of several arguments");
        };
        if !matches!(bound.pattern, Pattern::Name(_)) {
            return unsupported("walking a recursive function over a tuple pattern");
        }
        let argument = self.compile(*argument, context)?.eval;
        let set = self.compile(bound.set, &lazy.base)?;
        let member = self.member_test(&set);
        let is_walked = |walked: &&WalkedFunction| {
            walked.body == lazy.body
                && match (&walked.scope, &lazy.base.scope) {
                    (Some(walked), Some(scope)) => Rc::ptr_eq(walked, scope),
                    (walked, scope) => walked.is_none() && scope.is_none(),
                }
                && walked.is_primed == lazy.base.is_primed
                && walked.can_print == lazy.base.can_print
                && walked.is_init == options.is_init
                && walked.is_shortcut == options.is_shortcut
                && walked.known == *known
        };
        let found = self
            .walked_functions
            .iter()
            .find(is_walked)
            .map(|walked| (walked.slot, Arc::clone(&walked.walk)));
        let (slot, walk) = match found {
            Some(found) => found,
            None => {
                let binder = self.bind_bound(&bound.pattern, &lazy.base);
                let slot = binder.slots[0];
                let walk = Arc::new(OnceLock::new());
                self.walked_functions.push(WalkedFunction {
                    body: lazy.body,
                    scope: lazy.base.scope.clone(),
                    is_primed: lazy.base.is_primed,
                    can_print: lazy.base.can_print,
                    is_init: options.is_init,
                    is_shortcut: options.is_shortcut,
                    known: known.clone(),
                    slot,
                    walk: Arc::clone(&walk),
                });
                let body = self.walk(
                    lazy.body,
                    &binder.context,
                    options,
                    known,
                    &mut |_, after: &Known| {
                        if after == known {
                            Ok(None)
                        } else {
                            unsupported("walking a recursive function that assigns")
                        }
                    },
                );
                let body = match body {
                    Ok(body) => body,
                    Err(error) => {
                        self.walked_functions
                            .retain(|walked| !Arc::ptr_eq(&walked.walk, &walk));
                        return Err(error);
                    }
                };
                let _ = walk.set((body, self.program.slot_count as u32));
                (slot, walk)
            }
        };
        let rest = then(self, known)?;
        Ok(Some(step(move |machine, on_complete| {
            let value = argument(machine)?;
            if !member(machine, value)? {
                return Err(Bail("applied a function outside its domain"));
            }
            let (body, end) = walk
                .get()
                .expect("a recursive function's walk run before it compiled");
            let slots = slot as usize..*end as usize;
            let caller = machine.locals[slots.clone()].to_vec();
            machine.locals[slot as usize] = value;
            let result = machine.nested(|machine| {
                run_rest(body, machine, &mut |machine| {
                    let callee = machine.locals[slots.clone()].to_vec();
                    machine.locals[slots.clone()].copy_from_slice(&caller);
                    let result = run_rest(&rest, machine, on_complete);
                    machine.locals[slots.clone()].copy_from_slice(&callee);
                    result
                })
            });
            machine.locals[slots].copy_from_slice(&caller);
            result
        })))
    }

    // A RECURSIVE operator an expression applies: its parameters, its body and the context the
    // body sees before they are bound.
    fn resolve_recursive_operator(
        &mut self,
        node: NodeId,
        context: &Context,
    ) -> Option<RecursiveApplication> {
        let NodeKind::Apply { name, .. } = self.node(node).1 else {
            return None;
        };
        if name.is_local
            && let Some(found) = lookup(&context.scope, name.text)
        {
            let Binding::Operator(operator) = &found.binding else {
                return None;
            };
            let OperatorBody::Node(body) = operator.body else {
                return None;
            };
            return operator.is_recursive.then(|| RecursiveApplication {
                key: Rc::as_ptr(operator) as usize,
                operator: Some(Rc::clone(operator)),
                params: operator.params.clone(),
                body,
                base: super::operator_context(operator)
                    .primed(context.is_primed || operator.context.is_primed),
            });
        }
        let Resolution::Definition(index) = name.resolution else {
            return None;
        };
        let definition_node = self.ir.definitions[index as usize];
        let definition = self.definition(definition_node);
        let DefinitionForm::Operator(params) = &definition.form else {
            return None;
        };
        (definition.flags & Definition::RECURSIVE != 0).then(|| RecursiveApplication {
            key: definition_node as usize,
            operator: None,
            params: params.clone(),
            body: definition.body,
            base: context.global(context.can_print),
        })
    }

    // Whether an expression applies a RECURSIVE operator whose body TLC walks.
    fn is_recursive_walk(
        &mut self,
        node: NodeId,
        context: &Context,
        is_init: bool,
    ) -> Compiling<bool> {
        match self.resolve_operator(node, context, true)? {
            Some((body, inner)) => self.is_walked_body(body, &inner, is_init),
            None => Ok(false),
        }
    }

    // The variable an argument names, and whether primed: what an operator's body may assign
    // through the parameter.
    fn get_named_variable(
        &mut self,
        node: NodeId,
        context: &Context,
        depth: u32,
    ) -> Compiling<Option<(u32, bool)>> {
        if depth > 50 || context.is_primed {
            return Ok(None);
        }
        match self.node(node).1 {
            NodeKind::Prime(inner) => {
                Ok(match self.get_named_variable(*inner, context, depth + 1)? {
                    Some((variable, false)) => Some((variable, true)),
                    _ => None,
                })
            }
            NodeKind::Identifier(name) => {
                if name.is_local
                    && let Some(found) = lookup(&context.scope, name.text)
                {
                    return match &found.binding {
                        Binding::Argument(argument) => self.get_named_variable(
                            argument.expression,
                            &super::argument_context(argument),
                            depth + 1,
                        ),
                        _ => Ok(None),
                    };
                }
                let Resolution::Variable(index) = name.resolution else {
                    return Ok(None);
                };
                self.note_variable(index)?;
                Ok(Some((index, false)))
            }
            _ => Ok(None),
        }
    }

    // TLC walks a RECURSIVE operator's body where the initial predicate or an action applies it,
    // as any operator's, which a walk compiled path by path can't unroll. The body's walk is
    // compiled once for what the walk knows and the variables the arguments name, which decide
    // what the body assigns, and each application runs it a level deeper with the other
    // arguments' values in the parameters' slots. What the body assigns the compiler doesn't
    // follow, so the rest of the walk knows only what was assigned before.
    fn walk_recursive_operator(
        &mut self,
        recursive: &RecursiveApplication,
        args: &[NodeId],
        context: &Context,
        options: WalkOptions,
        known: &Known,
        then: &mut Then<'_, 'a>,
    ) -> Compiling<Rest> {
        if recursive.params.len() != args.len() {
            return unsupported("an operator applied to the wrong number of arguments");
        }
        if recursive.params.iter().any(|param| param.arity > 0) {
            return unsupported("walking a recursive higher-order operator");
        }
        let argument_context = context.without_print();
        let mut variables = Vec::with_capacity(args.len());
        let mut values = Vec::new();
        for &argument in args {
            let named = self.get_named_variable(argument, context, 0)?;
            if named.is_none() {
                if self
                    .get_assignable_index(argument, context, options.is_init)?
                    .is_some()
                    || self.get_unchanged_indices(argument, context, 0)?.is_some()
                {
                    return unsupported(
                        "walking a recursive operator whose argument names variables indirectly",
                    );
                }
                values.push(self.compile(argument, &argument_context)?.eval);
            }
            variables.push(named);
        }
        let is_walked = |walked: &&WalkedOperator, known: &Known| {
            walked.key == recursive.key
                && match (&walked.operator, &recursive.operator) {
                    (Some(walked), Some(operator)) => Rc::ptr_eq(walked, operator),
                    (walked, operator) => walked.is_none() && operator.is_none(),
                }
                && walked.variables == variables
                && walked.is_primed == recursive.base.is_primed
                && walked.can_print == recursive.base.can_print
                && walked.is_init == options.is_init
                && walked.is_shortcut == options.is_shortcut
                && walked.known == *known
        };
        // A body that assigns applies itself knowing more each level down, so past a few of
        // what a walk may know the body compiles for nothing known.
        let body_known = if self
            .walked_operators
            .iter()
            .filter(|walked| walked.key == recursive.key)
            .count()
            >= SHARED_PATHS
            && !self
                .walked_operators
                .iter()
                .any(|walked| is_walked(&walked, known))
        {
            Known::unknown()
        } else {
            known.clone()
        };
        let found = self
            .walked_operators
            .iter()
            .find(|walked| is_walked(walked, &body_known))
            .map(|walked| (walked.slots.clone(), walked.start, Arc::clone(&walked.walk)));
        let (slots, start, walk) = match found {
            Some(found) => found,
            None => {
                let start = self.program.slot_count as u32;
                let mut scope = recursive.base.scope.clone();
                let mut slots = Vec::with_capacity(args.len());
                for ((param, &argument), named) in recursive.params.iter().zip(args).zip(&variables)
                {
                    let binding = match named {
                        Some(_) => {
                            slots.push(None);
                            Binding::Argument(Rc::new(Argument {
                                expression: argument,
                                context: argument_context.clone(),
                                compiled: RefCell::new([None, None]),
                                own_scope: RefCell::new(std::rc::Weak::new()),
                            }))
                        }
                        None => {
                            let slot = self.allocate_slot();
                            slots.push(Some(slot));
                            Binding::Slot(slot)
                        }
                    };
                    scope = bind(&scope, param.name, binding);
                }
                let walk = Arc::new(OnceLock::new());
                self.walked_operators.push(WalkedOperator {
                    key: recursive.key,
                    operator: recursive.operator.clone(),
                    variables,
                    is_primed: recursive.base.is_primed,
                    can_print: recursive.base.can_print,
                    is_init: options.is_init,
                    is_shortcut: options.is_shortcut,
                    known: body_known.clone(),
                    slots: slots.clone(),
                    start,
                    walk: Arc::clone(&walk),
                });
                let body = self.walk(
                    recursive.body,
                    &recursive.base.with_scope(scope),
                    options,
                    &body_known,
                    &mut |_, _| Ok(None),
                );
                let body = match body {
                    Ok(body) => body,
                    Err(error) => {
                        self.walked_operators
                            .retain(|walked| !Arc::ptr_eq(&walked.walk, &walk));
                        return Err(error);
                    }
                };
                let _ = walk.set((body, self.program.slot_count as u32));
                (slots, start, walk)
            }
        };
        let slots: Vec<u32> = slots.into_iter().flatten().collect();
        let rest = then(self, &known.opaque())?;
        Ok(Some(step(move |machine, on_complete| {
            let at = machine.stack.len();
            for value in &values {
                match value(machine) {
                    Ok(value) => machine.stack.push(value),
                    Err(bail) => {
                        machine.stack.truncate(at);
                        return Err(bail);
                    }
                }
            }
            let (body, end) = walk
                .get()
                .expect("a recursive operator's walk run before it compiled");
            let frame = start as usize..*end as usize;
            let caller = machine.locals[frame.clone()].to_vec();
            for (offset, &slot) in slots.iter().enumerate() {
                machine.locals[slot as usize] = machine.stack[at + offset];
            }
            machine.stack.truncate(at);
            let result = machine.nested(|machine| {
                run_rest(body, machine, &mut |machine| {
                    let callee = machine.locals[frame.clone()].to_vec();
                    machine.locals[frame.clone()].copy_from_slice(&caller);
                    let result = run_rest(&rest, machine, on_complete);
                    machine.locals[frame.clone()].copy_from_slice(&callee);
                    result
                })
            });
            machine.locals[frame].copy_from_slice(&caller);
            result
        })))
    }

    fn is_walked_body(
        &mut self,
        node: NodeId,
        context: &Context,
        is_init: bool,
    ) -> Compiling<bool> {
        Ok(self.has_walk(node, context, true, is_init, 0)?
            || self.has_walk(node, context, false, is_init, 0)?)
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
        self.order(set, node, context, is_streamed)
    }

    // A compiled set in the order TLC enumerates it, `node` naming it where TLC keeps it lazy.
    pub(super) fn order(
        &mut self,
        set: Compiled,
        node: NodeId,
        context: &Context,
        is_streamed: bool,
    ) -> Compiling<Ordered> {
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
                if !self.is_walked_body(*body, context, is_init)? {
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
                definitions, body, ..
            } => {
                let inner = self.bind_let_definitions(definitions, *body, context)?;
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
                // TLC computes the initial states building a function at once
                // (`EvalControl.Init`), but a recursive one, and applies its value.
                if is_init && !lazy.is_recursive {
                    return self.guard_step(node, context, known, then);
                }
                if !self.is_walked_body(lazy.body, &lazy.base, is_init)? {
                    return self.guard_step(node, context, known, then);
                }
                if lazy.is_recursive {
                    return self
                        .walk_recursive_application(&lazy, args, context, options, known, then);
                }
                // TLC binds each name to its argument once every argument is in its bound's
                // set (`getFcnContext`).
                if args.len() != lazy.bounds.len()
                    || lazy
                        .bounds
                        .iter()
                        .any(|bound| !matches!(bound.pattern, Pattern::Name(_)))
                {
                    return unsupported("walking a lazy function over a tuple");
                }
                let mut inner = lazy.base.clone();
                let mut parameters = Vec::with_capacity(args.len());
                for (bound, &argument) in lazy.bounds.iter().zip(args) {
                    let argument = self.compile(argument, context)?.eval;
                    let set = self.compile(bound.set, &lazy.base)?;
                    let member: Member = self.member_test(&set);
                    let binder = self.bind_bound(&bound.pattern, &inner);
                    inner = binder.context;
                    parameters.push((argument, member, binder.slots[0]));
                }
                let walk = self.walk(lazy.body, &inner, options, known, then)?;
                Ok(Some(step(move |machine, on_complete| {
                    // Each argument once, as the interpreter evaluates it: a Print in it prints
                    // once.
                    let at = machine.stack.len();
                    for (argument, ..) in &parameters {
                        match argument(machine) {
                            Ok(value) => machine.stack.push(value),
                            Err(bail) => {
                                machine.stack.truncate(at);
                                return Err(bail);
                            }
                        }
                    }
                    let values = machine.stack.split_off(at);
                    for ((_, member, _), &value) in parameters.iter().zip(&values) {
                        if !member(machine, value)? {
                            return Err(Bail("applied a function outside its domain"));
                        }
                    }
                    for ((.., slot), value) in parameters.iter().zip(values) {
                        machine.locals[*slot as usize] = value;
                    }
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
                            // TLC assigns x' each subset of S, as x' \in SUBSET S.
                            _ => self.walk_membership(
                                variable,
                                (args[1], operator == "\\subseteq"),
                                node,
                                context,
                                options,
                                known,
                                then,
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
                if let Some((body, inner)) = self.resolve_action(node, context)? {
                    return self.walk(body, &inner, options, known, then);
                }
                if let Some(recursive) = self.resolve_recursive_operator(node, context)
                    && self.is_recursive_walk(node, context, is_init)?
                {
                    return self
                        .walk_recursive_operator(&recursive, args, context, options, known, then);
                }
                self.guard_step(node, context, known, then)
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
        let (variable, slot) = (leads.first()?.variable, leads[0].slot);
        if leads.len() < 2
            || leads
                .iter()
                .any(|leading| (leading.variable, leading.slot) != (variable, slot))
        {
            return None;
        }
        let walks: Box<[(Id, Step)]> = leads
            .iter()
            .zip(branches)
            .map(|(leading, branch)| (leading.constant, branch.clone().expect("a walk")))
            .collect();
        Some(step(move |machine, on_complete| {
            let function = machine.read_current(variable)?;
            let value = machine
                .store
                .apply(function, machine.locals[slot as usize])?;
            for (constant, walk) in walks.iter() {
                if machine.store.equals(value, *constant)? {
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
        // TLC goes through a tuple element by element (processUnchanged), assigning a variable
        // and comparing anything else's values in the two states, and through an operator's
        // argument, as the interpreter does.
        match self.node(expression).1 {
            NodeKind::Tuple(elements) => {
                return self.walk_unchanged_elements(elements, context, options, known, then);
            }
            NodeKind::Identifier(name) if name.is_local => {
                if let Some((body, inner)) = self.resolve_action(expression, context)? {
                    return self.walk_unchanged(body, &inner, options, known, then);
                }
            }
            _ => {}
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

    fn walk_unchanged_elements(
        &mut self,
        elements: &[NodeId],
        context: &Context,
        options: WalkOptions,
        known: &Known,
        then: &mut Then<'_, 'a>,
    ) -> Compiling<Rest> {
        let [first, rest @ ..] = elements else {
            return then(self, known);
        };
        self.walk_unchanged(*first, context, options, known, &mut |compiler, known| {
            compiler.walk_unchanged_elements(rest, context, options, known, then)
        })
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
    // `x \in S`, or, where `is_power_set`, `x \subseteq S`, which assigns x each subset of S.
    fn walk_membership(
        &mut self,
        variable: u32,
        (set, is_power_set): (NodeId, bool),
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
        let set = if is_power_set {
            let base = self.compile(set, context)?;
            let subsets = self.compile_subset(&base);
            self.order(subsets, set, context, true)?
        } else {
            self.compile_ordered(set, context, true)?
        };
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
        if context.is_primed {
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

    /// Compiles an expression of a liveness atom in the scope of an instance, where what it prints
    /// is printed, or `None` when the engine can't translate the scope.
    pub fn compile_in_scope(
        &mut self,
        node: NodeId,
        scope: Option<Index>,
    ) -> Result<Option<Compiled>, CompileError> {
        let Some(context) = self.context_from_scope(scope)? else {
            return Ok(None);
        };
        let context = Context {
            can_print: true,
            ..context
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
        let context = Context {
            can_print: true,
            ..context
        };
        self.compile_enabled(action, &context).map(Some)
    }
}
