//! The counting variant's walks of the initial predicate and of TLC's actions, as
//! `Tool.getInitStates` and `Tool.getNextStates` walk them and count: a leaf of a next-state walk
//! (a guard that holds, `x' = e`, `x' \in S`, UNCHANGED) counts once each time the walk after it
//! adds a successor, and an initial state counts into the leaf that completed it and into its
//! root (design/coverage.md). What TLC evaluates rather than walks counts as `Tool.eval` does
//! (`compile/coverage.rs`).

use std::collections::HashMap;
use std::rc::Rc;
use std::sync::Arc;

use tla_ir::{Definition, DefinitionForm, Ir, NodeId, NodeKind, Resolution};
use tla_values::store::{FALSE, KIND_SET, Outcome, TRUE};
use tla_values::{Bail, Id};

use super::coverage::{CountedBound, Tag, enumerated};
use super::nodes::assign_bound;
use super::{Binding, Compiler, Compiling, Context, argument_context, lookup, operator_context};
use crate::coverage::{Cm, NO_CM};
use crate::machine::{Continue, Eval, Machine, Step, UNASSIGNED};

fn decline<T>(what: impl std::fmt::Display) -> Compiling<T> {
    Err(super::CompileError::Decline(format!("coverage: {what}")))
}

fn step(
    walk: impl Fn(&mut Machine<'_>, &mut Continue<'_>) -> Outcome<()> + Send + Sync + 'static,
) -> Step {
    Arc::new(walk)
}

/// The codes of SANY's built-in operators TLC's walk evaluates as values, counting their node
/// (`OPCODE_*`), where it applies an operator of a standard module without (`Op::Builtin`).
const CODES: &[&str] = &[
    "=",
    "#",
    "/=",
    "\\in",
    "\\notin",
    "\\subseteq",
    "\\cup",
    "\\union",
    "\\cap",
    "\\intersect",
    "\\",
    "SUBSET",
    "UNION",
    "DOMAIN",
    "~",
    "\\lnot",
    "\\neg",
    "/\\",
    "\\land",
    "\\/",
    "\\lor",
    "=>",
    "<=>",
    "\\equiv",
];

/// What is left of a walk once a leaf holds (`ActionItemList`): conjuncts to walk, and the
/// parts of an UNCHANGED tuple.
struct Act {
    node: NodeId,
    /// The scope it is walked in, its `cm` the wrapper it is looked up under.
    context: Context,
    is_unchanged: bool,
    next: Acts,
}

type Acts = Option<Rc<Act>>;

/// The counting variant of the initial predicate's walk and of each of TLC's actions', with the
/// invariants and constraints.
pub(crate) struct Counting {
    pub init: Step,
    pub actions: Vec<Step>,
    pub invariants: Vec<Eval>,
    /// The position of each of `invariants` in the model's: TLC checks no constant one.
    pub invariant_owners: Vec<usize>,
    pub action_constraints: Vec<Eval>,
    pub constraints: Vec<Eval>,
    pub constraint_owners: Vec<u32>,
}

/// The walks compile against whether they are of the initial predicate, which TLC's walk always
/// evaluates once every variable has a value, and whether the next-state walk does too, which it
/// does with warnings on.
struct Walks {
    is_init: bool,
    is_shortcut: bool,
    rests: HashMap<usize, (Rc<Act>, Step)>,
}

impl Compiler<'_> {
    /// The counting variant of what the search checks the model with, or why it doesn't count as
    /// TLC does.
    pub(crate) fn compile_counting(&mut self, ir: &Ir) -> Compiling<Counting> {
        let plan = Arc::clone(self.coverage.as_ref().expect("a plan"));
        let model = &ir.model;
        if plan.actions.len() != model.actions.len() || model.actions.is_empty() {
            return decline("actions other than TLC's");
        }
        // TLC computes a constant invariant or constraint as it starts, and checks nothing of it
        // after.
        let checked = |names: &mut dyn Iterator<Item = &tla_ir::ConfigName>| -> Vec<usize> {
            names
                .enumerate()
                .filter(|(_, name)| {
                    name.definition.is_none_or(|index| {
                        self.definition(ir.definitions[index as usize]).flags
                            & Definition::NORMALIZED
                            == 0
                    })
                })
                .map(|(position, _)| position)
                .collect()
        };
        let invariant_owners =
            checked(&mut model.invariants.iter().map(|invariant| &invariant.root));
        let constraint_owners: Vec<u32> = checked(&mut model.constraints.iter())
            .into_iter()
            .map(|position| position as u32)
            .collect();
        if invariant_owners.len() != plan.invariants.len()
            || constraint_owners.len() != plan.constraints.len()
            || checked(&mut model.action_constraints.iter()).len() != model.action_constraints.len()
            || plan.action_constraints.len() != model.action_constraints.len()
        {
            return decline("invariants or constraints other than TLC checks");
        }
        self.is_counting_now = true;
        let result = (|| {
            let mut walks = Walks {
                is_init: true,
                is_shortcut: true,
                rests: HashMap::new(),
            };
            let init_context = Context {
                is_init: true,
                ..Context::ROOT
            };
            let mut acts: Acts = None;
            for &(node, root) in plan.inits.iter().skip(1).rev() {
                acts = Some(Rc::new(Act {
                    node,
                    context: Context {
                        cm: root,
                        ..init_context.clone()
                    },
                    is_unchanged: false,
                    next: acts,
                }));
            }
            let Some(&(first, root)) = plan.inits.first() else {
                return decline("no initial predicate");
            };
            let init = self.counted_walk(
                &mut walks,
                first,
                &acts,
                &Context {
                    cm: root,
                    ..init_context
                },
            )?;
            let mut walks = Walks {
                is_init: false,
                is_shortcut: model.is_warning_enabled,
                rests: HashMap::new(),
            };
            let mut actions = Vec::new();
            for (action, &root) in model.actions.iter().zip(&plan.actions) {
                let Some(context) = self.context_from_scope(action.scope)? else {
                    return decline("an action's scope");
                };
                let context = Context {
                    cm: root,
                    ..context
                };
                actions.push(self.counted_walk(&mut walks, action.expression, &None, &context)?);
            }
            let rooted = |compiler: &mut Self, roots: &[(NodeId, Cm)]| {
                roots
                    .iter()
                    .map(|&(node, root)| {
                        let context = Context {
                            cm: root,
                            ..Context::ROOT
                        };
                        compiler
                            .compile(node, &context)
                            .map(|compiled| compiled.eval)
                    })
                    .collect::<Compiling<Vec<Eval>>>()
            };
            let invariants = rooted(self, &plan.invariants)?;
            // `isInModel` and `isInActions` count into the root where the constraint is false,
            // and into its secondary count where it holds.
            let constrained = |evaluators: Vec<Eval>, roots: &[(NodeId, Cm)]| -> Vec<Eval> {
                evaluators
                    .into_iter()
                    .zip(roots)
                    .map(|(evaluate, &(_, root))| {
                        super::eval(move |machine| {
                            let value = evaluate(machine)?;
                            match value {
                                TRUE => machine.coverage.secondary[root as usize] += 1,
                                FALSE => machine.count(root),
                                _ => {}
                            }
                            Ok(value)
                        })
                    })
                    .collect()
            };
            let constraints = constrained(rooted(self, &plan.constraints)?, &plan.constraints);
            let action_constraints = constrained(
                rooted(self, &plan.action_constraints)?,
                &plan.action_constraints,
            );
            Ok(Counting {
                init,
                actions,
                invariants,
                invariant_owners,
                action_constraints,
                constraints,
                constraint_owners,
            })
        })();
        self.is_counting_now = false;
        result
    }

    // The wrapper a walk looks a node up as under `cm`, which a walk doesn't count itself.
    fn counted_walk_wrapper(&self, node: NodeId, cm: Cm) -> Compiling<Cm> {
        let plan = self.coverage.as_ref().expect("a plan");
        let Some(&sany) = plan.of_ir.get(&self.node(node).0) else {
            return decline("an expression SANY's view of the IR lacks");
        };
        plan.get(cm, sany).or_else(decline)
    }

    // A walk of `node` then of `acts`, looked up under `context.cm` (`getNextStates(action,
    // acts, ...)`, `getInitStates(init, acts, ...)`).
    fn counted_walk(
        &mut self,
        walks: &mut Walks,
        node: NodeId,
        acts: &Acts,
        context: &Context,
    ) -> Compiling<Step> {
        let (_, kind) = self.node(node);
        match kind {
            NodeKind::Label { body, .. } => return self.counted_walk(walks, *body, acts, context),
            NodeKind::Let {
                definitions, body, ..
            } => {
                // TLC walks a LET's body binding nothing: each definition is applied anew where
                // the body names it.
                let inner = self.bind_let_definitions(definitions, *body, context, false)?;
                return self.counted_walk(walks, *body, acts, &inner);
            }
            _ => {}
        }
        let wrapper = self.counted_walk_wrapper(node, context.cm)?;
        let at = Context {
            cm: wrapper,
            ..context.clone()
        };
        match kind {
            NodeKind::And(operands) => {
                let sany = self.coverage.as_ref().expect("a plan").of_ir[&self.node(node).0];
                let parents = self.junction_parents(sany, operands.len(), context.cm)?;
                let mut inner = acts.clone();
                for (&operand, &parent) in operands.iter().zip(&parents).skip(1).rev() {
                    inner = Some(Rc::new(Act {
                        node: operand,
                        context: Context {
                            cm: parent,
                            ..context.clone()
                        },
                        is_unchanged: false,
                        next: inner,
                    }));
                }
                let first = Context {
                    cm: parents[0],
                    ..context.clone()
                };
                self.counted_walk(walks, operands[0], &inner, &first)
            }
            NodeKind::Or(operands) => {
                let sany = self.coverage.as_ref().expect("a plan").of_ir[&self.node(node).0];
                let parents = self.junction_parents(sany, operands.len(), context.cm)?;
                let branches = operands
                    .iter()
                    .zip(&parents)
                    .map(|(&operand, &parent)| {
                        let branch = Context {
                            cm: parent,
                            ..context.clone()
                        };
                        self.counted_walk(walks, operand, acts, &branch)
                    })
                    .collect::<Compiling<Vec<Step>>>()?;
                Ok(step(move |machine, on_complete| {
                    for branch in &branches {
                        branch(machine, on_complete)?;
                    }
                    Ok(())
                }))
            }
            NodeKind::Exists { bounds, body } => {
                let CountedBound {
                    set,
                    slots,
                    tuple,
                    scope,
                    built,
                } = self.counted_bound(bounds, &at)?;
                let body = self.counted_walk(walks, *body, acts, &scope)?;
                let set = set.eval;
                Ok(step(move |machine, on_complete| {
                    let id = set(machine)?;
                    for position in 0..machine.store.size_of(id) {
                        let element = machine.store.element_at(id, position);
                        assign_bound(machine, &slots, tuple, element)?;
                        body(machine, on_complete)?;
                    }
                    let size = machine.store.size_of(id);
                    enumerated(machine, built, size + 1);
                    Ok(())
                }))
            }
            NodeKind::If {
                condition,
                consequent,
                alternative,
            } => {
                let condition = self.compile(*condition, &at)?.eval;
                let consequent = self.counted_walk(walks, *consequent, acts, &at)?;
                let alternative = self.counted_walk(walks, *alternative, acts, &at)?;
                Ok(step(move |machine, on_complete| {
                    if boolean(machine, &condition)? {
                        consequent(machine, on_complete)
                    } else {
                        alternative(machine, on_complete)
                    }
                }))
            }
            NodeKind::Case { arms, other } if !walks.is_init => {
                let sany = self.coverage.as_ref().expect("a plan").of_ir[&self.node(node).0];
                let pairs = self.coverage.as_ref().expect("a plan").nodes[sany as usize]
                    .args
                    .clone();
                let mut tests = Vec::new();
                for (position, &(condition, body)) in arms.iter().enumerate() {
                    let pair = Context {
                        cm: self.counted_walk_wrapper_of(pairs[position], wrapper)?,
                        ..context.clone()
                    };
                    tests.push((
                        self.compile(condition, &pair)?.eval,
                        self.counted_walk(walks, body, acts, &pair)?,
                    ));
                }
                let otherwise = match other {
                    Some(other) => {
                        let pair = Context {
                            cm: self.counted_walk_wrapper_of(pairs[arms.len()], wrapper)?,
                            ..context.clone()
                        };
                        Some(self.counted_walk(walks, *other, acts, &pair)?)
                    }
                    None => None,
                };
                Ok(step(move |machine, on_complete| {
                    for (test, body) in &tests {
                        if boolean(machine, test)? {
                            return body(machine, on_complete);
                        }
                    }
                    match &otherwise {
                        Some(otherwise) => otherwise(machine, on_complete),
                        None => Err(Bail("no CASE arm holds")),
                    }
                }))
            }
            NodeKind::Unchanged(expression) if !walks.is_init => {
                self.counted_walk_unchanged(walks, *expression, acts, &at)
            }
            NodeKind::FunctionApplication { .. } if !walks.is_init => {
                // TLC applies the function and walks on where the value is TRUE, counting the
                // application only as a leaf.
                let value = self.counted_compile_uncounted_node(node, &at)?;
                self.counted_value_leaf(walks, value, acts, wrapper)
            }
            NodeKind::Apply { name, args } => {
                self.counted_walk_apply(walks, node, name, args, acts, &at)
            }
            NodeKind::Identifier(name) => {
                self.counted_walk_identifier(walks, node, name, acts, &at)
            }
            _ => decline(format!("a walk of {}", super::nodes::kind_name(kind))),
        }
    }

    fn counted_walk_wrapper_of(&self, sany: Option<u32>, cm: Cm) -> Compiling<Cm> {
        let plan = self.coverage.as_ref().expect("a plan");
        plan.get(cm, sany.expect("a node")).or_else(decline)
    }

    // The node's value as `Tool.eval` gives it, counting what it evaluates under `at.cm`, its own
    // wrapper, but not the wrapper itself.
    fn counted_compile_uncounted_node(&mut self, node: NodeId, at: &Context) -> Compiling<Eval> {
        match self.node(node).1 {
            NodeKind::FunctionApplication { function, args } => {
                let [argument] = &args[..] else {
                    return decline("a function applied to several arguments");
                };
                // TLC applies a function it keeps lazy without building it, which counts its body
                // only for the argument and builds nothing.
                if !self.is_strict_function(*function, at) {
                    return decline("a function TLC may keep lazy, applied");
                }
                let function = self.compile(*function, at)?.eval;
                let argument = self.compile(*argument, at)?.eval;
                Ok(super::eval(move |machine| {
                    let value = function(machine)?;
                    let key = argument(machine)?;
                    machine.store.apply(value, key)
                }))
            }
            _ => Ok(self.compile_node(node, at)?.eval),
        }
    }

    fn counted_walk_apply(
        &mut self,
        walks: &mut Walks,
        node: NodeId,
        name: &tla_ir::Name,
        args: &[NodeId],
        acts: &Acts,
        at: &Context,
    ) -> Compiling<Step> {
        let wrapper = at.cm;
        if !name.is_local
            && let Resolution::Builtin(index) = name.resolution
        {
            let builtin = self.builtin_name(index);
            if (builtin == "=" || builtin == "\\in")
                && let Some(variable) =
                    self.counted_assigned_variable(args[0], at, walks.is_init)?
            {
                let is_membership = builtin == "\\in";
                let tag = self.tag_of(args[1], at);
                if is_membership && tag == Tag::Unknown {
                    return decline("x' \\in S of a set that may carry a cost model");
                }
                let built = match tag {
                    Tag::Built(wrapper) if is_membership => Some(wrapper),
                    _ => None,
                };
                let value = self.compile(args[1], at)?;
                if is_membership && !value.is_normalized {
                    return decline("x' \\in S of a set TLC keeps lazy");
                }
                let value = value.eval;
                let rest = self.counted_leaf_rest(walks, acts, wrapper)?;
                let is_init = walks.is_init;
                return Ok(step(move |machine, on_complete| {
                    let value = value(machine)?;
                    let held = target(machine, is_init)[variable as usize];
                    if held == UNASSIGNED {
                        if !is_membership {
                            target(machine, is_init)[variable as usize] = value;
                            let result = rest(machine, on_complete);
                            target(machine, is_init)[variable as usize] = UNASSIGNED;
                            return result;
                        }
                        if machine.store.kind_of(value) != KIND_SET {
                            return Err(Bail("x' \\in S of a non-set"));
                        }
                        for position in 0..machine.store.size_of(value) {
                            let element = machine.store.element_at(value, position);
                            target(machine, is_init)[variable as usize] = element;
                            let result = rest(machine, on_complete);
                            target(machine, is_init)[variable as usize] = UNASSIGNED;
                            result?;
                        }
                        let size = machine.store.size_of(value);
                        enumerated(machine, built, size + 1);
                        return Ok(());
                    }
                    if super::coverage::holds_function(machine, held) {
                        machine.abandon_coverage("a function TLC may compare between classes");
                    }
                    let holds = if is_membership {
                        machine.store.is_member(held, value)?
                    } else {
                        machine.store.equals(held, value)?
                    };
                    if holds {
                        rest(machine, on_complete)
                    } else {
                        Ok(())
                    }
                }));
            }
            if builtin == "=>" {
                let condition = self.compile(args[0], at)?.eval;
                let then = self.counted_walk(walks, args[1], acts, at)?;
                let rest = self.counted_leaf_rest(walks, acts, wrapper)?;
                return Ok(step(move |machine, on_complete| {
                    if boolean(machine, &condition)? {
                        then(machine, on_complete)
                    } else {
                        rest(machine, on_complete)
                    }
                }));
            }
            if matches!(builtin, "\\subseteq" | "/\\" | "\\land" | "\\/" | "\\lor") {
                return decline(format!("{builtin} in a walk"));
            }
            // A code TLC evaluates counting its node; an operator of a standard module whose
            // operands it evaluates without.
            let value = if CODES.contains(&builtin) {
                self.compile(node, at)?.eval
            } else {
                self.check_builtin(builtin, args, at)?;
                let compiled = self.compile_node(node, at)?;
                self.guard_builtin(builtin, args, at, compiled)?.eval
            };
            return self.counted_value_leaf(walks, value, acts, wrapper);
        }
        // An operator's body, walked in its arguments, each a lazy value TLC binds as it walks
        // into it.
        let (params, body, base) = match (name.is_local, name.resolution) {
            (false, Resolution::Definition(index)) => {
                let definition_node = self.ir.definitions[index as usize];
                let definition = self.definition(definition_node);
                let DefinitionForm::Operator(params) = &definition.form else {
                    return decline("a function definition applied");
                };
                if definition.flags & Definition::RECURSIVE != 0 || at.is_expanding(definition_node)
                {
                    return decline("a RECURSIVE operator");
                }
                (
                    params.clone(),
                    definition.body,
                    Context {
                        expanding: at.expanding_with(definition_node),
                        ..at.global(false)
                    },
                )
            }
            _ => {
                let Some(found) = lookup(&at.scope, name.text) else {
                    return decline("an operator the walk doesn't find");
                };
                let Binding::Operator(operator) = &found.binding else {
                    return decline("an operator the walk doesn't follow");
                };
                let operator = Rc::clone(operator);
                let super::OperatorBody::Node(body) = operator.body else {
                    return decline("a builtin passed as an operator");
                };
                if operator.is_recursive {
                    return decline("a RECURSIVE operator");
                }
                (
                    operator.params.clone(),
                    body,
                    Context {
                        cm: wrapper,
                        ..operator_context(&operator).primed(at.is_primed)
                    },
                )
            }
        };
        let first = self.cell_count;
        let callee = self.bind_arguments(&params, args, Some(body), at, base)?;
        let walked = self.counted_walk(walks, body, acts, &callee)?;
        Ok(resetting(walked, first..self.cell_count))
    }

    fn counted_walk_identifier(
        &mut self,
        walks: &mut Walks,
        node: NodeId,
        name: &tla_ir::Name,
        acts: &Acts,
        at: &Context,
    ) -> Compiling<Step> {
        let wrapper = at.cm;
        if name.is_local
            && let Some(found) = lookup(&at.scope, name.text)
            && let Binding::Argument(argument) = &found.binding
        {
            let argument = Rc::clone(argument);
            let base = argument_context(&argument);
            let Some(cell) = argument.cell else {
                // A LET's definition, which a walk binds nothing to: walked anew.
                let applied = Context {
                    cm: wrapper,
                    ..base
                };
                return self.counted_walk(walks, argument.expression, acts, &applied);
            };
            if walks.is_init {
                return decline("an argument the initial predicate walks");
            }
            // A lazy value TLC kept is a value; otherwise TLC walks its expression, keeping
            // nothing.
            let walked = self.counted_walk(walks, argument.expression, acts, &base)?;
            let quiet = self
                .compile(argument.expression, &Context { cm: NO_CM, ..base })?
                .eval;
            let kept = self.counted_value_leaf(walks, quiet, acts, wrapper)?;
            return Ok(step(move |machine, on_complete| {
                if machine.is_cell_kept(cell) {
                    kept(machine, on_complete)
                } else {
                    walked(machine, on_complete)
                }
            }));
        }
        if !name.is_local
            && let Resolution::Definition(index) = name.resolution
        {
            let definition_node = self.ir.definitions[index as usize];
            let definition = self.definition(definition_node);
            if !self.is_computed_at_startup(name.text, index) {
                let DefinitionForm::Operator(params) = &definition.form else {
                    return decline("a function definition walked");
                };
                if !params.is_empty() || at.is_expanding(definition_node) {
                    return decline("a definition the walk can't take");
                }
                if self.startup_definitions.contains_key(&definition_node) {
                    return decline("a constant definition with effects");
                }
                let base = Context {
                    expanding: at.expanding_with(definition_node),
                    ..at.global(false)
                };
                return self.counted_walk(walks, definition.body, acts, &base);
            }
        }
        // A value: a variable's, a constant's, a bound name's, what TLC computed at startup.
        let value = super::Compiler::compile_node(
            self,
            node,
            &Context {
                cm: NO_CM,
                ..at.clone()
            },
        )?
        .eval;
        self.counted_value_leaf(walks, value, acts, wrapper)
    }

    // `processUnchanged`: each variable of the expression assigned its current value, or tested.
    fn counted_walk_unchanged(
        &mut self,
        walks: &mut Walks,
        expression: NodeId,
        acts: &Acts,
        context: &Context,
    ) -> Compiling<Step> {
        let wrapper = self.counted_walk_wrapper(expression, context.cm)?;
        let at = Context {
            cm: wrapper,
            ..context.clone()
        };
        if let Some(variable) = self.counted_named_variable(expression, &at)? {
            let rest = self.counted_leaf_rest(walks, acts, wrapper)?;
            return Ok(step(move |machine, on_complete| {
                let before = machine.cur[variable as usize];
                let held = machine.next[variable as usize];
                if held == UNASSIGNED {
                    machine.next[variable as usize] = before;
                    let result = rest(machine, on_complete);
                    machine.next[variable as usize] = UNASSIGNED;
                    return result;
                }
                if machine.store.equals(before, held)? {
                    rest(machine, on_complete)
                } else {
                    machine.abandon_coverage("a variable changed an UNCHANGED leaves");
                    Ok(())
                }
            }));
        }
        match self.node(expression).1 {
            NodeKind::Label { body, .. } => {
                self.counted_walk_unchanged(walks, *body, acts, context)
            }
            NodeKind::Tuple(items) => {
                if items.is_empty() {
                    return self.counted_leaf_rest(walks, acts, wrapper);
                }
                let mut inner = acts.clone();
                for &item in items[1..].iter().rev() {
                    inner = Some(Rc::new(Act {
                        node: item,
                        context: at.clone(),
                        is_unchanged: true,
                        next: inner,
                    }));
                }
                self.counted_walk_unchanged(walks, items[0], &inner, &at)
            }
            NodeKind::Identifier(name)
                if !name.is_local && matches!(name.resolution, Resolution::Definition(_)) =>
            {
                let Resolution::Definition(index) = name.resolution else {
                    unreachable!("a definition")
                };
                let definition_node = self.ir.definitions[index as usize];
                let definition = self.definition(definition_node);
                if self.is_computed_at_startup(name.text, index)
                    || !matches!(&definition.form, DefinitionForm::Operator(params)
                        if params.is_empty())
                {
                    return self.counted_verify_unchanged(walks, expression, acts, &at);
                }
                let base = Context {
                    expanding: at.expanding_with(definition_node),
                    ..at.global(false)
                };
                self.counted_walk_unchanged(walks, definition.body, acts, &base)
            }
            _ => self.counted_verify_unchanged(walks, expression, acts, &at),
        }
    }

    // `verifyUnchanged`: the expression's value in the two states, compared.
    fn counted_verify_unchanged(
        &mut self,
        walks: &mut Walks,
        expression: NodeId,
        acts: &Acts,
        at: &Context,
    ) -> Compiling<Step> {
        let now = self.compile(expression, &at.primed(false))?.eval;
        let next = self.compile(expression, &at.primed(true))?.eval;
        let rest = self.counted_leaf_rest(walks, acts, at.cm)?;
        Ok(step(move |machine, on_complete| {
            let now = now(machine)?;
            let next = next(machine)?;
            if super::coverage::holds_function(machine, now) {
                machine.abandon_coverage("a function TLC may compare between classes");
            }
            if machine.store.equals(now, next)? {
                rest(machine, on_complete)
            } else {
                Ok(())
            }
        }))
    }

    // A value the walk goes on past where it is TRUE (`getNextStatesApplUsrDefOp`).
    fn counted_value_leaf(
        &mut self,
        walks: &mut Walks,
        value: Eval,
        acts: &Acts,
        wrapper: Cm,
    ) -> Compiling<Step> {
        let rest = self.counted_leaf_rest(walks, acts, wrapper)?;
        Ok(step(move |machine, on_complete| {
            if boolean(machine, &value)? {
                rest(machine, on_complete)
            } else {
                Ok(())
            }
        }))
    }

    // What follows a leaf at `wrapper`: in a next-state walk the rest, counting the leaf where
    // the rest added a successor (`getNextStates(acts, ..., cm)`); in the initial predicate's,
    // the rest, which counts the leaf that completes a state.
    fn counted_leaf_rest(
        &mut self,
        walks: &mut Walks,
        acts: &Acts,
        wrapper: Cm,
    ) -> Compiling<Step> {
        let rest = self.counted_rest(walks, acts)?;
        if walks.is_init {
            let root = self
                .coverage
                .as_ref()
                .expect("a plan")
                .tree
                .root_of(wrapper);
            return Ok(step(move |machine, on_complete| {
                machine.coverage.leaf = (wrapper, root);
                rest(machine, on_complete)
            }));
        }
        Ok(step(move |machine, on_complete| {
            let before = machine.coverage.added;
            rest(machine, on_complete)?;
            if machine.coverage.added > before {
                machine.count(wrapper);
            }
            Ok(())
        }))
    }

    // The walk of what is left, once (`getNextStates(acts, ...)`, `getInitStates(acts, ...)`).
    fn counted_rest(&mut self, walks: &mut Walks, acts: &Acts) -> Compiling<Step> {
        let Some(head) = acts else {
            let is_init = walks.is_init;
            return Ok(step(move |machine, on_complete| {
                if is_init {
                    let (leaf, root) = machine.coverage.leaf;
                    machine.count(leaf);
                    machine.count(root);
                } else {
                    machine.coverage.added += 1;
                }
                on_complete(machine)
            }));
        };
        let key = Rc::as_ptr(head) as usize;
        if let Some((_, known)) = walks.rests.get(&key) {
            return Ok(Arc::clone(known));
        }
        let walked = if head.is_unchanged {
            self.counted_walk_unchanged(walks, head.node, &head.next, &head.context)?
        } else {
            self.counted_walk(walks, head.node, &head.next, &head.context)?
        };
        let compiled = if walks.is_shortcut {
            self.counted_shortcut(walks, head, walked)?
        } else {
            walked
        };
        walks
            .rests
            .insert(key, (Rc::clone(head), Arc::clone(&compiled)));
        Ok(compiled)
    }

    // Once every variable has a value, TLC evaluates what is left rather than walking it: in the
    // initial predicate always, counting a state into the leaf that completed it or a failed one
    // into the root's secondary count; in a next-state walk with warnings on, counting nothing
    // but what it evaluates, and walking an UNCHANGED left (`getNextStatesAllAssigned`).
    fn counted_shortcut(
        &mut self,
        walks: &mut Walks,
        head: &Rc<Act>,
        walked: Step,
    ) -> Compiling<Step> {
        enum Left {
            Holds(Eval),
            Unchanged(Step),
        }
        let mut left = Vec::new();
        let mut act = Some(Rc::clone(head));
        while let Some(current) = act {
            if current.is_unchanged {
                if walks.is_init {
                    return decline("UNCHANGED in the initial predicate");
                }
                let unchanged = self.counted_walk_unchanged(
                    walks,
                    current.node,
                    &current.next,
                    &current.context,
                )?;
                left.push(Left::Unchanged(unchanged));
                break;
            }
            let context = Context {
                is_init: walks.is_init,
                ..current.context.clone()
            };
            left.push(Left::Holds(self.compile(current.node, &context)?.eval));
            act = current.next.clone();
        }
        let is_init = walks.is_init;
        Ok(step(move |machine, on_complete| {
            if target(machine, is_init).contains(&UNASSIGNED) {
                return walked(machine, on_complete);
            }
            for item in &left {
                match item {
                    Left::Holds(holds) => {
                        if !boolean(machine, holds)? {
                            if is_init {
                                let (_, root) = machine.coverage.leaf;
                                machine.coverage.secondary[root as usize] += 1;
                            }
                            return Ok(());
                        }
                    }
                    Left::Unchanged(unchanged) => return unchanged(machine, on_complete),
                }
            }
            if is_init {
                let (leaf, root) = machine.coverage.leaf;
                machine.count(leaf);
                machine.count(root);
            } else {
                machine.coverage.added += 1;
            }
            on_complete(machine)
        }))
    }

    // The variable `x' = e` or `x' \in S` assigns: `x'` in a next-state walk, `x` in the initial
    // predicate's, through definitions and arguments (`getPrimedVar`, `getVar`).
    fn counted_assigned_variable(
        &self,
        node: NodeId,
        context: &Context,
        is_init: bool,
    ) -> Compiling<Option<u32>> {
        if is_init {
            return self.counted_named_variable(node, context);
        }
        match self.node(node).1 {
            NodeKind::Label { body, .. } => self.counted_assigned_variable(*body, context, is_init),
            NodeKind::Prime(inner) => self.counted_named_variable(*inner, context),
            NodeKind::Identifier(name) => match self.counted_named_target(name, context) {
                Some((expression, inner)) => {
                    self.counted_assigned_variable(expression, &inner, is_init)
                }
                None => Ok(None),
            },
            _ => Ok(None),
        }
    }

    // The variable an expression names, through definitions and arguments (`getVar`).
    fn counted_named_variable(&self, node: NodeId, context: &Context) -> Compiling<Option<u32>> {
        match self.node(node).1 {
            NodeKind::Label { body, .. } => self.counted_named_variable(*body, context),
            NodeKind::Identifier(name) => {
                if !name.is_local
                    && let Resolution::Variable(index) = name.resolution
                {
                    if index as usize >= self.ir.variables.len() {
                        return decline("a variable past the state's");
                    }
                    return Ok(Some(index));
                }
                match self.counted_named_target(name, context) {
                    Some((expression, inner)) => self.counted_named_variable(expression, &inner),
                    None => Ok(None),
                }
            }
            NodeKind::Let { .. } => decline("a LET where TLC looks for a variable"),
            _ => Ok(None),
        }
    }

    // What a name stands for that TLC looks through for a variable: an argument's expression, or
    // a definition's body, TLC computing neither at startup.
    fn counted_named_target(
        &self,
        name: &tla_ir::Name,
        context: &Context,
    ) -> Option<(NodeId, Context)> {
        if name.is_local
            && let Some(found) = lookup(&context.scope, name.text)
        {
            return match &found.binding {
                Binding::Argument(argument) => {
                    Some((argument.expression, argument_context(argument)))
                }
                _ => None,
            };
        }
        let Resolution::Definition(index) = name.resolution else {
            return None;
        };
        let definition = self.definition(self.ir.definitions[index as usize]);
        (!self.is_computed_at_startup(name.text, index)
            && matches!(&definition.form, DefinitionForm::Operator(params) if params.is_empty()))
        .then(|| (definition.body, context.global(false)))
    }
}

// The variables a walk assigns: the current state's in the initial predicate, else the next's.
fn target<'m>(machine: &'m mut Machine<'_>, is_init: bool) -> &'m mut Vec<Id> {
    if is_init {
        &mut machine.cur
    } else {
        &mut machine.next
    }
}

fn boolean(machine: &mut Machine<'_>, evaluate: &Eval) -> Outcome<bool> {
    match evaluate(machine)? {
        TRUE => Ok(true),
        FALSE => Ok(false),
        _ => Err(Bail("expected a boolean")),
    }
}

// Forgets the lazy values of the arguments a walk binds as it walks into an operator.
fn resetting(walked: Step, cells: std::ops::Range<usize>) -> Step {
    if cells.is_empty() {
        return walked;
    }
    step(move |machine, on_complete| {
        for cell in cells.clone() {
            machine.coverage.cells[cell].is_kept = false;
        }
        walked(machine, on_complete)
    })
}
