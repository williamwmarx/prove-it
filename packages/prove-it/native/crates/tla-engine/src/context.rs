//! What a search needs of a model: the walks of the initial predicate and the next-state
//! relation, and the compiled invariants, constraints and properties, as `createEngineContext` in
//! `context.ts` builds them, in its order.

use std::collections::HashSet;

use tla_ir::{
    AtomKind, ConfigName, Definition, DefinitionForm, EnabledActions, Index, Ir, NodeId, NodeKind,
    PredicateForm, Resolution, ScopeBinding,
};
use tla_values::Bail;
use tla_values::store::{FALSE, Outcome, TRUE};

use crate::compile::{ActionOptions, CompileError, Compiled, Compiler, Root};
use crate::machine::{Eval, Machine, Step};

/// A predicate checked conjunct by conjunct, with the variables it reads when a successor that
/// leaves them unchanged may skip it.
pub struct Predicate {
    pub eval: Eval,
    pub vars: Option<Vec<u32>>,
}

pub struct EngineContext {
    pub width: usize,
    /// Whether the search reads TLC's diameter, which the native checker doesn't follow: it
    /// stops once TLC has started, as an assumption may stop TLC first.
    pub is_diameter_searched: bool,
    /// Whether the VIEW reads what the search sets, such as TLCGet("level"), which the native
    /// checker doesn't follow: it too stops once TLC has started.
    pub is_view_search_read: bool,
    pub init: Step,
    /// The walk of the next-state relation, none where the configuration names none: TLC then
    /// stops once it has the initial states.
    pub next: Option<Step>,
    /// A walk of each of TLC's actions, which together take the steps of `next` in its order, or
    /// `None` when the engine can't build one. The search walks them only when the model asks it
    /// to label its steps; they also label the steps of a path it prints.
    pub actions: Option<Vec<Step>>,
    pub invariants: Vec<Predicate>,
    /// For each of `invariants`, the first invariant it is a conjunct of: a position in the
    /// model's invariants, then past them in its properties checked as invariants. Checked in
    /// order, the first that fails names the invariant TLC reports violated.
    pub invariant_owners: Vec<usize>,
    /// The invariants an initial state may violate: the others are conjuncts of the initial
    /// predicate, so hold of every state it gives.
    pub initial_invariants: Vec<Eval>,
    /// The owner of each of `initial_invariants`, as `invariant_owners`.
    pub initial_invariant_owners: Vec<usize>,
    pub constraints: Vec<Predicate>,
    /// For each of `constraints`, the position in the model's constraints of the first it is a
    /// conjunct of.
    pub constraint_owners: Vec<u32>,
    pub action_constraints: Vec<Eval>,
    /// The `_POSSIBLE` predicates, each with whether it is of a step: TLC counts the states in the
    /// model, or the steps, each holds of.
    pub possible: Vec<(Eval, bool)>,
    /// Each holds of a step unless the action and the subscript's UNCHANGED are both false.
    pub action_properties: Vec<(Eval, Eval)>,
    pub initial_predicates: Vec<Eval>,
    /// The value a VIEW maps the current state to, which the search tells states apart by.
    pub view: Option<Eval>,
    /// The liveness checker's atoms, compiled, when the search records its graph.
    pub atoms: Vec<Atom>,
    /// Whether evaluating an atom may print.
    pub is_live_printing: bool,
    /// Whether an atom sets or reads TLC's registers, which the search then answers as TLC
    /// evaluates it.
    pub is_live_registered: bool,
    /// Whether each atom reads TLCGet("diameter").
    pub diameter_atoms: Vec<bool>,
    /// Whether each atom reads TLCGet("level").
    pub level_atoms: Vec<bool>,
    /// Whether an invariant may print, which the search prints among Next's prints.
    pub is_invariant_printing: bool,
    /// What TLC evaluates when it starts.
    pub startup: Startup,
}

/// What TLC evaluates when it starts, compiled: each substitute, then each constant definition
/// with effects, then the symmetry, then each assumption, with the name TLC reports it by.
pub struct Startup {
    pub substitutes: Vec<Eval>,
    pub definitions: Vec<Eval>,
    /// The constant definitions the configuration names, with how TLC rejects each one's value
    /// and the configuration error's words for it.
    pub predicates: Vec<(Eval, PredicateForm, String, String)>,
    pub symmetry: Option<StartupSymmetry>,
    pub assumptions: Vec<(Eval, String)>,
}

/// The SYMMETRY definition's body, and each set it permutes: the name TLC's warning gives it, and
/// the set TLC checks for a model value the group moves.
pub struct StartupSymmetry {
    pub definition: Eval,
    pub permuted_sets: Vec<(String, Option<Eval>)>,
}

/// How the engine answers a liveness atom on its states, or why it can't, in which case the
/// interpreter answers it (`createLiveOracle` in `live.ts`).
pub enum Atom {
    State(Eval),
    /// A state predicate that reads TLCGet("level"), answered at the level of the state TLC adds
    /// and of each state a step from it reaches, one past it (`Table`).
    LevelState(Eval),
    /// An action that reads TLCGet("level"), at the level of its step's first state, and of the
    /// next one past it but for the stuttering step's. Its subscript doesn't read the level.
    LevelAction {
        action: Eval,
        subscript: Option<Eval>,
    },
    /// An action, false of a step that leaves the subscript unchanged, and the position of the
    /// ENABLED atom of its fairness: the checker asks about no step from a state where that is
    /// false.
    Action {
        action: Eval,
        subscript: Option<Eval>,
        enabled: Option<usize>,
        /// Whether the action is the next-state relation itself, which holds of every step the
        /// search took where TLC's predicate evaluation of it can't fail.
        is_next: bool,
    },
    /// ENABLED, run, or answered from the steps the search took when the action is made of TLC's
    /// actions of the next-state relation.
    Enabled {
        run: Result<Eval, String>,
        steps: Option<EnabledSteps>,
    },
    Unknown(String),
}

/// ENABLED <<A>>_v holds of a state the search ran TLC's actions from just when one of the steps A
/// takes changes v.
pub struct EnabledSteps {
    pub subscript: Eval,
    /// What the subscript's value depends on besides the state, which the atoms whose subscripts
    /// have the same share their values of.
    pub key: SubscriptKey,
    /// The positions of TLC's actions A splits into, or `None` for all of them.
    pub actions: Option<Vec<bool>>,
}

/// A subscript's expression and the scope it is read in.
pub type SubscriptKey = (NodeId, Option<Index>);

// What a subscript's value depends on besides the state: the expression in its scope, or, for a
// definition of a module without parameters read where the scopes bind only values, which none of
// its names can be bound to, the definition alone.
fn get_subscript_key(ir: &Ir, node: NodeId, scope: Option<Index>) -> SubscriptKey {
    let mut id = node;
    while let NodeKind::Reference(target) = &ir.nodes.arena[id as usize].kind {
        id = *target;
    }
    let definition = match &ir.nodes.arena[id as usize].kind {
        NodeKind::Identifier(name) if !name.is_local => match name.resolution {
            Resolution::Definition(index) => Some(ir.definitions[index as usize]),
            _ => None,
        },
        _ => None,
    };
    let is_parameterless = definition.is_some_and(|definition| {
        matches!(
            &ir.nodes.arena[definition as usize].kind,
            NodeKind::Definition(definition)
                if matches!(&definition.form, DefinitionForm::Operator(params) if params.is_empty())
        )
    });
    let mut bound = scope;
    let mut binds_values = true;
    while let Some(index) = bound {
        let entry = &ir.scopes[index as usize];
        binds_values &= matches!(entry.binding, ScopeBinding::Value(_));
        bound = entry.parent;
    }
    match definition {
        Some(definition) if is_parameterless && binds_values => (definition, None),
        _ => (id, scope),
    }
}

/// Whether a compiled predicate holds, failing on a value that isn't a boolean.
pub fn holds(machine: &mut Machine<'_>, predicate: &Eval) -> Outcome<bool> {
    match predicate(machine)? {
        TRUE => Ok(true),
        FALSE => Ok(false),
        _ => Err(Bail("a predicate that isn't a boolean")),
    }
}

/// The position of the first predicate that doesn't hold, if one doesn't.
pub fn holds_all(machine: &mut Machine<'_>, predicates: &[Eval]) -> Outcome<bool> {
    for predicate in predicates {
        if !holds(machine, predicate)? {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Counts each `_POSSIBLE` predicate of a state, or with `is_action` of a step, that holds, as
/// `trackPossible` does.
pub fn count_possible(
    machine: &mut Machine<'_>,
    possible: &[(Eval, bool)],
    is_action: bool,
    counts: &mut [i64],
) -> Outcome<()> {
    for ((predicate, is_of_step), count) in possible.iter().zip(counts) {
        if *is_of_step == is_action {
            *count = (*count).max(0) + i64::from(holds(machine, predicate)?);
        }
    }
    Ok(())
}

/// Whether every predicate holds of the successor that is current, given that each held of its
/// parent.
pub fn holds_all_changed(
    machine: &mut Machine<'_>,
    predicates: &[Predicate],
    successor: &[u32],
    parent: &[u32],
) -> Outcome<bool> {
    first_failing_changed(machine, predicates, successor, parent)
        .map(|failing| failing.is_none())
        .map_err(|(_, bail)| bail)
}

/// The position of the first predicate that doesn't hold of the successor that is current, given
/// that each held of its parent: one that reads only variables the step left unchanged has the
/// parent's value.
pub fn first_failing_changed(
    machine: &mut Machine<'_>,
    predicates: &[Predicate],
    successor: &[u32],
    parent: &[u32],
) -> Result<Option<usize>, (usize, Bail)> {
    for (position, predicate) in predicates.iter().enumerate() {
        if let Some(vars) = &predicate.vars
            && vars
                .iter()
                .all(|&variable| successor[variable as usize] == parent[variable as usize])
        {
            continue;
        }
        if !holds(machine, &predicate.eval).map_err(|bail| (position, bail))? {
            return Ok(Some(position));
        }
    }
    Ok(None)
}

/// A conjunct the engine checks: a name the configuration gives, as an identifier of it, or an
/// expression of the model.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Conjunct {
    Named(Index),
    Node(NodeId),
    /// An expression read in the scope of the instance it comes from, checked whole.
    Scoped(NodeId, Index),
}

struct Conjuncts<'i> {
    ir: &'i Ir,
    found: Vec<Conjunct>,
    seen: HashSet<Conjunct>,
    expanded: HashSet<Index>,
    expanding: HashSet<Index>,
}

impl<'i> Conjuncts<'i> {
    fn new(ir: &'i Ir) -> Conjuncts<'i> {
        Conjuncts {
            ir,
            found: Vec::new(),
            seen: HashSet::new(),
            expanded: HashSet::new(),
            expanding: HashSet::new(),
        }
    }

    fn resolve(&self, node: NodeId) -> (NodeId, &'i NodeKind) {
        let mut id = node;
        loop {
            match &self.ir.nodes.arena[id as usize].kind {
                NodeKind::Reference(target) => id = *target,
                kind => return (id, kind),
            }
        }
    }

    fn definition(&self, index: Index) -> &'i Definition {
        match self.resolve(self.ir.definitions[index as usize]).1 {
            NodeKind::Definition(definition) => definition,
            _ => panic!("a definition that isn't one"),
        }
    }

    // The definition a conjunct asserts, a zero-arity operator TLC doesn't evaluate at startup,
    // as the compiler resolves a name nothing binds locally.
    fn asserted(&self, conjunct: Conjunct) -> Option<Index> {
        let index = match conjunct {
            Conjunct::Named(index) => index,
            Conjunct::Scoped(..) => return None,
            Conjunct::Node(node) => match self.resolve(node).1 {
                NodeKind::Identifier(name) if !name.is_local => match name.resolution {
                    Resolution::Definition(index) => index,
                    _ => return None,
                },
                _ => return None,
            },
        };
        let is_operator = matches!(
            &self.definition(index).form,
            DefinitionForm::Operator(params) if params.is_empty()
        );
        (is_operator && !self.ir.model.startup.definitions.contains(&index)).then_some(index)
    }

    fn add(&mut self, conjunct: Conjunct) {
        if self.seen.insert(conjunct) {
            self.found.push(conjunct);
        }
    }

    // The expressions an expression asserts as conjuncts, through zero-arity definitions. A
    // definition that reaches itself stays a conjunct, for the compiler to refuse.
    fn collect(&mut self, conjunct: Conjunct) {
        let conjunct = match conjunct {
            Conjunct::Node(node) => Conjunct::Node(self.resolve(node).0),
            other => other,
        };
        if let Conjunct::Node(node) = conjunct
            && let NodeKind::And(operands) = self.resolve(node).1
        {
            for &operand in operands {
                self.collect(Conjunct::Node(operand));
            }
            return;
        }
        match self.asserted(conjunct) {
            Some(index) if !self.expanding.contains(&index) => {
                if self.expanded.insert(index) {
                    self.expanding.insert(index);
                    self.collect(Conjunct::Node(self.definition(index).body));
                    self.expanding.remove(&index);
                }
            }
            _ => self.add(conjunct),
        }
    }
}

fn named(kind: &str, ir: &Ir, name: &ConfigName) -> Result<Index, CompileError> {
    name.definition.ok_or_else(|| {
        CompileError::Bail(format!(
            "the {kind} {} isn't defined",
            ir.texts[name.name as usize]
        ))
    })
}

fn compile_conjunct(
    compiler: &mut Compiler<'_>,
    conjunct: Conjunct,
    can_print: bool,
) -> Result<Compiled, CompileError> {
    let (root, scope) = match conjunct {
        Conjunct::Named(index) => (Root::Definition(index), None),
        Conjunct::Node(node) => (Root::Expression(node), None),
        Conjunct::Scoped(node, scope) => (Root::Expression(node), Some(scope)),
    };
    compiler.compile_scoped(root, scope, can_print)
}

// The variables a state predicate reads, which decide its value: it reads only its footprint.
fn predicate_vars(compiled: &Compiled, width: usize) -> Option<Vec<u32>> {
    let footprint = &compiled.footprint;
    if !footprint.primes.is_empty() || !footprint.slots.is_empty() || footprint.vars.len() == width
    {
        return None;
    }
    Some(footprint.vars.clone())
}

impl EngineContext {
    /// Compiles what a search of the model needs. A model whose invariants may print is the
    /// TypeScript engine's, since the native engine leaves printing to the interpreter.
    pub fn build(compiler: &mut Compiler<'_>, ir: &Ir) -> Result<EngineContext, CompileError> {
        let model = &ir.model;
        let width = ir.variables.len();
        let startup = Startup {
            substitutes: model
                .startup
                .substitutes
                .iter()
                .map(|&(_, index)| {
                    let body = match &ir.nodes.arena[ir.definitions[index as usize] as usize].kind {
                        NodeKind::Definition(definition) => definition.body,
                        _ => unreachable!("a definition's node"),
                    };
                    compiler
                        .compile_root_printing(Root::Expression(body), true)
                        .map(|compiled| compiled.eval)
                })
                .collect::<Result<_, CompileError>>()?,
            definitions: model
                .startup
                .definitions
                .iter()
                .map(|&index| {
                    compiler
                        .compile_root_printing(Root::Definition(index), true)
                        .map(|compiled| compiled.eval)
                })
                .collect::<Result<_, CompileError>>()?,
            predicates: model
                .startup
                .predicates
                .iter()
                .map(|predicate| {
                    compiler
                        .compile_root_printing(Root::Definition(predicate.definition), true)
                        .map(|compiled| {
                            (
                                compiled.eval,
                                predicate.form,
                                ir.texts[predicate.kind as usize].to_string(),
                                ir.texts[predicate.name as usize].to_string(),
                            )
                        })
                })
                .collect::<Result<_, CompileError>>()?,
            symmetry: model
                .startup
                .symmetry
                .as_ref()
                .map(|symmetry| {
                    let body = match &ir.nodes.arena
                        [ir.definitions[symmetry.definition as usize] as usize]
                        .kind
                    {
                        NodeKind::Definition(definition) => definition.body,
                        _ => unreachable!("a definition's node"),
                    };
                    Ok::<_, CompileError>(StartupSymmetry {
                        definition: compiler.compile_symmetry(body)?.eval,
                        permuted_sets: symmetry
                            .permuted_sets
                            .iter()
                            .map(|set| {
                                let operand = set
                                    .operand
                                    .map(|node| compiler.compile_root(Root::Expression(node)))
                                    .transpose()?;
                                Ok((
                                    ir.texts[set.name as usize].to_string(),
                                    operand.map(|compiled| compiled.eval),
                                ))
                            })
                            .collect::<Result<_, CompileError>>()?,
                    })
                })
                .transpose()?,
            assumptions: model
                .startup
                .assumptions
                .iter()
                .map(|&(node, name)| {
                    let eval = match compiler.compile_root_printing(Root::Expression(node), true) {
                        Ok(compiled) => compiled.eval,
                        // The native checker leaves one the engine doesn't compile to its
                        // caller, as it does one it stops at a limit of: RandomSubset in an
                        // operator's argument draws once where TLC first uses the argument.
                        Err(CompileError::Bail(_)) if compiler.is_native => {
                            crate::compile::eval(|_| Err(Bail(UNCOMPILED_ASSUMPTION)))
                        }
                        Err(error) => return Err(error),
                    };
                    Ok((eval, ir.texts[name as usize].to_string()))
                })
                .collect::<Result<_, CompileError>>()?,
        };
        // Each invariant and constraint is checked conjunct by conjunct, so a successor skips
        // each conjunct that reads only variables its step left unchanged. An invariant that may
        // print is checked whole each time, as TLC checks it, where the search may print.
        // With temporal properties, the search keeps what it prints until the checker has
        // evaluated the atoms, whose prints go between its own.
        let can_print = true;
        let mut conjuncts = Conjuncts::new(ir);
        let mut printed = HashSet::new();
        let mut invariant_owners = Vec::new();
        let roots = model
            .invariants
            .iter()
            .map(|invariant| {
                let root = Conjunct::Named(named("invariant", ir, &invariant.root)?);
                Ok((root, invariant.has_repeated_effect))
            })
            .chain(
                model
                    .property_invariants
                    .iter()
                    .zip(&model.property_invariant_scopes)
                    .map(|(invariant, scope)| {
                        Ok((
                            scope.map_or(Conjunct::Node(invariant.root), |scope| {
                                Conjunct::Scoped(invariant.root, scope)
                            }),
                            invariant.has_repeated_effect,
                        ))
                    }),
            )
            .collect::<Result<Vec<_>, CompileError>>()?;
        for (owner, (root, has_repeated_effect)) in roots.into_iter().enumerate() {
            if has_repeated_effect && can_print {
                printed.insert(root);
                conjuncts.add(root);
            } else {
                conjuncts.collect(root);
            }
            invariant_owners.resize(conjuncts.found.len(), owner);
        }
        let invariant_conjuncts = conjuncts.found;
        let invariants = invariant_conjuncts
            .iter()
            .map(|&conjunct| compile_conjunct(compiler, conjunct, printed.contains(&conjunct)))
            .collect::<Result<Vec<Compiled>, CompileError>>()?;
        let is_invariant_printing = invariants.iter().any(Compiled::is_printing);
        // An initial predicate in an instance's scope resolves its names there, so it implies
        // nothing.
        let init_conjuncts: HashSet<Conjunct> = if model.scope.is_none() {
            let mut found = Conjuncts::new(ir);
            found.collect(Conjunct::Node(model.init));
            found.found.into_iter().collect()
        } else {
            HashSet::new()
        };
        // TLC checks each step against the action properties as it finds the step, after the
        // invariants (`doNextCheckImplied`), as the search does, so they may print where the
        // native checker reports what the search finds.
        let mut action_properties = Vec::new();
        let is_native = compiler.is_native;
        for property in &model.action_properties {
            let action = compiler.compile_scoped(
                Root::Expression(property.action),
                property.scope,
                is_native,
            )?;
            let unchanged = compiler.compile_scoped(
                Root::Unchanged(property.subscript),
                property.scope,
                is_native,
            )?;
            action_properties.push((action.eval, unchanged.eval));
        }
        let initial_predicates = model
            .initial_predicates
            .iter()
            .zip(&model.initial_predicate_scopes)
            .map(|(&predicate, &scope)| {
                compiler
                    .compile_scoped(Root::Expression(predicate), scope, false)
                    .map(|compiled| compiled.eval)
            })
            .collect::<Result<Vec<Eval>, CompileError>>()?;
        let mut is_view_search_read = false;
        let view = match &model.view {
            Some(view) => {
                let compiled = compiler.compile_root(Root::Definition(named("view", ir, view)?))?;
                if compiled.reads_search() {
                    if !compiler.is_native {
                        return Err(CompileError::Bail(VIEW_SEARCH_READ.into()));
                    }
                    is_view_search_read = true;
                }
                Some(compiled.eval)
            }
            None => None,
        };
        // A constraint that may print or set a register is checked whole each time, as TLC
        // checks it, where the native checker reports what the search finds.
        let mut conjuncts = Conjuncts::new(ir);
        let mut constraint_owners = Vec::new();
        let mut printed = HashSet::new();
        for (owner, constraint) in model.constraints.iter().enumerate() {
            let root = Conjunct::Named(named("constraint", ir, constraint)?);
            if compiler.is_native && compile_conjunct(compiler, root, true)?.is_printing() {
                printed.insert(root);
                conjuncts.add(root);
            } else {
                conjuncts.collect(root);
            }
            constraint_owners.resize(conjuncts.found.len(), owner as u32);
        }
        let constraints = conjuncts
            .found
            .into_iter()
            .map(|conjunct| {
                compile_conjunct(compiler, conjunct, printed.contains(&conjunct)).map(|compiled| {
                    Predicate {
                        vars: predicate_vars(&compiled, width),
                        eval: compiled.eval,
                    }
                })
            })
            .collect::<Result<Vec<Predicate>, CompileError>>()?;
        let action_constraints = model
            .action_constraints
            .iter()
            .map(|constraint| {
                let index = named("action constraint", ir, constraint)?;
                compiler
                    .compile_root(Root::Definition(index))
                    .map(|compiled| compiled.eval)
            })
            .collect::<Result<Vec<Eval>, CompileError>>()?;
        let possible = model
            .possible
            .iter()
            .map(|possible| {
                let index = named("possible", ir, &possible.name)?;
                compiler
                    .compile_root(Root::Definition(index))
                    .map(|compiled| (compiled.eval, possible.is_action))
            })
            .collect::<Result<Vec<_>, CompileError>>()?;
        let init = compiler.compile_action(
            model.init,
            model.scope,
            ActionOptions {
                is_init: true,
                is_shortcut: true,
                can_print,
            },
            "a specification",
        )?;
        // Without a next-state relation TLC stops once it has the initial states, before the
        // temporal properties, the postconditions and the `_POSSIBLE` predicates it would check.
        if model.next.is_none()
            && (!compiler.is_native
                || model.is_recording_graph
                || !model.postconditions.is_empty()
                || !model.possible.is_empty())
        {
            return Err(CompileError::Decline(
                "a model without a next-state relation".into(),
            ));
        }
        let next = model
            .next
            .map(|next| {
                compiler.compile_action(
                    next,
                    model.scope,
                    ActionOptions {
                        is_init: false,
                        is_shortcut: model.is_warning_enabled,
                        can_print,
                    },
                    "a specification",
                )
            })
            .transpose()?;
        // Compiled whether or not the search walks them, since they also label a printed path.
        let actions = match Some(&model.actions).filter(|actions| !actions.is_empty()) {
            None => None,
            Some(actions) => {
                let mut steps = Vec::with_capacity(actions.len());
                for action in actions {
                    // Where one doesn't compile, the search walks the next-state relation
                    // unlabelled, and ENABLED runs.
                    match compiler.compile_action(
                        action.expression,
                        action.scope,
                        ActionOptions {
                            is_init: false,
                            is_shortcut: model.is_warning_enabled,
                            // A simulation takes its steps by the actions alone.
                            can_print: compiler.simulation.is_some(),
                        },
                        "an action",
                    ) {
                        Ok(step) => steps.push(step),
                        Err(_) => break,
                    }
                }
                (steps.len() == actions.len()).then_some(steps)
            }
        };
        // TLC's diameter grows as the search goes, which only the liveness checker's atoms follow.
        let is_diameter_searched = compiler.is_diameter_read;
        if is_diameter_searched && !compiler.is_native {
            return Err(CompileError::Bail(DIAMETER_SEARCHED.into()));
        }
        let compiled: Vec<CompiledAtom> = if model.is_recording_graph {
            model
                .atoms
                .iter()
                .map(|atom| compile_atom(compiler, ir, atom))
                .collect()
        } else {
            Vec::new()
        };
        let is_live_printing = compiled.iter().any(|atom| atom.is_printing);
        let is_live_registered = compiled.iter().any(|atom| atom.uses_registers);
        let diameter_atoms = compiled.iter().map(|atom| atom.reads_diameter).collect();
        let level_atoms = compiled
            .iter()
            .map(|atom| matches!(atom.atom, Atom::LevelState(_) | Atom::LevelAction { .. }))
            .collect();
        let atoms = compiled.into_iter().map(|atom| atom.atom).collect();
        let (initial_invariants, initial_invariant_owners) = invariants
            .iter()
            .zip(&invariant_conjuncts)
            .zip(&invariant_owners)
            .filter(|((_, conjunct), _)| !init_conjuncts.contains(conjunct))
            .map(|((compiled, _), &owner)| (compiled.eval.clone(), owner))
            .unzip();
        // Under a VIEW TLC fingerprints the view's value alone, so a set TLC keeps lazy that a
        // variable holds stays as the spec built it, in an order the store doesn't keep.
        if view.is_some() && compiler.is_lazy_set_held && compiler.is_held_set_enumerated {
            return Err(CompileError::Bail(
                "unsupported: enumerating a lazy set of the state under a VIEW".into(),
            ));
        }
        Ok(EngineContext {
            width,
            init,
            next,
            actions,
            invariants: invariants
                .into_iter()
                .map(|compiled| Predicate {
                    vars: predicate_vars(&compiled, width),
                    eval: compiled.eval,
                })
                .collect(),
            invariant_owners,
            initial_invariants,
            initial_invariant_owners,
            constraints,
            constraint_owners,
            action_constraints,
            possible,
            action_properties,
            is_diameter_searched,
            is_view_search_read,
            initial_predicates,
            view,
            atoms,
            is_live_printing,
            is_live_registered,
            diameter_atoms,
            level_atoms,
            is_invariant_printing,
            startup,
        })
    }
}

fn resolve(ir: &Ir, node: NodeId) -> &NodeKind {
    let mut id = node;
    loop {
        match &ir.nodes.arena[id as usize].kind {
            NodeKind::Reference(target) => id = *target,
            kind => return kind,
        }
    }
}

/// Why the engine doesn't search a model that reads TLC's diameter.
const UNCOMPILED_ASSUMPTION: &str = "unsupported: an assumption the engine doesn't compile";
pub const DIAMETER_SEARCHED: &str = "unsupported: TLCGet(\"diameter\") in the search";
pub const VIEW_SEARCH_READ: &str = "unsupported: TLCGet in a VIEW";

fn describe(error: CompileError) -> String {
    match error {
        CompileError::Bail(reason) | CompileError::Decline(reason) => reason,
    }
}

// An expression of an atom, compiled in the atom's scope. What TLCGet reads holds only while the
// search runs; what the atom prints the search prints in TLC's order.
fn compile_live(
    compiler: &mut Compiler<'_>,
    node: NodeId,
    scope: Option<Index>,
) -> Result<Compiled, String> {
    match compiler.compile_in_scope(node, scope) {
        Ok(Some(compiled)) if compiled.reads_distinct() => {
            Err("unsupported: TLCGet(\"distinct\") after the search".into())
        }
        // TLC evaluates the atoms as it adds each state to the behavior graphs, in an order
        // the registers would tell.
        Ok(Some(compiled)) if compiled.uses_registers() && !compiler.is_native => {
            Err("unsupported: TLC's registers in the liveness checker's atoms".into())
        }
        Ok(Some(compiled)) => Ok(compiled),
        Ok(None) => Err("a scope the engine can't translate".into()),
        Err(error) => Err(describe(error)),
    }
}

// A subscript the checker compares in each state of a step: a state function.
fn compile_subscript(
    compiler: &mut Compiler<'_>,
    node: NodeId,
    scope: Option<Index>,
) -> Result<Compiled, String> {
    let compiled = compile_live(compiler, node, scope)?;
    if !compiled.footprint.primes.is_empty() {
        return Err("unsupported: a subscript that reads a primed variable".into());
    }
    if compiled.reads_level() {
        return Err("unsupported: TLCGet(\"level\") in a subscript".into());
    }
    // TLC evaluates a subscript in both states of each step it checks, where the engine reads its
    // value once for each state.
    if compiled.is_printing() {
        return Err("unsupported: a subscript that prints".into());
    }
    Ok(compiled)
}

// An atom, compiled, with whether evaluating it may print and whether it reads TLCGet("diameter").
struct CompiledAtom {
    atom: Atom,
    is_printing: bool,
    reads_diameter: bool,
    uses_registers: bool,
}

// Whether an atom's action is the next-state relation, named as the specification names it in the
// same scope, and TLC evaluates it as a predicate as it walks it but for the comparisons of the
// primed variables.
fn is_next(compiler: &Compiler<'_>, ir: &Ir, atom: &tla_ir::Atom) -> bool {
    let Some(next) = ir.model.next else {
        return false;
    };
    let is_named = atom.expression == next
        || matches!(
            (resolve(ir, atom.expression), resolve(ir, next)),
            (NodeKind::Identifier(action), NodeKind::Identifier(relation))
                if !action.is_local
                    && matches!(action.resolution, Resolution::Definition(_))
                    && action.resolution == relation.resolution
        );
    is_named
        && atom.scope == ir.model.scope
        && compiler.is_walk_repeatable(next, &mut HashSet::new())
}

fn compile_atom(compiler: &mut Compiler<'_>, ir: &Ir, atom: &tla_ir::Atom) -> CompiledAtom {
    let scope = atom.scope;
    let mut is_printing = false;
    let mut reads_diameter = false;
    let mut uses_registers = false;
    let compiled = match &atom.kind {
        AtomKind::State => compile_live(compiler, atom.expression, scope).map(|compiled| {
            is_printing = compiled.is_printing();
            reads_diameter = compiled.reads_diameter();
            uses_registers = compiled.uses_registers();
            if compiled.reads_level() {
                Atom::LevelState(compiled.eval)
            } else {
                Atom::State(compiled.eval)
            }
        }),
        AtomKind::Action { unchanged, enabled } => (|| {
            let subscript = match unchanged {
                None => None,
                Some(node) => match resolve(ir, *node) {
                    NodeKind::Unchanged(inner) => Some(compile_subscript(compiler, *inner, scope)?),
                    _ => return Err("a subscript the engine doesn't read".to_string()),
                },
            };
            let action = compile_live(compiler, atom.expression, scope)?;
            is_printing = action.is_printing();
            reads_diameter =
                action.reads_diameter() || subscript.as_ref().is_some_and(Compiled::reads_diameter);
            uses_registers =
                action.uses_registers() || subscript.as_ref().is_some_and(Compiled::uses_registers);
            if action.reads_level() {
                return Ok(Atom::LevelAction {
                    action: action.eval,
                    subscript: subscript.map(|subscript| subscript.eval),
                });
            }
            Ok(Atom::Action {
                is_next: !action.reads_search() && is_next(compiler, ir, atom),
                action: action.eval,
                subscript: subscript.map(|subscript| subscript.eval),
                enabled: enabled.map(|position| position as usize),
            })
        })(),
        AtomKind::Enabled { actions } => {
            let run = match compiler.compile_enabled_in_scope(atom.expression, scope) {
                Ok(Some(compiled)) if compiled.reads_level() => {
                    Err("unsupported: TLCGet(\"level\") in ENABLED".to_string())
                }
                Ok(Some(compiled)) => {
                    is_printing = compiled.is_printing();
                    uses_registers = compiled.uses_registers();
                    Ok(compiled.eval)
                }
                Ok(None) => Err("a scope the engine can't translate".to_string()),
                Err(error) => Err(describe(error)),
            };
            let steps = match (resolve(ir, atom.expression), actions) {
                (_, EnabledActions::Unknown) => None,
                (NodeKind::AngleAction { subscript, .. }, actions) => {
                    // A subscript that reads TLC's diameter leaves ENABLED to its run, which
                    // doesn't read it.
                    compile_subscript(compiler, *subscript, scope)
                        .ok()
                        .filter(|subscript| !subscript.reads_diameter())
                        .map(|compiled| EnabledSteps {
                            subscript: compiled.eval,
                            key: get_subscript_key(ir, *subscript, scope),
                            actions: match actions {
                                EnabledActions::Some(positions) => {
                                    let length =
                                        positions.iter().max().map_or(0, |&last| last as usize + 1);
                                    let mut taken = vec![false; length];
                                    for &position in positions {
                                        taken[position as usize] = true;
                                    }
                                    Some(taken)
                                }
                                _ => None,
                            },
                        })
                }
                _ => None,
            };
            Ok(Atom::Enabled { run, steps })
        }
    };
    CompiledAtom {
        atom: compiled.unwrap_or_else(Atom::Unknown),
        is_printing,
        reads_diameter,
        uses_registers,
    }
}
