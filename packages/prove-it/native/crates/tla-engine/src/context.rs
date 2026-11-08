//! What a search needs of a model: the walks of the initial predicate and the next-state
//! relation, and the compiled invariants, constraints and properties, as `createEngineContext` in
//! `context.ts` builds them, in its order.

use std::collections::HashSet;

use tla_ir::{
    AtomKind, ConfigName, Definition, DefinitionForm, EnabledActions, Index, Ir, NodeId, NodeKind,
    Resolution, Startup,
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
    pub init: Step,
    pub next: Step,
    /// A walk of each of TLC's actions, which together take the steps of `next` in its order, or
    /// `None` when the engine can't build one.
    pub actions: Option<Vec<Step>>,
    pub invariants: Vec<Predicate>,
    /// The invariants an initial state may violate: the others are conjuncts of the initial
    /// predicate, so hold of every state it gives.
    pub initial_invariants: Vec<Eval>,
    pub constraints: Vec<Predicate>,
    pub action_constraints: Vec<Eval>,
    /// Each holds of a step unless the action and the subscript's UNCHANGED are both false.
    pub action_properties: Vec<(Eval, Eval)>,
    pub initial_predicates: Vec<Eval>,
    /// The value a VIEW maps the current state to, which the search tells states apart by.
    pub view: Option<Eval>,
    /// The liveness checker's atoms, compiled, when the search records its graph.
    pub atoms: Vec<Atom>,
}

/// How the engine answers a liveness atom on its states, or why it can't, in which case the
/// interpreter answers it (`createLiveOracle` in `live.ts`).
pub enum Atom {
    State(Eval),
    /// An action, false of a step that leaves the subscript unchanged.
    Action {
        action: Eval,
        subscript: Option<Eval>,
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
    /// The positions of TLC's actions A splits into, or `None` for all of them.
    pub actions: Option<Vec<bool>>,
}

/// Whether a compiled predicate holds, failing on a value that isn't a boolean.
pub fn holds(machine: &mut Machine<'_>, predicate: &Eval) -> Outcome<bool> {
    match predicate(machine)? {
        TRUE => Ok(true),
        FALSE => Ok(false),
        _ => Err(Bail("a predicate that isn't a boolean")),
    }
}

pub fn holds_all(machine: &mut Machine<'_>, predicates: &[Eval]) -> Outcome<bool> {
    for predicate in predicates {
        if !holds(machine, predicate)? {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Whether every predicate holds of the successor that is current, given that each held of its
/// parent: one that reads only variables the step left unchanged has the parent's value.
pub fn holds_all_changed(
    machine: &mut Machine<'_>,
    predicates: &[Predicate],
    successor: &[u32],
    parent: &[u32],
) -> Outcome<bool> {
    for predicate in predicates {
        if let Some(vars) = &predicate.vars
            && vars
                .iter()
                .all(|&variable| successor[variable as usize] == parent[variable as usize])
        {
            continue;
        }
        if !holds(machine, &predicate.eval)? {
            return Ok(false);
        }
    }
    Ok(true)
}

/// A conjunct the engine checks: a name the configuration gives, as an identifier of it, or an
/// expression of the model.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Conjunct {
    Named(Index),
    Node(NodeId),
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

    // The definition a conjunct asserts, a zero-arity operator with no startup value, as the
    // compiler resolves a name nothing binds locally.
    fn asserted(&self, conjunct: Conjunct) -> Option<Index> {
        let index = match conjunct {
            Conjunct::Named(index) => index,
            Conjunct::Node(node) => match self.resolve(node).1 {
                NodeKind::Identifier(name) if !name.is_local => match name.resolution {
                    Resolution::Definition(index) => index,
                    _ => return None,
                },
                _ => return None,
            },
        };
        let definition = self.definition(index);
        matches!(
            (&definition.form, &definition.startup),
            (DefinitionForm::Operator(params), Startup::None) if params.is_empty()
        )
        .then_some(index)
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
            named => named,
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
    compiler.compile_root_printing(
        match conjunct {
            Conjunct::Named(index) => Root::Definition(index),
            Conjunct::Node(node) => Root::Expression(node),
        },
        can_print,
    )
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
        // Each invariant and constraint is checked conjunct by conjunct, so a successor skips
        // each conjunct that reads only variables its step left unchanged. An invariant that may
        // print is checked whole each time, as TLC checks it, where the search may print.
        let can_print = !model.is_recording_graph;
        let mut conjuncts = Conjuncts::new(ir);
        let mut printed = HashSet::new();
        for invariant in &model.invariants {
            let root = Conjunct::Named(named("invariant", ir, &invariant.root)?);
            if invariant.has_repeated_effect && can_print {
                printed.insert(root);
                conjuncts.add(root);
            } else {
                conjuncts.collect(root);
            }
        }
        for invariant in &model.property_invariants {
            let root = Conjunct::Node(invariant.root);
            if invariant.has_repeated_effect && can_print {
                printed.insert(root);
                conjuncts.add(root);
            } else {
                conjuncts.collect(root);
            }
        }
        let invariant_conjuncts = conjuncts.found;
        let invariants = invariant_conjuncts
            .iter()
            .map(|&conjunct| compile_conjunct(compiler, conjunct, printed.contains(&conjunct)))
            .collect::<Result<Vec<Compiled>, CompileError>>()?;
        // An initial predicate in an instance's scope resolves its names there, so it implies
        // nothing.
        let init_conjuncts: HashSet<Conjunct> = if model.scope.is_none() {
            let mut found = Conjuncts::new(ir);
            found.collect(Conjunct::Node(model.init));
            found.found.into_iter().collect()
        } else {
            HashSet::new()
        };
        let mut action_properties = Vec::new();
        for property in &model.action_properties {
            let action = compiler.compile_root(Root::Expression(property.action))?;
            let unchanged = compiler.compile_root(Root::Unchanged(property.subscript))?;
            action_properties.push((action.eval, unchanged.eval));
        }
        let initial_predicates = model
            .initial_predicates
            .iter()
            .map(|&predicate| {
                compiler
                    .compile_root(Root::Expression(predicate))
                    .map(|compiled| compiled.eval)
            })
            .collect::<Result<Vec<Eval>, CompileError>>()?;
        let view = match &model.view {
            Some(view) => {
                let compiled = compiler.compile_root(Root::Definition(named("view", ir, view)?))?;
                if compiled.reads_search() {
                    return Err(CompileError::Bail("unsupported: TLCGet in a VIEW".into()));
                }
                Some(compiled.eval)
            }
            None => None,
        };
        let mut constraint_roots = Vec::new();
        for constraint in &model.constraints {
            constraint_roots.push(Conjunct::Named(named("constraint", ir, constraint)?));
        }
        let mut conjuncts = Conjuncts::new(ir);
        for root in constraint_roots {
            conjuncts.collect(root);
        }
        let constraints = conjuncts
            .found
            .into_iter()
            .map(|conjunct| {
                compile_conjunct(compiler, conjunct, false).map(|compiled| Predicate {
                    vars: predicate_vars(&compiled, width),
                    eval: compiled.eval,
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
        let next = compiler.compile_action(
            model.next,
            model.scope,
            ActionOptions {
                is_init: false,
                is_shortcut: model.is_warning_enabled,
                can_print,
            },
            "a specification",
        )?;
        let actions = match &model.actions {
            None => None,
            Some(actions) => {
                let mut steps = Vec::with_capacity(actions.len());
                for action in actions {
                    match compiler.compile_action(
                        action.expression,
                        action.scope,
                        ActionOptions {
                            is_init: false,
                            is_shortcut: model.is_warning_enabled,
                            can_print: false,
                        },
                        "an action",
                    ) {
                        Ok(step) => steps.push(step),
                        Err(CompileError::Bail(_)) => break,
                        Err(decline) => return Err(decline),
                    }
                }
                (steps.len() == actions.len()).then_some(steps)
            }
        };
        let atoms = if model.is_recording_graph {
            model
                .atoms
                .iter()
                .map(|atom| compile_atom(compiler, ir, atom))
                .collect()
        } else {
            Vec::new()
        };
        let initial_invariants = invariants
            .iter()
            .zip(&invariant_conjuncts)
            .filter(|(_, conjunct)| !init_conjuncts.contains(conjunct))
            .map(|(compiled, _)| compiled.eval.clone())
            .collect();
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
            initial_invariants,
            constraints,
            action_constraints,
            action_properties,
            initial_predicates,
            view,
            atoms,
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

fn describe(error: CompileError) -> String {
    match error {
        CompileError::Bail(reason) | CompileError::Decline(reason) => reason,
    }
}

// An expression of an atom, compiled in the atom's scope. What TLCGet reads holds only while the
// search runs.
fn compile_live(
    compiler: &mut Compiler<'_>,
    node: NodeId,
    scope: Option<Index>,
) -> Result<Compiled, String> {
    match compiler.compile_in_scope(node, scope) {
        Ok(Some(compiled)) if compiled.reads_search() => {
            Err("unsupported: TLCGet after the search".into())
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
) -> Result<Eval, String> {
    let compiled = compile_live(compiler, node, scope)?;
    if !compiled.footprint.primes.is_empty() {
        return Err("unsupported: a subscript that reads a primed variable".into());
    }
    Ok(compiled.eval)
}

fn compile_atom(compiler: &mut Compiler<'_>, ir: &Ir, atom: &tla_ir::Atom) -> Atom {
    let scope = atom.scope;
    let compiled = match &atom.kind {
        AtomKind::State => compile_live(compiler, atom.expression, scope)
            .map(|compiled| Atom::State(compiled.eval)),
        AtomKind::Action { unchanged } => (|| {
            let subscript = match unchanged {
                None => None,
                Some(node) => match resolve(ir, *node) {
                    NodeKind::Unchanged(inner) => Some(compile_subscript(compiler, *inner, scope)?),
                    _ => return Err("a subscript the engine doesn't read".to_string()),
                },
            };
            let action = compile_live(compiler, atom.expression, scope)?.eval;
            Ok(Atom::Action { action, subscript })
        })(),
        AtomKind::Enabled { actions } => {
            let run = match compiler.compile_enabled_in_scope(atom.expression, scope) {
                Ok(Some(compiled)) => Ok(compiled.eval),
                Ok(None) => Err("a scope the engine can't translate".to_string()),
                Err(error) => Err(describe(error)),
            };
            let steps = match (resolve(ir, atom.expression), actions) {
                (_, EnabledActions::Unknown) => None,
                (NodeKind::AngleAction { subscript, .. }, actions) => {
                    compile_subscript(compiler, *subscript, scope)
                        .ok()
                        .map(|subscript| EnabledSteps {
                            subscript,
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
    compiled.unwrap_or_else(Atom::Unknown)
}
