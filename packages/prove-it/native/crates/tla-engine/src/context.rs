//! What a search needs of a model: the walks of the initial predicate and the next-state
//! relation, and the compiled invariants, constraints and properties, as `createEngineContext` in
//! `context.ts` builds them, in its order.

use std::collections::HashSet;
use std::sync::Arc;

use tla_ir::{
    AtomKind, ConfigName, Definition, DefinitionForm, EnabledActions, Index, Ir, NodeId, NodeKind,
    Pattern, PredicateForm, Resolution, ScopeBinding, TextId,
};
use tla_values::Bail;
use tla_values::store::{FALSE, Outcome, TRUE};

use crate::compile::{ActionOptions, CompileError, Compiled, Compiler, Root, SymmetryElements};
use crate::machine::{Eval, Machine, Step, UNASSIGNED};

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
    /// How many bytes of bits each step keeps for the action atoms made of pieces of Next, none
    /// where no atom is.
    pub piece_width: usize,
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
    /// Whether an action property may print, which the search prints among Next's prints.
    pub is_action_property_printing: bool,
    /// What TLC evaluates when it starts.
    pub startup: Startup,
    /// The constant definitions whose body is a CHOOSE over a set, as the compiler found them
    /// once it compiled the rest (`Compiler::get_constant_choices`).
    pub choices: Vec<(Index, Eval)>,
}

/// What TLC evaluates when it starts, compiled: each substitute, then each constant definition
/// with effects, then the symmetry, then each assumption, with the name TLC reports it by.
pub struct Startup {
    pub substitutes: Vec<Eval>,
    /// The substitutes of constant level that may recurse, which the engine evaluates only to
    /// find one too deep for it (`Startup::recursive_substitutes` of the IR's).
    pub recursive_substitutes: Vec<Eval>,
    /// Each startup definition and the conditions under which a startup failure can be retried.
    pub definitions: Vec<StartupDefinition>,
    /// The constant definitions without effects of their own TLC computes as it starts that name
    /// a startup definition (`tla_ir::Startup::dependents`).
    pub dependents: Vec<StartupDependent>,
    /// The constant definitions that reach TLCSet the engine computes as TLC does as it starts,
    /// to find whether TLC fails or completes there before any effect
    /// (`tla_ir::Startup::register_probes`), each compiled, or why the engine can't.
    pub register_probes: Vec<Result<Eval, String>>,
    /// Whether the one register probe is read once, by the first assumption, after a startup
    /// with no other effect (`tla_ir::Startup::is_probe_assumed_once`).
    pub is_probe_assumed_once: bool,
    /// The constant definitions the configuration names, with how TLC rejects each one's value
    /// and the configuration error's words for it, and the position among `definitions` of the
    /// startup definition it names, if it is one, the definition it names among the IR's, and
    /// whether TLC takes it for a state's (`tla_ir::StartupPredicate::is_state_level`).
    #[allow(clippy::type_complexity)]
    pub predicates: Vec<(
        Eval,
        PredicateForm,
        String,
        String,
        Option<usize>,
        Index,
        bool,
    )>,
    pub symmetry: Option<StartupSymmetry>,
    /// The exception `Tool.getActions` throws as TLC builds its `Tool`, after the symmetry, on a
    /// literal it reaches as an action (`get_next_literal`), as TLC reports it after
    /// `UNEXPECTED_HEAD`.
    pub next_failure: Option<String>,
    /// Whether `Tool.getActions` reaches a variable or a constant as it builds its `Tool`, after
    /// the symmetry, where it fails casting its declaration to a definition
    /// (`reaches_next_declaration`), which the engine declines.
    pub is_next_declaration: bool,
    /// Whether `Tool.getActions` takes an operator's application with arguments whole, where it
    /// catches the cast of a variable or a constant in its body (`reaches_application_cast`),
    /// which the engine declines.
    pub is_next_application_cast: bool,
    pub assumptions: Vec<(Eval, String)>,
}

/// A constant definition TLC computes at startup and may evaluate again where it is used.
pub struct StartupDefinition {
    pub evaluate: Eval,
    pub is_retried: bool,
    pub is_direct_infinite_operation: bool,
    pub has_failing_set_print: bool,
    pub is_warning_only: bool,
    /// A PrintT of an expression without effects (`Compiler::is_pure_print`).
    pub is_pure_print: bool,
    /// Whether another constant definition TLC computes as it starts, one the engine computes
    /// only where it is used, names it (`Compiler::is_named_at_startup`).
    pub is_named_at_startup: bool,
    /// The machine's slot its value is kept in (`Compiler::startup_once`).
    pub once: Option<usize>,
    /// A recursive function TLC keeps lazy, of which the search keeps no value though it doesn't
    /// fail (`Compiler::compile_kept_lazy_startup`).
    pub is_kept_lazy: bool,
    /// Why the engine doesn't compile one only the first assumption reads, whose effects as TLC
    /// computes it the reporter's evaluator gives (`is_left_to_reporter`).
    pub left: Option<String>,
}

/// A constant definition without effects of its own that TLC computes as it starts, and that
/// names startup definitions: where one of those failed, TLC swallowed it and evaluates it again
/// inside this one, with its effects, which the engine has where TLC computes this one.
pub struct StartupDependent {
    /// How many of the startup definitions TLC computes before it.
    pub position: usize,
    /// The startup definitions it names, by position.
    pub named: Vec<usize>,
    /// The definition compiled as TLC computes it, or why the engine can't.
    pub evaluate: Result<Eval, String>,
    /// The definition, among the IR's.
    pub index: Index,
    /// Whether it is one of the startup definitions, which TLC looks up again for a later module
    /// whose context holds it from a module it extends or an INSTANCE without parameters.
    pub is_repeat: bool,
}

/// The SYMMETRY definition's body, and each set it permutes: the name TLC's warning gives it, and
/// the set TLC checks for a model value the group moves.
pub struct StartupSymmetry {
    pub definition: Eval,
    pub permuted_sets: Vec<(String, Option<Eval>)>,
    /// The exception `Tool.getSymmetryPerms` throws on a body whose value's class the engine
    /// knows, a number or a string, which isn't a set: its class and message, as TLC reports them
    /// after `UNEXPECTED_HEAD`.
    pub failure: Option<&'static str>,
    /// How TLC holds the elements of the body's value, which it requires to be function records.
    pub elements: SymmetryElements,
    /// Whether TLC holds the body's value as a `SetEnumValue`, as `getSymmetryPerms` requires.
    pub is_enumerated: bool,
}

// What `Tool.getActions` meets in the next-state relation, as far as the engine follows it.
enum NextAction {
    // A literal, by its text (`NumeralNode.toString`), on which TLC fails.
    Literal(String),
    // An action TLC takes whole without evaluating anything.
    Whole,
    // Something TLC may evaluate, print or fail in, or a literal whose text the IR doesn't hold.
    Unknown,
}

// The literal `Tool.getActions` fails on as TLC builds its `Tool`, where it reaches one before
// it evaluates anything. TLC takes the body of the definition the configuration's NEXT names
// (`SpecProcessor.processConfigSpec`) and goes through a LET's body, a label's and each disjunct
// in turn; an operator's application or an \E it evaluates the arguments or the bounds of, and
// swallows what fails in it (`getActionsAppl`), and any other expression is an action of its own.
// A SPECIFICATION's next-state relation is the application of the operator it names, which TLC
// takes whole where its body fails so.
fn get_next_literal(ir: &Ir) -> Option<String> {
    let model = &ir.model;
    if model.specification.is_some() || model.next_substitution.is_some() {
        return None;
    }
    let NodeKind::Identifier(name) = &ir.nodes.arena[model.next? as usize].kind else {
        return None;
    };
    let Resolution::Definition(index) = name.resolution else {
        return None;
    };
    if name.is_local {
        return None;
    }
    let NodeKind::Definition(definition) =
        &ir.nodes.arena[ir.definitions[index as usize] as usize].kind
    else {
        return None;
    };
    if !matches!(&definition.form, DefinitionForm::Operator(params) if params.is_empty()) {
        return None;
    }
    match next_action(ir, definition.body) {
        NextAction::Literal(image) => Some(image),
        NextAction::Whole | NextAction::Unknown => None,
    }
}

/// Why the engine declines a next-state relation `Tool.getActions` fails on with a
/// ClassCastException.
pub const NEXT_DECLARATION: &str = "a variable or a constant TLC's splitting of the next-state relation reaches, which it fails to cast to a definition as it starts";

// Whether `Tool.getActions` reaches a variable or a constant on its way through the body of the
// definition the configuration's NEXT names, or through the action of a SPECIFICATION's
// `[][A]_v`, where `getActionsAppl` looks the name up to its declaration or to the constant's
// value, neither a definition, and casts the declaration to `OpDefNode`: a ClassCastException
// TLC doesn't catch, so it fails as it starts. TLC goes through a LET's body, a label's and each
// disjunct in turn, failing first on a literal before it; inside an operator's application or an
// \E it catches the failure and takes the whole as one action.
fn reaches_next_declaration(ir: &Ir) -> bool {
    let model = &ir.model;
    if model.next_substitution.is_some() {
        return false;
    }
    let Some(next) = model.next else {
        return false;
    };
    // A SPECIFICATION's `[][A]_v`: TLC splits `A` itself, which as an operator's application it
    // takes whole where its body fails so.
    if model.specification.is_some() {
        return next_declaration(ir, next) == Some(true);
    }
    let NodeKind::Identifier(name) = &ir.nodes.arena[next as usize].kind else {
        return false;
    };
    let Resolution::Definition(index) = name.resolution else {
        return false;
    };
    if name.is_local {
        return false;
    }
    let NodeKind::Definition(definition) =
        &ir.nodes.arena[ir.definitions[index as usize] as usize].kind
    else {
        return false;
    };
    if !matches!(&definition.form, DefinitionForm::Operator(params) if params.is_empty()) {
        return false;
    }
    next_declaration(ir, definition.body) == Some(true)
}

/// Why the engine declines a next-state relation `Tool.getActions` splits into an operator's
/// application with arguments whose body reaches a variable or a constant.
pub const NEXT_APPLICATION_CAST: &str = "a variable, a constant or a parameter TLC's splitting of the next-state relation fails to cast to a definition inside an operator's application, a LET's definition or an \\E, which it then takes whole as one action";

// Whether `Tool.getActions`, going through the body of the definition the configuration's NEXT
// names (or a SPECIFICATION's `[][A]_v`) as `reaches_next_declaration` does, fails casting a
// declaration to `OpDefNode` inside what catches that failure: `getActionsAppl` casts the
// operator of a name it doesn't look up to a definition, as of a variable, a constant, a formal
// parameter or a bound name, and the ClassCastException is caught by the innermost operator's
// application whose definition it walks (with arguments of constant level, a LET's definition,
// or a definition without parameters TLC didn't compute as it started), which it then takes
// whole as one action after the actions it split of it before, or by an \E, which takes the
// whole \E as one action in place of those. The engine names and counts those otherwise, but
// for the cast of a name whose value is FALSE before any action of the application: the whole
// application adds no step to the engine's.
fn reaches_application_cast(ir: &Ir) -> bool {
    let model = &ir.model;
    if model.next_substitution.is_some() {
        return false;
    }
    let Some(next) = model.next else {
        return false;
    };
    let body = if model.specification.is_some() {
        next
    } else {
        let NodeKind::Identifier(name) = &ir.nodes.arena[next as usize].kind else {
            return false;
        };
        let Resolution::Definition(index) = name.resolution else {
            return false;
        };
        if name.is_local {
            return false;
        }
        let NodeKind::Definition(definition) =
            &ir.nodes.arena[ir.definitions[index as usize] as usize].kind
        else {
            return false;
        };
        definition.body
    };
    matches!(
        application_cast(ir, body, false, &[], &mut false, 0),
        Err(Stop::Declined)
    )
}

// A local name the walk of `reaches_application_cast` binds.
#[derive(Clone, Copy)]
enum Local {
    // A name of a tuple an \E binds, or a function a LET defines, which TLC looks up to a value.
    Bound(TextId),
    // A formal parameter of the operator whose application the walk went into, with whether its
    // argument is FALSE, or a name an \E binds, with whether its set holds FALSE alone.
    Param {
        name: TextId,
        is_false: bool,
    },
    // A LET's definition, which `getActionsAppl` looks up to its `OpDefNode` and walks, with
    // whether it may be of more than constant level.
    Let {
        name: TextId,
        definition: NodeId,
        is_state: bool,
    },
}

impl Local {
    fn name(&self) -> TextId {
        match *self {
            Local::Bound(name) | Local::Param { name, .. } | Local::Let { name, .. } => name,
        }
    }
}

// Where the walk of `reaches_application_cast` stops: at a cast, which the innermost catch
// takes (`is_excused` where the engine follows that), or at one the engine declines.
enum Stop {
    Cast { is_excused: bool },
    Declined,
}

// `reaches_application_cast` of an expression, `in_catcher` inside what catches the failure,
// with the local names a LET, an \E or an application of the walk binds; `added` says whether
// the walk added an action inside the innermost catch so far.
fn application_cast(
    ir: &Ir,
    node: NodeId,
    in_catcher: bool,
    locals: &[Local],
    added: &mut bool,
    depth: u32,
) -> Result<(), Stop> {
    if depth > 64 {
        return Err(Stop::Declined);
    }
    // What the walk takes as one action: `getActions`' default.
    let leaf = |added: &mut bool| {
        *added = true;
        Ok(())
    };
    // The cast of a name, which a catch takes; outside any, TLC fails as it starts
    // (`reaches_next_declaration`).
    let cast = |is_false: bool, added: &mut bool| {
        if in_catcher {
            Err(Stop::Cast {
                is_excused: is_false && !*added,
            })
        } else {
            *added = true;
            Ok(())
        }
    };
    // The walk of a body inside the catch of an application or a definition, which adds an
    // action however it ends.
    let caught = |body: NodeId, locals: &[Local], added: &mut bool| {
        match application_cast(ir, body, true, locals, &mut false, depth + 1) {
            Ok(()) | Err(Stop::Cast { is_excused: true }) => {}
            Err(_) => return Err(Stop::Declined),
        }
        *added = true;
        Ok(())
    };
    match &ir.nodes.arena[node as usize].kind {
        NodeKind::Reference(target) => {
            application_cast(ir, *target, in_catcher, locals, added, depth + 1)
        }
        NodeKind::Label { body, .. } => {
            application_cast(ir, *body, in_catcher, locals, added, depth + 1)
        }
        NodeKind::Let {
            definitions, body, ..
        } => {
            let mut inner = locals.to_vec();
            for &definition in definitions {
                if let NodeKind::Definition(written) = &ir.nodes.arena[definition as usize].kind {
                    inner.push(match &written.form {
                        DefinitionForm::Operator(_) => Local::Let {
                            name: written.name,
                            definition,
                            is_state: mentions_state(ir, written.body, &inner, &mut HashSet::new()),
                        },
                        DefinitionForm::Function(_) => Local::Bound(written.name),
                    });
                }
            }
            application_cast(ir, *body, in_catcher, &inner, added, depth + 1)
        }
        // `getActions` binds each bound of an \E to its values and splits the body, catching
        // any failure there, which takes the whole \E in place of what it split.
        NodeKind::Exists { bounds, body } => {
            let mut inner = locals.to_vec();
            for bound in bounds {
                match &bound.pattern {
                    // A name bound to FALSE alone, as a parameter whose argument is FALSE.
                    Pattern::Name(name) => inner.push(Local::Param {
                        name: *name,
                        is_false: matches!(&ir.nodes.arena[bound.set as usize].kind,
                            NodeKind::SetEnumeration(elements)
                                if !elements.is_empty()
                                    && elements
                                        .iter()
                                        .all(|&element| is_false_argument(ir, element, &inner))),
                    }),
                    Pattern::Tuple(names) => {
                        inner.extend(names.iter().map(|&name| Local::Bound(name)))
                    }
                }
            }
            match application_cast(ir, *body, true, &inner, &mut false, depth + 1) {
                Ok(()) | Err(Stop::Cast { is_excused: true }) => {
                    *added = true;
                    Ok(())
                }
                Err(_) => Err(Stop::Declined),
            }
        }
        NodeKind::Or(operands) => {
            for &operand in operands {
                application_cast(ir, operand, in_catcher, locals, added, depth + 1)?;
            }
            Ok(())
        }
        // Action composition, which the front end names as a core symbol without a definition:
        // `getActions` takes it whole as one action, which TLC fails on as it evaluates it.
        NodeKind::Apply { name, .. }
            if name.is_local
                && matches!(name.resolution, Resolution::None)
                && &*ir.texts[name.text as usize] == "\\cdot" =>
        {
            leaf(added)
        }
        // A local name: a LET's definition is walked inside its own catch; a bound name or a
        // formal parameter is cast.
        NodeKind::Identifier(name) | NodeKind::Apply { name, .. } if name.is_local => {
            match locals.iter().rev().find(|local| local.name() == name.text) {
                Some(&Local::Let { definition, .. }) => {
                    let NodeKind::Definition(written) = &ir.nodes.arena[definition as usize].kind
                    else {
                        return Err(Stop::Declined);
                    };
                    let args: &[NodeId] = match &ir.nodes.arena[node as usize].kind {
                        NodeKind::Apply { args, .. } => args,
                        _ => &[],
                    };
                    if args
                        .iter()
                        .any(|&arg| mentions_state(ir, arg, locals, &mut HashSet::new()))
                    {
                        return leaf(added);
                    }
                    let mut inner = locals.to_vec();
                    if let DefinitionForm::Operator(params) = &written.form {
                        inner.extend(params.iter().zip(args).map(|(param, &arg)| Local::Param {
                            name: param.name,
                            is_false: is_false_argument(ir, arg, locals),
                        }));
                    }
                    caught(written.body, &inner, added)
                }
                Some(&Local::Param { is_false, .. }) => cast(is_false, added),
                _ => cast(false, added),
            }
        }
        NodeKind::Identifier(name) => match name.resolution {
            Resolution::Variable(_) => cast(false, added),
            Resolution::Constant(index) => cast(
                ir.constants.get(index as usize).is_some_and(|constant| {
                    constant.value.is_some_and(|value| {
                        ir.values.list.get(value as usize) == Some(&tla_ir::Value::Bool(false))
                    })
                }),
                added,
            ),
            Resolution::Definition(index) => {
                match &ir.nodes.arena[ir.definitions[index as usize] as usize].kind {
                    NodeKind::Definition(definition)
                        if matches!(&definition.form,
                        DefinitionForm::Operator(params) if params.is_empty()) =>
                    {
                        // TLC computes one of constant level as it starts and looks the name
                        // up to that value, which it takes whole as one action, where that
                        // doesn't fail (`processConstantDefns`).
                        if !mentions_state(ir, definition.body, &[], &mut HashSet::new())
                            && startup_value(ir, definition.body, 0) != Computed::Unknown
                        {
                            return leaf(added);
                        }
                        caught(definition.body, &[], added)
                    }
                    _ => leaf(added),
                }
            }
            _ => leaf(added),
        },
        // `getActionsAppl` goes into the body only where every argument is of constant level.
        NodeKind::Apply { name, args }
            if !args.is_empty()
                && !args
                    .iter()
                    .any(|&arg| mentions_state(ir, arg, locals, &mut HashSet::new())) =>
        {
            match name.resolution {
                Resolution::Definition(index) => {
                    match &ir.nodes.arena[ir.definitions[index as usize] as usize].kind {
                        NodeKind::Definition(definition) => match &definition.form {
                            DefinitionForm::Operator(params) => {
                                let inner: Vec<Local> = params
                                    .iter()
                                    .zip(args)
                                    .map(|(param, &arg)| Local::Param {
                                        name: param.name,
                                        is_false: is_false_argument(ir, arg, locals),
                                    })
                                    .collect();
                                caught(definition.body, &inner, added)
                            }
                            DefinitionForm::Function(_) => leaf(added),
                        },
                        _ => leaf(added),
                    }
                }
                _ => leaf(added),
            }
        }
        _ => leaf(added),
    }
}

// Whether an argument is FALSE: the literal, a constant the configuration sets so, a definition
// TLC computes so as it starts, or a parameter bound to FALSE.
fn is_false_argument(ir: &Ir, node: NodeId, locals: &[Local]) -> bool {
    match &ir.nodes.arena[node as usize].kind {
        NodeKind::Identifier(name) if name.is_local => locals
            .iter()
            .rev()
            .find(|local| local.name() == name.text)
            .is_some_and(|local| matches!(local, Local::Param { is_false: true, .. })),
        _ => startup_value(ir, node, 0) == Computed::Bool(false),
    }
}

// What TLC's evaluation of a constant expression as it starts gives, as far as the walk of
// `reaches_application_cast` follows it: a boolean, another value, or what it doesn't follow,
// which may fail.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Computed {
    Bool(bool),
    Other,
    Unknown,
}

// `Computed` of an expression of literals, constants the configuration sets, definitions without
// parameters of those, and the junctions and negations of booleans, which `Tool.eval` evaluates
// in order, a junction ending at the first operand that decides it.
fn startup_value(ir: &Ir, node: NodeId, depth: u32) -> Computed {
    if depth > 32 {
        return Computed::Unknown;
    }
    let junction = |operands: &[NodeId], is_or: bool| {
        for &operand in operands {
            match startup_value(ir, operand, depth + 1) {
                Computed::Bool(value) if value == is_or => return Computed::Bool(is_or),
                Computed::Bool(_) => {}
                _ => return Computed::Unknown,
            }
        }
        Computed::Bool(!is_or)
    };
    let builtin = |index: Index| &*ir.texts[ir.builtins[index as usize].name as usize];
    match &ir.nodes.arena[node as usize].kind {
        NodeKind::Reference(target) => startup_value(ir, *target, depth + 1),
        NodeKind::Label { body, .. } => startup_value(ir, *body, depth + 1),
        NodeKind::Number(_) | NodeKind::String(_) => Computed::Other,
        // `LET q == e IN q`.
        NodeKind::Let {
            definitions, body, ..
        } => match &ir.nodes.arena[*body as usize].kind {
            NodeKind::Identifier(name) if name.is_local => definitions
                .iter()
                .find_map(
                    |&definition| match &ir.nodes.arena[definition as usize].kind {
                        NodeKind::Definition(written)
                            if written.name == name.text
                                && matches!(&written.form,
                                DefinitionForm::Operator(params) if params.is_empty()) =>
                        {
                            Some(startup_value(ir, written.body, depth + 1))
                        }
                        _ => None,
                    },
                )
                .unwrap_or(Computed::Unknown),
            _ => Computed::Unknown,
        },
        NodeKind::Or(operands) => junction(operands, true),
        NodeKind::And(operands) => junction(operands, false),
        NodeKind::Identifier(name) if !name.is_local => match name.resolution {
            Resolution::Builtin(index) => match builtin(index) {
                "TRUE" => Computed::Bool(true),
                "FALSE" => Computed::Bool(false),
                _ => Computed::Unknown,
            },
            Resolution::Constant(index) => {
                match ir
                    .constants
                    .get(index as usize)
                    .and_then(|constant| constant.value)
                    .and_then(|value| ir.values.list.get(value as usize))
                {
                    Some(tla_ir::Value::Bool(value)) => Computed::Bool(*value),
                    Some(_) => Computed::Other,
                    None => Computed::Unknown,
                }
            }
            Resolution::Definition(index) => {
                match &ir.nodes.arena[ir.definitions[index as usize] as usize].kind {
                    NodeKind::Definition(definition)
                        if matches!(&definition.form,
                            DefinitionForm::Operator(params) if params.is_empty()) =>
                    {
                        startup_value(ir, definition.body, depth + 1)
                    }
                    _ => Computed::Unknown,
                }
            }
            _ => Computed::Unknown,
        },
        NodeKind::Apply { name, args } if !name.is_local && args.len() == 1 => {
            match name.resolution {
                Resolution::Builtin(index) if builtin(index) == "~" => {
                    match startup_value(ir, args[0], depth + 1) {
                        Computed::Bool(value) => Computed::Bool(!value),
                        _ => Computed::Unknown,
                    }
                }
                _ => Computed::Unknown,
            }
        }
        _ => Computed::Unknown,
    }
}

// Whether an expression may be of more than constant level, as SANY levels it: a variable, a
// prime, UNCHANGED or ENABLED in it or in a definition it names, a LET's definition `locals`
// holds of more than constant level, or a subexpression the walk doesn't follow. A formal
// parameter or a bound name is of constant level (`FormalParamNode`).
fn mentions_state(ir: &Ir, node: NodeId, locals: &[Local], seen: &mut HashSet<NodeId>) -> bool {
    if !seen.insert(node) {
        return false;
    }
    let kind = &ir.nodes.arena[node as usize].kind;
    let named = match kind {
        NodeKind::Prime(_)
        | NodeKind::Unchanged(_)
        | NodeKind::Enabled(_)
        | NodeKind::Subexpression(_) => true,
        NodeKind::Identifier(name) | NodeKind::Apply { name, .. } if name.is_local => locals
            .iter()
            .rev()
            .find(|local| local.name() == name.text)
            .is_some_and(|local| matches!(local, Local::Let { is_state: true, .. })),
        NodeKind::Identifier(name)
        | NodeKind::Apply { name, .. }
        | NodeKind::OperatorReference(name) => match name.resolution {
            Resolution::Variable(_) => true,
            Resolution::Definition(index) => {
                mentions_state(ir, ir.definitions[index as usize], &[], seen)
            }
            _ => false,
        },
        NodeKind::Definition(definition) => mentions_state(ir, definition.body, &[], seen),
        _ => false,
    };
    named
        || kind
            .children()
            .into_iter()
            .any(|child| mentions_state(ir, child, locals, seen))
}

// What `Tool.getActions` meets first of a variable or a constant (`Some(true)`) and a literal it
// fails on with its own error (`Some(false)`), taking the disjuncts in order.
fn next_declaration(ir: &Ir, node: NodeId) -> Option<bool> {
    match &ir.nodes.arena[node as usize].kind {
        NodeKind::Reference(target) => next_declaration(ir, *target),
        NodeKind::Let { body, .. } | NodeKind::Label { body, .. } => next_declaration(ir, *body),
        NodeKind::Or(operands) => operands
            .iter()
            .find_map(|&operand| next_declaration(ir, operand)),
        NodeKind::Number(_)
        | NodeKind::WideNumber(_)
        | NodeKind::Decimal(_)
        | NodeKind::String(_) => Some(false),
        NodeKind::Identifier(name)
            if !name.is_local
                && matches!(
                    name.resolution,
                    Resolution::Variable(_) | Resolution::Constant(_)
                ) =>
        {
            Some(true)
        }
        _ => None,
    }
}

fn next_action(ir: &Ir, node: NodeId) -> NextAction {
    let entry = &ir.nodes.arena[node as usize];
    match &entry.kind {
        NodeKind::Reference(target) => next_action(ir, *target),
        NodeKind::Let { body, .. } | NodeKind::Label { body, .. } => next_action(ir, *body),
        NodeKind::Or(operands) => {
            for &operand in operands {
                match next_action(ir, operand) {
                    NextAction::Whole => {}
                    action => return action,
                }
            }
            NextAction::Whole
        }
        // A numeral's text is as written: the IR holds its value, which prints as written where
        // it has as many digits, below 1000 (`\h`, `\o` and `\b` numerals that short are longer).
        NodeKind::Number(value) => match entry.range {
            Some(range)
                if (0..1000).contains(value)
                    && range.start_line == range.end_line
                    && (range.end_column - range.start_column + 1) as usize
                        == value.to_string().len() =>
            {
                NextAction::Literal(value.to_string())
            }
            _ => NextAction::Unknown,
        },
        NodeKind::And(_)
        | NodeKind::Prime(_)
        | NodeKind::Unchanged(_)
        | NodeKind::If { .. }
        | NodeKind::Case { .. }
        | NodeKind::Forall { .. } => NextAction::Whole,
        NodeKind::Apply { name, .. }
            if !name.is_local
                && matches!(name.resolution, Resolution::Builtin(index)
                    if matches!(&*ir.texts[ir.builtins[index as usize].name as usize],
                        "=" | "#" | "/=" | "\\in" | "\\notin")) =>
        {
            NextAction::Whole
        }
        _ => NextAction::Unknown,
    }
}

/// `getSymmetryPerms`'s failure on a value that isn't a set enumeration.
pub const NOT_A_SET_OF_FUNCTIONS: &str =
    "java.lang.RuntimeException\n: The symmetry operator must specify a set of functions.";
/// `getSymmetryPerms`'s failure on an element that isn't a `FcnRcdValue`.
pub const NOT_FUNCTION_RECORDS: &str =
    "java.lang.RuntimeException\n: The symmetry values must be function records.";
/// `MVPerms.permutationSubgroup`'s failure on a function that maps a value that isn't a model
/// value, or to one.
pub const NOT_MODEL_VALUES: &str =
    "java.lang.RuntimeException\n: Symmetry function must have model values as domain and range.";
/// What `MVPerms.permutationSubgroup` throws where it sizes its set of permutations one below
/// the number of them, for fewer than two (`util.Set`'s capacity must be positive): an exception
/// without a message, whose report holds its stack trace, from `TLC.process` building the model
/// checker's tool (`TLCStateMut.setTool`).
pub const FEW_PERMUTATIONS: &str = concat!(
    "java.lang.IllegalArgumentException\njava.lang.IllegalArgumentException\n",
    "\tat util.Set.<init>(Set.java:89)\n",
    "\tat util.Set.<init>(Set.java:103)\n",
    "\tat tlc2.value.impl.MVPerms.permutationSubgroup(MVPerms.java:21)\n",
    "\tat tlc2.tool.impl.Tool.getSymmetryPerms(Tool.java:3877)\n",
    "\tat tlc2.tool.TLCStateMut.setTool(TLCStateMut.java:77)\n",
    "\tat tlc2.tool.impl.Tool.<init>(Tool.java:222)\n",
    "\tat tlc2.tool.impl.Tool.<init>(Tool.java:202)\n",
    "\tat tlc2.tool.impl.Tool.<init>(Tool.java:187)\n",
    "\tat tlc2.tool.impl.FastTool.<init>(FastTool.java:62)\n",
    "\tat tlc2.TLC.process(TLC.java:1400)\n",
    "\tat tlc2.TLC.main(TLC.java:364)\n",
);

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
        /// What the subscript's value depends on besides the state: the atoms whose subscripts
        /// have the same key share its values on the helpers.
        key: Option<SubscriptKey>,
        enabled: Option<usize>,
        /// Whether the action is the next-state relation itself, which holds of every step the
        /// search took where TLC's predicate evaluation of it can't fail.
        is_next: bool,
        /// TLC's actions the action splits into, as the ENABLED of its fairness splits it, whose
        /// steps then answer it where the search labels them.
        split: Option<Split>,
        /// The position of the bit the walk sets on a step it takes through the pieces of Next
        /// the action is made of, which then answers it (`pieces.rs`).
        piece: Option<u32>,
    },
    /// ENABLED, run, or answered from the steps the search took when the action is made of TLC's
    /// actions of the next-state relation.
    Enabled {
        run: Result<Eval, String>,
        steps: Option<EnabledSteps>,
    },
    Unknown(String),
}

/// TLC's actions an action splits into: all of them, or those at the positions marked.
pub enum Split {
    All,
    Some(Vec<bool>),
}

impl Split {
    fn of(actions: &EnabledActions) -> Option<Split> {
        match actions {
            EnabledActions::Unknown => None,
            EnabledActions::All => Some(Split::All),
            EnabledActions::Some(positions) => {
                let length = positions.iter().max().map_or(0, |&last| last as usize + 1);
                let mut taken = vec![false; length];
                for &position in positions {
                    taken[position as usize] = true;
                }
                Some(Split::Some(taken))
            }
        }
    }
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
#[inline(always)]
pub fn count_possible(
    machine: &mut Machine<'_>,
    possible: &[(Eval, bool)],
    is_action: bool,
    counts: &mut [i64],
) -> Outcome<()> {
    if possible.is_empty() {
        return Ok(());
    }
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

/// The first of the predicates that fails of the state, evaluating each: where a parent may
/// violate one, as under `-continue`, none holds by its parent's.
pub fn first_failing(
    machine: &mut Machine<'_>,
    predicates: &[Predicate],
) -> Result<Option<usize>, (usize, Bail)> {
    for (position, predicate) in predicates.iter().enumerate() {
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
    // definition that reaches itself stays a conjunct, for the compiler to refuse. A constant
    // definition TLC computes as it starts (`processConstantDefns`) stays one too, whose value
    // TLC keeps and every use reads (`Compiler::adopted_definition`).
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
            Some(index)
                if matches!(conjunct, Conjunct::Node(_))
                    && self.definition(index).flags & Definition::NORMALIZED != 0 =>
            {
                self.add(conjunct)
            }
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

// Whether the engine leaves a startup definition it doesn't compile to its reporter, as it leaves
// an assumption it doesn't compile to the trace evaluator: TLC computes it as it starts
// (`processConstantDefns`), printing and drawing there, and every use reads the value it kept.
// Only where the first assumption names it, so that the reporter's evaluator, which checks that
// assumption, computes it before anything else TLC checks reads it, and where nothing but the
// assumptions reads it: what the engine compiles names it and fails to compile as it does, and
// the trace evaluator computes no ALIAS, POSTCONDITION or VIEW that may name it without the
// value TLC kept. Without the configuration's predicates or a symmetry, which the evaluator of
// assumptions doesn't follow, and only of a definition without parameters that TLC computes
// for its value, not its warnings.
fn is_left_to_reporter(ir: &Ir, index: Index) -> bool {
    let model = &ir.model;
    let startup = &model.startup;
    let node = ir.definitions[index as usize];
    let NodeKind::Definition(definition) = &ir.nodes.arena[node as usize].kind else {
        return false;
    };
    startup.predicates.is_empty()
        && startup.symmetry.is_none()
        && startup.dependents.is_empty()
        && model.alias.is_none()
        && model.view.is_none()
        && model.postconditions.is_empty()
        && definition.flags & Definition::STARTUP_WARNING_ONLY == 0
        && matches!(&definition.form, DefinitionForm::Operator(params) if params.is_empty())
        && startup
            .assumptions
            .first()
            .is_some_and(|&(assumption, _)| reaches_definition(ir, assumption, node))
}

// Whether evaluating an expression may name a definition, itself or through the definitions it
// names.
fn reaches_definition(ir: &Ir, root: NodeId, target: NodeId) -> bool {
    let mut seen = HashSet::new();
    let mut pending = vec![root];
    while let Some(node) = pending.pop() {
        if node == target {
            return true;
        }
        if !seen.insert(node) {
            continue;
        }
        let kind = &ir.nodes.arena[node as usize].kind;
        match kind {
            NodeKind::Reference(target) => pending.push(*target),
            NodeKind::Identifier(name)
            | NodeKind::OperatorReference(name)
            | NodeKind::Apply { name, .. } => {
                if let Resolution::Definition(index) = name.resolution {
                    pending.push(ir.definitions[index as usize]);
                }
            }
            NodeKind::Definition(definition) => pending.push(definition.body),
            _ => {}
        }
        pending.extend(kind.children());
    }
    false
}

// The variables a state predicate reads, which decide its value: it reads only its footprint.
// Whether evaluating an expression may read the next state outside an ENABLED: a prime, an
// UNCHANGED or an action's subscript, itself or through the definitions it names. SANY rejects
// such an invariant, but not one whose declared constant the configuration replaces by an action.
fn may_read_next(ir: &Ir, root: NodeId) -> bool {
    let mut seen = HashSet::new();
    let mut pending = vec![root];
    while let Some(node) = pending.pop() {
        if !seen.insert(node) {
            continue;
        }
        let kind = &ir.nodes.arena[node as usize].kind;
        match kind {
            NodeKind::Prime(_)
            | NodeKind::Unchanged(_)
            | NodeKind::BoxAction { .. }
            | NodeKind::AngleAction { .. } => return true,
            // ENABLED takes its own successors.
            NodeKind::Enabled(_) => continue,
            NodeKind::Reference(target) => pending.push(*target),
            NodeKind::Identifier(name)
            | NodeKind::OperatorReference(name)
            | NodeKind::Apply { name, .. } => {
                if let Resolution::Definition(index) = name.resolution {
                    pending.push(ir.definitions[index as usize]);
                }
            }
            NodeKind::Definition(definition) => pending.push(definition.body),
            _ => {}
        }
        pending.extend(kind.children());
    }
    false
}

// An invariant's evaluation as TLC's `Tool.isValid` makes it, of the state alone
// (`TLCState.Empty` as the next state): where the invariant may read the next state, a successor
// the search holds as the next state is hidden from it.
fn of_state_alone(eval: Eval) -> Eval {
    Arc::new(move |machine: &mut Machine<'_>| {
        let next = machine.next().to_vec();
        let unassigned = vec![UNASSIGNED; next.len()];
        machine.set_next(&unassigned);
        let value = eval(machine);
        machine.set_next(&next);
        value
    })
}

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
            // One the compiler can't take it can't take where it is read either.
            recursive_substitutes: model
                .startup
                .recursive_substitutes
                .iter()
                .filter_map(|&index| {
                    let body = match &ir.nodes.arena[ir.definitions[index as usize] as usize].kind {
                        NodeKind::Definition(definition) => definition.body,
                        _ => unreachable!("a definition's node"),
                    };
                    compiler
                        .compile_root_printing(Root::Expression(body), true)
                        .ok()
                        .map(|compiled| compiled.eval)
                })
                .collect(),
            definitions: model
                .startup
                .definitions
                .iter()
                .map(|&index| {
                    let is_retried = compiler.is_retried_at_use(index);
                    let has_failing_set_print = compiler.has_failing_set_print(index);
                    let is_direct_infinite_operation =
                        compiler.has_direct_infinite_operation(index);
                    let is_pure_print = compiler.is_pure_print(index);
                    let is_named_at_startup = compiler.is_named_at_startup(index);
                    if let Some(evaluate) = compiler.compile_kept_lazy_startup(index)? {
                        return Ok(StartupDefinition {
                            evaluate,
                            is_retried: false,
                            is_direct_infinite_operation: false,
                            has_failing_set_print: false,
                            is_pure_print: false,
                            is_named_at_startup,
                            is_warning_only: false,
                            is_kept_lazy: true,
                            left: None,
                            once: None,
                        });
                    }
                    let compiled = compiler.compile_root_printing(Root::Definition(index), true);
                    if let Err(CompileError::Bail(reason)) = &compiled
                        && compiler.is_native
                        && is_left_to_reporter(ir, index)
                    {
                        // Nothing the engine compiles reads it, and the reporter gives what TLC
                        // prints and draws as it computes it (`Reporter::computes_left_startup`).
                        return Ok(StartupDefinition {
                            evaluate: crate::compile::eval(|_| Ok(TRUE)),
                            is_retried: false,
                            is_direct_infinite_operation: false,
                            has_failing_set_print: false,
                            is_pure_print: false,
                            is_named_at_startup,
                            is_warning_only: false,
                            is_kept_lazy: false,
                            left: Some(reason.clone()),
                            once: None,
                        });
                    }
                    compiled
                        .map(|compiled| StartupDefinition {
                            is_kept_lazy: false,
                            left: None,
                            once: compiler.startup_once(index),
                            evaluate: compiled.eval,
                            is_retried,
                            is_direct_infinite_operation,
                            has_failing_set_print,
                            is_pure_print,
                            is_named_at_startup,
                            is_warning_only: matches!(
                                &ir.nodes.arena[ir.definitions[index as usize] as usize].kind,
                                NodeKind::Definition(definition) if definition.flags & Definition::STARTUP_WARNING_ONLY != 0
                            ),
                        })
                })
                .collect::<Result<_, CompileError>>()?,
            dependents: model
                .startup
                .dependents
                .iter()
                .map(|&(position, index)| {
                    // A startup definition listed again, for a later module that holds it, is
                    // evaluated again only where it failed itself.
                    let repeated = model
                        .startup
                        .definitions
                        .iter()
                        .position(|&listed| listed == index);
                    StartupDependent {
                        position: position as usize,
                        named: match repeated {
                            Some(listed) => vec![listed],
                            None => compiler.get_startup_names(index),
                        },
                        evaluate: compiler.compile_startup_dependent(index),
                        index,
                        is_repeat: repeated.is_some(),
                    }
                })
                .collect(),
            is_probe_assumed_once: model.startup.is_probe_assumed_once,
            register_probes: model
                .startup
                .register_probes
                .iter()
                .map(|&index| compiler.compile_register_probe(index))
                .collect(),
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
                                model
                                    .startup
                                    .definitions
                                    .iter()
                                    .position(|&index| index == predicate.definition),
                                predicate.definition,
                                predicate.is_state_level,
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
                    // A number or a string isn't a set (`getSymmetryPerms`).
                    let failure = match &ir.nodes.arena[body as usize].kind {
                        NodeKind::Number(_) | NodeKind::String(_) => {
                            Some(NOT_A_SET_OF_FUNCTIONS)
                        }
                        _ => None,
                    };
                    let (definition, elements, is_enumerated) =
                        compiler.compile_symmetry(body)?;
                    Ok::<_, CompileError>(StartupSymmetry {
                        failure,
                        definition: definition.eval,
                        elements,
                        is_enumerated,
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
            next_failure: get_next_literal(ir).map(|image| {
                format!(
                    "java.lang.RuntimeException\n: The next state relation is not a boolean expression.\n{image}"
                )
            }),
            is_next_declaration: reaches_next_declaration(ir)
                || model.startup.is_next_constant_cast,
            is_next_application_cast: reaches_application_cast(ir),
            assumptions: model
                .startup
                .assumptions
                .iter()
                .map(|&(node, name)| {
                    // TLC's diameter is the level of its empty trace as it checks the
                    // assumptions, which the startup sets, not one the search grows.
                    let is_diameter_read = compiler.is_diameter_read;
                    let compiled = compiler.compile_root_printing(Root::Expression(node), true);
                    compiler.is_diameter_read = is_diameter_read;
                    let eval = match compiled {
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
        for (owner, &(root, has_repeated_effect)) in roots.iter().enumerate() {
            if has_repeated_effect && can_print {
                printed.insert(root);
                conjuncts.add(root);
            } else {
                conjuncts.collect(root);
            }
            invariant_owners.resize(conjuncts.found.len(), owner);
        }
        // TLC checks each invariant whole in an initial state, and under -continue goes on past
        // one violated, so each keeps the conjuncts it shares with an invariant before it.
        let owned_conjuncts: Vec<(Conjunct, usize)> = roots
            .iter()
            .enumerate()
            .flat_map(|(owner, &(root, _))| {
                let mut owned = Conjuncts::new(ir);
                if printed.contains(&root) {
                    owned.add(root);
                } else {
                    owned.collect(root);
                }
                owned
                    .found
                    .into_iter()
                    .map(move |conjunct| (conjunct, owner))
            })
            .collect();
        let invariant_conjuncts = conjuncts.found;
        let mut invariants = invariant_conjuncts
            .iter()
            .map(|&conjunct| compile_conjunct(compiler, conjunct, printed.contains(&conjunct)))
            .collect::<Result<Vec<Compiled>, CompileError>>()?;
        let is_next_read = invariants
            .iter()
            .any(|compiled| !compiled.footprint.primes.is_empty())
            || model.invariants.iter().any(|invariant| {
                invariant
                    .root
                    .definition
                    .is_some_and(|index| may_read_next(ir, ir.definitions[index as usize]))
            })
            || model
                .property_invariants
                .iter()
                .any(|invariant| may_read_next(ir, invariant.root));
        if is_next_read {
            for compiled in &mut invariants {
                compiled.eval = of_state_alone(compiled.eval.clone());
            }
        }
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
        let mut is_action_property_printing = false;
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
            is_action_property_printing |= action.is_printing() || unchanged.is_printing();
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
        // `Tool.isInModel` evaluates the constraints of the state alone, as the invariants.
        let is_next_read = model.constraints.iter().any(|constraint| {
            constraint
                .definition
                .is_some_and(|index| may_read_next(ir, ir.definitions[index as usize]))
        });
        let constraints = conjuncts
            .found
            .into_iter()
            .map(|conjunct| {
                compile_conjunct(compiler, conjunct, printed.contains(&conjunct)).map(|compiled| {
                    let is_alone = is_next_read || !compiled.footprint.primes.is_empty();
                    Predicate {
                        vars: predicate_vars(&compiled, width),
                        eval: if is_alone {
                            of_state_alone(compiled.eval)
                        } else {
                            compiled.eval
                        },
                    }
                })
            })
            .collect::<Result<Vec<Predicate>, CompileError>>()?;
        // TLC checks each step against the action constraints as it finds the step, after the
        // constraints (`Worker.addElement`, `Tool.isInActions`), as the search does, so one may
        // print where the native checker reports what the search finds, and no step is walked
        // again for the liveness checker, a VIEW or symmetry.
        let can_action_constraint_print = compiler.is_native
            && compiler.simulation.is_none()
            && !model.is_recording_graph
            && model.view.is_none()
            && model.startup.symmetry.is_none();
        let action_constraints = model
            .action_constraints
            .iter()
            .map(|constraint| {
                let index = named("action constraint", ir, constraint)?;
                compiler
                    .compile_root_printing(Root::Definition(index), can_action_constraint_print)
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
        // The action atoms made of pieces of Next, each with a bit of its own, which the walk sets
        // on the steps it takes through them; the steps' answers are then the bits. Recorded only
        // where the steps aren't labelled by TLC's actions, which answer them otherwise.
        let mut pieces: Vec<Option<u32>> = match model.next {
            Some(next) if model.is_recording_graph && !model.is_labelled => {
                let mut count = 0;
                model
                    .atoms
                    .iter()
                    .map(|atom| {
                        let is_candidate = matches!(atom.kind, AtomKind::Action { .. })
                            && count < u64::BITS
                            && !is_next(compiler, ir, atom)
                            && compiler.is_walk_repeatable(atom.expression, &mut HashSet::new());
                        let values = is_candidate
                            .then(|| get_bound_values(ir, atom.scope, model.scope))
                            .flatten()?;
                        if !compiler.add_pieces(atom.expression, next, &values, count) {
                            return None;
                        }
                        count += 1;
                        Some(count - 1)
                    })
                    .collect()
            }
            _ => vec![None; model.atoms.len()],
        };
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
        // An atom answers from its bit only where the walk of Next went through each of its
        // pieces under the values it fixes.
        for piece in &mut pieces {
            *piece = piece.filter(|&bit| compiler.is_piece_walked(bit));
        }
        let piece_width = pieces
            .iter()
            .flatten()
            .max()
            .map_or(0, |&last| last as usize / 8 + 1);
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
                .zip(&pieces)
                .map(|(atom, &piece)| compile_atom(compiler, ir, atom, piece))
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
        let (initial_invariants, initial_invariant_owners) = owned_conjuncts
            .into_iter()
            .filter(|(conjunct, _)| !init_conjuncts.contains(conjunct))
            .map(|(conjunct, owner)| {
                let position = invariant_conjuncts
                    .iter()
                    .position(|&found| found == conjunct)
                    .expect("an invariant's conjunct the invariants hold");
                (invariants[position].eval.clone(), owner)
            })
            .unzip();
        // Under a VIEW TLC fingerprints the view's value alone, so a set TLC keeps lazy that a
        // variable holds stays as the spec built it, in an order the store doesn't keep.
        if view.is_some() && compiler.is_lazy_set_held && compiler.is_held_set_enumerated {
            return Err(CompileError::Bail(
                "unsupported: enumerating a lazy set of the state under a VIEW".into(),
            ));
        }
        Ok(EngineContext {
            piece_width,
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
            is_action_property_printing,
            startup,
            choices: compiler.get_constant_choices(),
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

// The values an atom's scope binds its names to below the model's scope, as the liveness checker
// expands a temporal `\A`, innermost first; none where it binds anything else.
fn get_bound_values(
    ir: &Ir,
    scope: Option<Index>,
    model_scope: Option<Index>,
) -> Option<Vec<(tla_ir::TextId, u32)>> {
    let mut values = Vec::new();
    let mut bound = scope;
    while bound != model_scope {
        let entry = &ir.scopes[bound? as usize];
        let ScopeBinding::Value(Some(value)) = entry.binding else {
            return None;
        };
        values.push((entry.name, value));
        bound = entry.parent;
    }
    Some(values)
}

// TLC's actions an action atom splits into, where the ENABLED of its fairness is of the same
// action in the same scope and splits it.
fn get_split(ir: &Ir, atom: &tla_ir::Atom, enabled: Option<Index>) -> Option<Split> {
    let enabled = &ir.model.atoms[enabled? as usize];
    let AtomKind::Enabled { actions } = &enabled.kind else {
        return None;
    };
    let NodeKind::AngleAction { action, .. } = resolve(ir, enabled.expression) else {
        return None;
    };
    (enabled.scope == atom.scope && resolve_id(ir, *action) == resolve_id(ir, atom.expression))
        .then(|| Split::of(actions))
        .flatten()
}

fn resolve_id(ir: &Ir, node: NodeId) -> NodeId {
    let mut id = node;
    while let NodeKind::Reference(target) = &ir.nodes.arena[id as usize].kind {
        id = *target;
    }
    id
}

// TLC prints a warning its liveness checker meets evaluating an atom (Tool's OPCODE_exc prints
// 2144 for an EXCEPT's missing path, enabledUnchangedImpl 2143 for an UNCHANGED that doesn't
// hold) between what the checker reports, unless MP's history of warnings already holds it; the
// engine doesn't place it there, so an atom's evaluation that warns fails instead, as an atom
// that may fail to evaluate.
fn guard_atom_warnings(atom: Atom) -> Atom {
    let guard = |evaluate: Eval| -> Eval {
        Arc::new(move |machine: &mut Machine<'_>| {
            let outer = machine.guarding_atom_warnings;
            machine.guarding_atom_warnings = true;
            let result = evaluate(machine);
            machine.guarding_atom_warnings = outer;
            result
        })
    };
    match atom {
        Atom::State(evaluate) => Atom::State(guard(evaluate)),
        Atom::LevelState(evaluate) => Atom::LevelState(guard(evaluate)),
        Atom::LevelAction { action, subscript } => Atom::LevelAction {
            action: guard(action),
            subscript: subscript.map(guard),
        },
        Atom::Action {
            action,
            subscript,
            key,
            enabled,
            is_next,
            split,
            piece,
        } => Atom::Action {
            action: guard(action),
            subscript: subscript.map(guard),
            key,
            enabled,
            is_next,
            split,
            piece,
        },
        Atom::Enabled { run, steps } => Atom::Enabled {
            run: run.map(guard),
            steps: steps.map(|steps| EnabledSteps {
                subscript: guard(steps.subscript),
                ..steps
            }),
        },
        Atom::Unknown(why) => Atom::Unknown(why),
    }
}

fn compile_atom(
    compiler: &mut Compiler<'_>,
    ir: &Ir,
    atom: &tla_ir::Atom,
    piece: Option<u32>,
) -> CompiledAtom {
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
            let (subscript, key) = match unchanged {
                None => (None, None),
                Some(node) => match resolve(ir, *node) {
                    NodeKind::Unchanged(inner) => (
                        Some(compile_subscript(compiler, *inner, scope)?),
                        Some(get_subscript_key(ir, *inner, scope)),
                    ),
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
            let is_answered = !action.reads_search();
            Ok(Atom::Action {
                is_next: is_answered && is_next(compiler, ir, atom),
                split: get_split(ir, atom, *enabled).filter(|_| {
                    is_answered && compiler.is_walk_repeatable(atom.expression, &mut HashSet::new())
                }),
                piece: piece.filter(|_| is_answered),
                action: action.eval,
                subscript: subscript.map(|subscript| subscript.eval),
                key,
                enabled: enabled.map(|position| position as usize),
            })
        })(),
        AtomKind::Enabled { actions } => {
            let outer = std::mem::replace(&mut compiler.is_unchanged_warning, false);
            let compiled_run = compiler.compile_enabled_in_scope(atom.expression, scope);
            // TLC's ENABLED warns of an UNCHANGED variable its action changed
            // (`enabledUnchangedImpl`), where the search's steps, whatever their answer, may not
            // have (`processUnchangedImplVar` meets the conjuncts otherwise), so an ENABLED whose
            // walk may warn so is run, where a warning fails the atom, and not read off them.
            let may_warn_unchanged = compiler.is_unchanged_warning;
            compiler.is_unchanged_warning |= outer;
            let run = match compiled_run {
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
                _ if may_warn_unchanged => None,
                (NodeKind::AngleAction { subscript, .. }, actions) => {
                    // A subscript that reads TLC's diameter leaves ENABLED to its run, which
                    // doesn't read it.
                    compile_subscript(compiler, *subscript, scope)
                        .ok()
                        .filter(|subscript| !subscript.reads_diameter())
                        .map(|compiled| EnabledSteps {
                            subscript: compiled.eval,
                            key: get_subscript_key(ir, *subscript, scope),
                            actions: match Split::of(actions) {
                                Some(Split::Some(taken)) => Some(taken),
                                _ => None,
                            },
                        })
                }
                _ => None,
            };
            Ok(Atom::Enabled { run, steps })
        }
    };
    let atom = compiled.unwrap_or_else(Atom::Unknown);
    CompiledAtom {
        atom: if ir.model.is_warning_enabled {
            guard_atom_warnings(atom)
        } else {
            atom
        },
        is_printing,
        reads_diameter,
        uses_registers,
    }
}
