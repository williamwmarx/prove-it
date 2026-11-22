//! The engine IR: the model as `src/engine/ir.ts` lowers it, which the native engine reads in
//! place of the TypeScript AST and environment. [`decode`] reads the blob and [`encode`] writes
//! it again, byte for byte, which is how the two sides are held to one layout. `ir.ts` documents
//! the layout; the constants below are its numbers.

mod decode;
mod encode;
pub mod wtf8;

/// The stack the decoder and the encoder run on. Both follow nested nodes by recursion, up to the
/// decoder's limit, and a Rust stack overflow aborts the process rather than failing, so they run
/// on a thread whose stack holds that many levels. Ten thousand levels took between 128 and 256 MB
/// in a debug build and under 32 MB in a release build; each size is about twice that. The stack
/// is reserved, not committed.
#[cfg(not(target_arch = "wasm32"))]
const NESTING_STACK_BYTES: usize = if cfg!(debug_assertions) {
    512 * 1024 * 1024
} else {
    64 * 1024 * 1024
};

fn on_nesting_stack<T: Send>(work: impl FnOnce() -> T + Send) -> T {
    // WebAssembly runs on one thread, whose stack the module sets as it links.
    #[cfg(target_arch = "wasm32")]
    return work();
    #[cfg(not(target_arch = "wasm32"))]
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(NESTING_STACK_BYTES)
            .spawn_scoped(scope, work)
            .expect("a thread for the nested nodes")
            .join()
            .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
    })
}

use std::collections::HashMap;

pub use decode::{DecodeError, decode};
pub use encode::encode;

/// The version of the layout, `IR_VERSION` in `ir.ts`.
pub const IR_VERSION: u32 = 17;

/// The version before the startup's dependents (`Startup::dependents`), which an IR without any
/// is still written as, so that what was written then reads as it did.
pub const IR_VERSION_WITHOUT_DEPENDENTS: u32 = 16;

/// "PIIR" as a little-endian word.
pub const MAGIC: u32 = 0x5249_4950;

/// An index into [`Ir::texts`].
pub type TextId = u32;
/// An index into [`Nodes::arena`].
pub type NodeId = u32;
/// A warning raised while TLC evaluates the model, kept in evaluation order with Print.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum RuntimeWarning {
    Except { node: NodeId },
    Unchanged { node: NodeId, variable: u32 },
}

/// An index into [`Ir::definitions`], [`Ir::scopes`], [`Ir::constants`] or [`Ir::builtins`].
pub type Index = u32;

impl Ir {
    /// A text's UTF-16 code units, as the store holds a string.
    pub fn get_text_units(&self, text: TextId) -> Vec<u16> {
        self.wide_texts.get(&text).map_or_else(
            || self.texts[text as usize].encode_utf16().collect(),
            |units| units.to_vec(),
        )
    }

    /// Whether the IR may apply TLC's TLCGet to `key`: wherever it names the builtin but where
    /// it applies it to a string literal other than `key`.
    pub fn may_read_tlc_get(&self, key: &str) -> bool {
        let is_tlc_get = |name: &Name| {
            !name.is_local
                && matches!(name.resolution, Resolution::Builtin(index)
                    if self.builtins.get(index as usize).is_some_and(|builtin|
                        &*self.texts[builtin.name as usize] == "TLCGet"))
        };
        self.nodes.arena.iter().any(|node| match &node.kind {
            NodeKind::Apply { name, args } => {
                is_tlc_get(name)
                    && !args.first().is_some_and(|&arg| {
                        matches!(&self.nodes.arena[arg as usize].kind,
                            NodeKind::String(text) if &*self.texts[*text as usize] != key)
                    })
            }
            NodeKind::Identifier(name) | NodeKind::OperatorReference(name) => is_tlc_get(name),
            _ => false,
        })
    }

    /// A node, through the references that stand for it.
    fn resolve(&self, node: NodeId) -> (NodeId, &NodeKind) {
        let mut id = node;
        loop {
            match &self.nodes.arena[id as usize].kind {
                NodeKind::Reference(target) => id = *target,
                kind => return (id, kind),
            }
        }
    }

    /// How many of the ranked texts TLC numbers as the IR ranks them, which the fingerprint of a
    /// model value of that name shows (`UniqueString.tok`): those TLC interns first, the texts of
    /// the configuration's values (`ModelConfig`), and then those it interns as it starts, up to
    /// the last of them, "@". The texts of the modules come after, which TLC numbers otherwise.
    pub fn get_numbered_rank_count(&self) -> i32 {
        let ranked = &self.texts[..(self.ranked_count as usize).min(self.texts.len())];
        ranked
            .iter()
            .position(|ranked| &**ranked == "@")
            .map_or(0, |position| position as i32 + 1)
    }

    /// The rank of the root module's name where TLC numbers it as the IR ranks it
    /// (`UniqueString.tok`), past those of [`Ir::get_numbered_rank_count`]: the texts of the root
    /// module rank in the order TLC interns them, from the separator of its header, which TLC
    /// interns with the `MODULE` after it as one number, and so the name after them has TLC's
    /// number where neither the separator nor `MODULE` ranks among those TLC interns first, nor
    /// the name. The texts after it TLC numbers otherwise.
    pub fn get_root_name_rank(&self) -> Option<i32> {
        let numbered = self.get_numbered_rank_count();
        let name = self.model.root_module_name?;
        let ranked = &self.texts[..(self.ranked_count as usize).min(self.texts.len())];
        let is_separator = |text: &str| text.len() >= 4 && text.bytes().all(|byte| byte == b'-');
        let is_first_after_separator = numbered > 0
            && ranked
                .get(numbered as usize)
                .is_some_and(|text| is_separator(text))
            && name as i64 == i64::from(numbered) + 1
            && ranked[..numbered as usize]
                .iter()
                .all(|text| !is_separator(text) && &**text != "MODULE");
        is_first_after_separator.then_some(name as i32)
    }

    /// Whether the function of an application or the record of a field, other than an
    /// application of TestRandomSetOfSubsets itself, may reach TestRandomSetOfSubsets, which TLC
    /// evaluates there with `EvalControl.KeepLazy`: through a definition (its body, and a
    /// function's bounds), a filter's bound set, or a name bound to an argument or a LET's
    /// definition, which may be one, whether applied, named or passed as an operator. A
    /// subexpression selector, which names what it reaches by text, may reach anything.
    pub fn may_keep_test_draws_lazy(&self) -> bool {
        let is_test = |name: &Name| {
            !name.is_local
                && matches!(name.resolution, Resolution::Builtin(index)
                    if self.builtins.get(index as usize).is_some_and(|builtin|
                        &*self.texts[builtin.name as usize] == "TestRandomSetOfSubsets"))
        };
        let reaches = |start: NodeId| {
            let mut visited = std::collections::HashSet::new();
            let mut pending = vec![start];
            while let Some(node) = pending.pop() {
                let (node, kind) = self.resolve(node);
                if !visited.insert(node) {
                    continue;
                }
                match kind {
                    NodeKind::Subexpression(_) => return true,
                    NodeKind::Identifier(name)
                    | NodeKind::OperatorReference(name)
                    | NodeKind::Apply { name, .. } => {
                        if name.is_local || is_test(name) {
                            return true;
                        }
                        if let Resolution::Definition(index) = name.resolution {
                            pending.push(self.definitions[index as usize]);
                        }
                    }
                    NodeKind::SetFilter { bound, .. } => pending.push(bound.set),
                    _ => {}
                }
                pending.extend(kind.children());
            }
            false
        };
        self.nodes.arena.iter().any(|node| match &node.kind {
            NodeKind::FunctionApplication { function, args } => {
                let is_applied_test = args.len() == 1
                    && matches!(self.resolve(*function).1, NodeKind::Apply { name, .. } if is_test(name));
                !is_applied_test && reaches(*function)
            }
            NodeKind::FieldAccess { record, .. } => reaches(*record),
            _ => false,
        })
    }
}

/// A decoded IR. Everything that refers to a node does so by its [`NodeId`].
#[derive(Debug, Clone, PartialEq)]
pub struct Ir {
    /// How many of the texts TLC ranks: text `i` below this has rank `i`.
    pub ranked_count: u32,
    pub texts: Vec<Box<str>>,
    /// The UTF-16 code units of each text with a lone surrogate, which a `str` can't hold: TLC
    /// computes such strings, as `Tail("😀a")`, and ranks them.
    pub wide_texts: std::collections::BTreeMap<TextId, Box<[u16]>>,
    /// The variables in the engine's order.
    pub variables: Vec<TextId>,
    /// TLC's order of the variables, as positions in [`Ir::variables`].
    pub tlc_order: Vec<i32>,
    pub builtins: Vec<Builtin>,
    pub constants: Vec<Constant>,
    pub scopes: Vec<Scope>,
    pub values: Values,
    pub model: Model,
    /// The definitions the model reaches: each a node of kind [`NodeKind::Definition`].
    pub definitions: Vec<NodeId>,
    pub nodes: Nodes,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Builtin {
    pub name: TextId,
    pub arity: i32,
    pub flags: i32,
    /// With `TABLE`, a configuration's definition of a constant operator by its values: each
    /// row's arguments as a tuple and its value, or `None` for one the IR can't hold.
    pub table: Vec<(Option<Index>, Option<Index>)>,
}

impl Builtin {
    pub const STATE_LEVEL: i32 = 1;
    pub const LEVEL_CONSTANT: i32 = 2;
    pub const LAZY: i32 = 4;
    pub const TABLE: i32 = 8;
    /// The frontend modeled this actual configuration table object and all declared receivers
    /// which initialize it, before startup effects. Missing/failed lazy row data stays at eval.
    pub const TABLE_PHASE_KNOWN: i32 = 16384;
    /// Existing source-resolver reads proved every actual standard shortcut and dependency
    /// absent from external source paths or byte-identical to this pinned reference profile.
    /// Only the new Json replay/Array/Object paths consume this source-prefix certificate.
    pub const PINNED_STANDARD_SOURCES: i32 = 32768;
    /// `>=` of `tlc2.module.Naturals`, which names itself `>` in its errors, where the `>=` of
    /// Integers names itself.
    pub const NATURALS_GEQ: i32 = 16;
    /// An operator a method of `tlc2.module.Naturals` computes rather than one of
    /// `tlc2.module.Integers`, which TLC loads over it where the spec uses Integers.
    pub const NATURALS_METHOD: i32 = 32;
    /// A TLCExt builtin the engine declines where it computes it, as it did before it checked
    /// them: one a configuration substitute, or a constant definition or an assumption TLC
    /// computes as it starts, reaches.
    pub const DECLINED: i32 = 64;
    /// This exact numeral or string Expr was not visited by TLC's processConstants.
    pub const UNINITIALIZED_LITERAL: i32 = 2048;
    /// The standard-module linker installed TLCExt's TLCDefer with the packaged Java
    /// implementation selected under a closed resolver and override-index context.
    pub const PACKAGED_TLC_DEFER: i32 = 4096;
    /// The environment found an external Java class for this builtin's module or an override
    /// index that may replace it. Optimizations assuming the packaged method keep their prior path.
    pub const EXTERNAL_CLASS: i32 = 256;
    /// The frontend proved the complete Java producer context closed for this model.
    pub const CLOSED_JAVA_CONTEXT: i32 = 8192;
    /// With `DECLINED`, a definition a method a `tlc2.overrides.TLCOverrides` index lists
    /// replaces (`processModuleOverrides`): the engine declines where it computes it, and only
    /// there, since TLC never calls the method where it doesn't.
    pub const INDEX_REPLACED: i32 = 65536;
    /// On TLCGet: the spec reads `TLCGet("stats")` only through its domain and its fields other
    /// than its duration, and `TLCGet("revision")` only through its domain, so the values TLC
    /// alone knows, the time it has run and its build, show nowhere.
    pub const RUN_UNKNOWNS_UNREAD: i32 = 131072;
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Constant {
    pub name: TextId,
    /// The value, or `None` for one the transfer encoding can't hold.
    pub value: Option<u32>,
}

/// A binding of an instance's scope, which the compiler translates as `contextFromScope` does.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Scope {
    pub parent: Option<Index>,
    pub name: TextId,
    pub binding: ScopeBinding,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ScopeBinding {
    /// A value, or `None` for one the transfer encoding can't hold.
    Value(Option<u32>),
    Thunk {
        expression: NodeId,
        scope: Option<Index>,
    },
    Closure {
        name: TextId,
        params: Vec<Param>,
        body: NodeId,
        scope: Option<Index>,
    },
    /// A binding the engine can't translate, such as to a builtin.
    Opaque,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Param {
    pub name: TextId,
    pub arity: i32,
}

/// The values of constants and scopes, in `transfer.ts`'s encoding.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Values {
    /// The texts the values' strings and model values name, by the encoding's string index.
    pub strings: Vec<TextId>,
    pub list: Vec<Value>,
}

/// A value as `transfer.ts` encodes it. A string or model value names its text by the index into
/// [`Values::strings`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Value {
    Bool(bool),
    Int(i32),
    String(u32),
    ModelValue(u32),
    Set(Vec<Value>),
    /// A function with its TLC class (0 none, 1 lambda, 2 tuple, 3 record).
    Function {
        class: i32,
        domain: Vec<Value>,
        range: Vec<Value>,
    },
    /// A function over the interval `low..low + range.len() - 1`.
    IntervalFunction {
        class: i32,
        low: i32,
        range: Vec<Value>,
    },
}

/// A name the configuration gives, and the definition it names.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConfigName {
    pub name: TextId,
    pub definition: Option<Index>,
}

/// A root that may print, which the engine checks whole each time, as TLC does.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Printed<T> {
    pub root: T,
    pub has_repeated_effect: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Action {
    pub expression: NodeId,
    pub scope: Option<Index>,
    /// How TLC names the action in a trace: `Inc line 5, col 8 to line 5, col 41 of module D`.
    pub label: TextId,
    /// The name and location TLC's `Action` holds, which TLCExt's CounterExample records:
    /// `UnnamedAction` for an action of no operator.
    pub name: TextId,
    pub location: Option<SourceRange>,
    /// The definition TLC split the action from (`Action.getOpDef`), whose parameters
    /// CounterExample binds, by index; none for an action of no operator, or of one a LET
    /// defines.
    pub definition: Option<Index>,
}

/// A definition an INSTANCE with substitutions copies, and the name and location TLC gives an
/// action that applies it: the name the instance exports it by, at the INSTANCE.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InstanceAction {
    pub definition: Index,
    pub name: TextId,
    pub location: Option<SourceRange>,
}

/// A `_POSSIBLE` predicate, which TLC counts the states, or with `is_action` the steps, it holds of.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Possible {
    pub name: ConfigName,
    pub is_action: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ActionProperty {
    pub action: NodeId,
    pub subscript: NodeId,
    /// The scope of the instance the property comes from, which it is read in.
    pub scope: Option<Index>,
    /// How TLC names the property as it reports a step that violates it
    /// (`SpecProcessor.impliedActNameVec`): the configuration's name for a property that is the
    /// `[][A]_v` alone, and where the `[][A]_v` is written for a conjunct of one.
    pub name: TextId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AtomKind {
    State,
    /// An action, with the atom of its fairness's ENABLED, which the checker asks first.
    Action {
        unchanged: Option<NodeId>,
        enabled: Option<Index>,
    },
    Enabled {
        actions: EnabledActions,
    },
}

/// The positions of TLC's actions an ENABLED atom splits into.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EnabledActions {
    Unknown,
    All,
    Some(Vec<i32>),
}

/// A liveness atom the tableau asks about.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Atom {
    pub kind: AtomKind,
    pub expression: NodeId,
    pub scope: Option<Index>,
}

/// A term of the formula the liveness checker solves, in prefix order: a junction is followed by
/// its operands and a unary term by its body. An atom is its position among the model's atoms, or
/// past them for one the checker asks nothing of.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LiveTerm {
    Boolean(bool),
    State(Index),
    Enabled(Index),
    Action { atom: Index, enabled: Option<Index> },
    Not,
    Always,
    Eventually,
    Next,
    And(u32),
    Or(u32),
}

/// A temporal property, by name, as the liveness checker names it in a counterexample.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LiveProperty {
    pub name: TextId,
    pub formula: Vec<LiveTerm>,
}

/// What the configuration and the checker ask of the search.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Model {
    pub init: NodeId,
    /// The next-state relation, none where the configuration names none: TLC then computes
    /// the initial states only, and the configuration checks nothing of behaviors.
    pub next: Option<NodeId>,
    pub scope: Option<Index>,
    /// TLC's actions of the next-state relation, which a trace labels its steps with.
    pub actions: Vec<Action>,
    /// Whether the search takes each state's steps through the actions and labels them, which
    /// ENABLED asks for, rather than through the next-state relation.
    pub is_labelled: bool,
    pub invariants: Vec<Printed<ConfigName>>,
    pub property_invariants: Vec<Printed<NodeId>>,
    /// The name TLC gives each of `property_invariants` when it reports it violated: the operator
    /// the property asserts always holds, or the property's name.
    pub property_invariant_names: Vec<TextId>,
    /// The scope of the instance each of `property_invariants` comes from, which it is read in.
    pub property_invariant_scopes: Vec<Option<Index>>,
    pub constraints: Vec<ConfigName>,
    pub action_constraints: Vec<ConfigName>,
    pub possible: Vec<Possible>,
    pub action_properties: Vec<ActionProperty>,
    pub initial_predicates: Vec<NodeId>,
    /// The scope of the instance each of `initial_predicates` comes from, which it is read in.
    pub initial_predicate_scopes: Vec<Option<Index>>,
    /// The name TLC gives each of `initial_predicates` when an initial state violates it: the
    /// property's.
    pub initial_predicate_names: Vec<TextId>,
    pub view: Option<ConfigName>,
    /// The configuration's ALIAS, which TLC prints each state of a trace through.
    pub alias: Option<ConfigName>,
    /// The configuration's POSTCONDITIONs, which TLC checks once the search ends.
    pub postconditions: Vec<ConfigName>,
    pub check_deadlock: bool,
    pub is_warning_enabled: bool,
    pub is_recording_graph: bool,
    pub version: Option<TextId>,
    /// The seed TLC seeds its generator with before it starts, and reseeds it with for each state
    /// it expands, xored with the state's fingerprint (`RandomEnumerableValues`).
    pub random_seed: u64,
    /// The index in FP64.Polys of the polynomial TLC fingerprints with, which `-fp` picks. The
    /// IR's encoding doesn't hold it: an IR decodes with 0, which JavaScript checks with, and the
    /// command line sets it.
    pub fingerprint_index: usize,
    /// The text of the root module's name, which TLC numbers as the IR ranks it where it is the
    /// first text of the root module TLC interns after those it interns as it starts
    /// (`Ir::get_root_name_rank`). The IR's encoding doesn't hold it: an IR decodes without it,
    /// and the command line sets it.
    pub root_module_name: Option<TextId>,
    pub atoms: Vec<Atom>,
    /// The fairness and the negated properties as the liveness checker joins them, or no terms.
    pub live_formula: Vec<LiveTerm>,
    /// Each property, whose violation a counterexample's checks find, in the configuration's order.
    pub live_properties: Vec<LiveProperty>,
    /// The source range of the definition the configuration's SPECIFICATION names, which TLC's
    /// warning of a stuttering counterexample prints.
    pub specification: Option<SourceRange>,
    /// Where the SPECIFICATION reaches the next-state relation through a definition an INSTANCE
    /// with substitutions copies, the first such INSTANCE, at which TLC takes the relation as one
    /// unnamed action (`describeSpecification`).
    pub next_substitution: Option<SourceRange>,
    /// The definitions of the IR an INSTANCE with substitutions copies (`instanceActions`), by
    /// index.
    pub instance_actions: Vec<InstanceAction>,
    /// The name TLC gives each definition of the IR a named INSTANCE copies, such as `I!Foo`
    /// (`instanceNames`), by index.
    pub instance_names: Vec<(Index, TextId)>,
    /// TLCGet("spec"), the record of the specification as TLC processed it, by its position in
    /// the IR's values, where an expression reads it (`TLCGetSet.TLCGetStringValue`).
    pub tlc_spec: Option<u32>,
    /// What `TLCExt.tlcDefByName` finds in the root module for each name a TLCEvalDefinition is
    /// written with (`ModuleNode.getOpDef`), by the name's text. A name it doesn't list is one
    /// the front end didn't look up.
    pub evaluated_definitions: Vec<(TextId, EvaluatedDefinition)>,
    /// What TLC evaluates when it starts, before the search.
    pub startup: Startup,
}

/// What `ModuleNode.getOpDef` of the root module gives TLCEvalDefinition for a name.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EvaluatedDefinition {
    /// A definition without parameters, by index, whose body TLC evaluates as written.
    Body(Index),
    /// A definition with parameters, by its signature (`OpDefNode.getSignature`).
    Signature(TextId),
    /// No definition of the root module's by that name.
    Missing,
}

/// What TLC evaluates when it starts, in the order the engine evaluates it: each substitute,
/// then each definition, then the symmetry, then each assumption.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Startup {
    /// The substitutes for declared constants that TLC evaluates and rejects if they fail: the
    /// constant's name and the 0-ary definition substituted for it, whose level bound is above
    /// constant.
    pub substitutes: Vec<(TextId, Index)>,
    /// The 0-ary definitions of constant level substituted for declared constants that may
    /// recurse: TLC evaluates each as it starts and swallows the EvalException it throws, but not
    /// the StackOverflowError of a recursion without end, which ends the startup
    /// (`processConstantDefns`). The engine evaluates each only to find one too deep for it.
    pub recursive_substitutes: Vec<Index>,
    /// The constant definitions with effects that TLC evaluates once, in TLC's order. Each keeps
    /// the value it computes.
    pub definitions: Vec<Index>,
    /// The constant definitions without effects of their own that TLC computes as it starts and
    /// that name one of `definitions`, as written or through the definitions they name: each
    /// with how many of `definitions` TLC computes before it. Where one of those fails, TLC
    /// swallows it and evaluates it again inside each, with its effects
    /// (`processConstantDefns`).
    pub dependents: Vec<(u32, Index)>,
    /// The constant definitions that reach TLCSet, which TLC computes as it starts, before it
    /// has a checker, so that TLCSet of a number throws there, where the front end can't tell
    /// whether TLC fails or completes before any effect. The engine computes each there, after
    /// `definitions`, and stops at its TLCSet: one that fails, or completes to a boolean, a
    /// number or a string, without any effect before, TLC swallows or keeps, and the engine
    /// computes at each use alike; at any other end the engine declines.
    pub register_probes: Vec<Index>,
    /// Whether the one register probe is a definition only the first assumption reads, once, by
    /// its name alone, after a startup in which nothing else has an effect: TLC computes it as it
    /// starts, with its effects, and keeps the value where it reaches no TLCSet, which the engine,
    /// computing it at the assumption from the same generator, shows alike.
    pub is_probe_assumed_once: bool,
    /// The constant definitions the configuration names, which TLC evaluates as it reads the
    /// configuration (`getConstantValue`) and rejects for their value, in TLC's order.
    pub predicates: Vec<StartupPredicate>,
    /// The SYMMETRY definition, which TLC evaluates to its group as it builds its `Tool`.
    pub symmetry: Option<Symmetry>,
    /// Whether `Tool.getActions`, which follows the symmetry as TLC builds its `Tool`, fails first
    /// casting the declaration of a constant the configuration substitutes a definition for
    /// (`C <- Op`) to OpDefNode, which the engine declines.
    pub is_next_constant_cast: bool,
    /// The assumptions that aren't axioms, each with the name TLC reports it by.
    pub assumptions: Vec<(NodeId, TextId)>,
}

/// A constant definition the configuration names, which TLC rejects for its value. A definition
/// that fails to evaluate is no error: TLC keeps it as an operator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StartupPredicate {
    pub form: PredicateForm,
    /// What the configuration names it as, such as `invariant`.
    pub kind: TextId,
    pub name: TextId,
    pub definition: Index,
    /// Whether `getLevelBound` takes it for a state's, as it names a name spelled as a variable,
    /// so that TLC doesn't compute it as it starts but checks it in each state: the engine,
    /// computing it, answers only where that computation reads the same (a failure, or TRUE but
    /// for an invariant) and has no effect.
    pub is_state_level: bool,
}

/// How TLC rejects a constant definition the configuration names.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PredicateForm {
    /// `getConfigPredicate`: any value but TRUE, as "The {kind} of {name} is equal to {value}".
    Predicate = 0,
    /// `getConfigDefinition`: any value, as "The {kind} {name} cannot be a constant.".
    Definition = 1,
    /// The SPECIFICATION: any value, as "The value of {name} is equal to {value}".
    Specification = 2,
    /// A constant conjunct of the SPECIFICATION (`processConfigSpec`), which TLC drops where it
    /// is TRUE: FALSE as "The spec is trivially false because {name} is false.", any other value
    /// as "The operator {name}, which equals {value},\ncannot be used as a {kind}".
    Conjunct = 3,
}

/// The configuration's SYMMETRY: a 0-ary definition whose value is a set of permutations of
/// model values (`Tool.getSymmetryPerms`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Symmetry {
    pub definition: Index,
    /// The sets the definition's body applies its operator to, which TLC warns about where they
    /// hold fewer than two elements.
    pub permuted_sets: Vec<PermutedSet>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PermutedSet {
    /// The name TLC's warning gives the set: the name the configuration substitutes for it, or
    /// the text of its expression.
    pub name: TextId,
    /// For `Permutations(S)` with S a constant or definition the configuration doesn't replace
    /// with `<-`, S, whose value TLC checks for a model value the group moves.
    pub operand: Option<NodeId>,
}

/// The nodes, in the order of the blob, and which of them are written at the top level.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct Nodes {
    pub arena: Vec<Node>,
    pub top: Vec<NodeId>,
    /// How each junction that is a bulleted list or an infix chain is written, by its node.
    pub junctions: HashMap<NodeId, Junction>,
    /// How each numeral written otherwise than its value in decimal (`007`, `\b101`, `\h1F`) is
    /// written, by its node: SANY's `NumeralNode.toString`, its image.
    pub numerals: HashMap<NodeId, TextId>,
}

/// How a junction is written: as a bulleted list, or as an infix chain such as A /\ B /\ C, which
/// SANY parses as (A /\ B) /\ C. TLC prints the range of each prefix of two or more operands, which
/// ends where `prefix_ends` says, a line and column for each.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Junction {
    pub is_bulleted: bool,
    pub prefix_ends: Vec<(i32, i32)>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Node {
    pub line: i32,
    pub column: i32,
    /// Where the node is written, which TLC's messages print, if the front end knows.
    pub range: Option<SourceRange>,
    pub kind: NodeKind,
}

/// A node's source range: its module and where it starts and ends, as TLC prints them in
/// `line 2, col 3 to line 2, col 9 of module M`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SourceRange {
    pub module: TextId,
    pub start_line: i32,
    pub start_column: i32,
    pub end_line: i32,
    pub end_column: i32,
}

/// What a name refers to outside any binding of it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Resolution {
    None,
    /// A variable by its slot, which for an instance's variable that ENABLED's rewrite names, such
    /// as `x@ENABLED`, may be past the state's variables.
    Variable(u32),
    Constant(Index),
    Definition(Index),
    Builtin(Index),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Name {
    pub text: TextId,
    pub resolution: Resolution,
    /// Whether SANY resolved the name to a binding around it, which the compiler looks up first.
    pub is_local: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Pattern {
    Name(TextId),
    Tuple(Vec<TextId>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Bound {
    pub pattern: Pattern,
    pub set: NodeId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PathStep {
    Field(TextId),
    Index(Vec<NodeId>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Update {
    pub path: Vec<PathStep>,
    pub value: NodeId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Selector {
    Name {
        name: TextId,
        args: Vec<NodeId>,
    },
    /// An operand by number, or -1 for `<<` and -2 for `>>`.
    Operand(i32),
    Bound(Vec<NodeId>),
    At,
    Colon,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DefinitionForm {
    Operator(Vec<Param>),
    Function(Vec<Bound>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Definition {
    pub name: TextId,
    pub flags: i32,
    pub form: DefinitionForm,
    pub body: NodeId,
}

impl Definition {
    pub const RECURSIVE: i32 = 1;
    pub const LOCAL: i32 = 2;
    pub const SELF_REFERENTIAL: i32 = 4;
    pub const REPEATED_EFFECT: i32 = 8;
    pub const SUBSTITUTED: i32 = 16;
    /// A copy an INSTANCE with substitutions makes of a definition that is itself such a copy,
    /// made by an INSTANCE in the module instantiated: TLC's copy's body is a `SubstInNode` over
    /// the copied definition's, which is one too.
    pub const NESTED_SUBSTITUTION: i32 = 1024;
    /// A constant definition TLC computes and deep-normalizes at startup (`processConstantDefns`).
    pub const NORMALIZED: i32 = 32;
    /// An operator definition whose body is a numeral or a string, which TLC holds as the value it
    /// gave the literal and never computes as it starts (`SymbolNodeValueLookupProvider.lookup`):
    /// not an INSTANCE's copy with substitutions, whose body is a substitution, and not one the
    /// configuration substitutes for another definition, which TLC computes in that one's name
    /// (`processConstantDefns`); the front end counts any name but a declared constant of the root
    /// module as one.
    pub const LITERAL: i32 = 64;
    /// A copy of a constant definition TLC computes as it starts, which a name the configuration
    /// substitutes it for reads: that name's lookup finds the definition's OpDefNode, not the
    /// value `processConstantDefns` kept, and `Tool.evalAppl` evaluates the body as written.
    pub const CONFIGURED_SUBSTITUTE: i32 = 2048;
    /// A constant definition with effects the engine computes as TLC starts, which another
    /// constant definition TLC computes there (`processConstantDefns`), one the engine computes
    /// only where it is used or never, names, as written or through the definitions it names:
    /// TLC evaluates it again there, with its prints and draws, where it fails. The front end
    /// lists those others (`Startup::dependents`), and writes it for a definition the
    /// configuration substitutes for another definition, which TLC computes again where it
    /// reaches that one, whatever came of computing it before, and for one that a drawing
    /// INSTANCE substitute read more than once in one evaluation of the copy names, which TLC
    /// computes again at the substitute's first read only, where it failed.
    pub const NAMED_AT_STARTUP: i32 = 4096;
    /// Startup evaluates this definition only to preserve its EXCEPT warnings; it has no other effects.
    pub const STARTUP_WARNING_ONLY: i32 = 256;
}

#[derive(Debug, Clone, PartialEq)]
pub enum NodeKind {
    Number(i32),
    /// A number outside 32 bits, by its text.
    WideNumber(TextId),
    Decimal(TextId),
    String(TextId),
    Identifier(Name),
    Apply {
        name: Name,
        args: Vec<NodeId>,
    },
    OperatorReference(Name),
    Lambda {
        params: Vec<TextId>,
        body: NodeId,
    },
    And(Vec<NodeId>),
    Or(Vec<NodeId>),
    Prime(NodeId),
    Unchanged(NodeId),
    Enabled(NodeId),
    If {
        condition: NodeId,
        consequent: NodeId,
        alternative: NodeId,
    },
    Case {
        arms: Vec<(NodeId, NodeId)>,
        other: Option<NodeId>,
    },
    Let {
        instances: u32,
        definitions: Vec<NodeId>,
        body: NodeId,
    },
    Forall {
        bounds: Vec<Bound>,
        body: NodeId,
    },
    Exists {
        bounds: Vec<Bound>,
        body: NodeId,
    },
    UnboundedQuantifier {
        is_forall: bool,
        /// `\EE` or `\AA`, a temporal quantifier, rather than `\E x :` or `\A x :`.
        is_temporal: bool,
        names: Vec<TextId>,
        body: NodeId,
    },
    Choose {
        pattern: Pattern,
        set: Option<NodeId>,
        body: NodeId,
    },
    SetEnumeration(Vec<NodeId>),
    SetFilter {
        bound: Bound,
        predicate: NodeId,
    },
    SetMap {
        expression: NodeId,
        bounds: Vec<Bound>,
    },
    Tuple(Vec<NodeId>),
    FunctionConstruction {
        is_recursive: bool,
        bounds: Vec<Bound>,
        body: NodeId,
    },
    FunctionSet {
        domain: NodeId,
        range: NodeId,
    },
    Record(Vec<(TextId, NodeId)>),
    RecordSet(Vec<(TextId, NodeId)>),
    Except {
        function: NodeId,
        updates: Vec<Update>,
    },
    ExceptAt,
    FunctionApplication {
        function: NodeId,
        args: Vec<NodeId>,
    },
    Bracket(Vec<NodeId>),
    FieldAccess {
        record: NodeId,
        field: TextId,
    },
    Product(Vec<NodeId>),
    Always(NodeId),
    Eventually(NodeId),
    BoxAction {
        action: NodeId,
        subscript: NodeId,
    },
    AngleAction {
        action: NodeId,
        subscript: NodeId,
    },
    WeakFairness {
        subscript: NodeId,
        action: NodeId,
        enabled: Option<NodeId>,
    },
    StrongFairness {
        subscript: NodeId,
        action: NodeId,
        enabled: Option<NodeId>,
    },
    Label {
        name: TextId,
        params: Vec<TextId>,
        body: NodeId,
    },
    Subexpression(Vec<Selector>),
    /// A definition: a global one the model reaches, or one a LET defines.
    Definition(Definition),
    /// A node met again, written where it was first met.
    Reference(NodeId),
}

impl NodeKind {
    /// The expressions directly inside a node, as `collectChildren` finds them. A reference has
    /// none: it stands for the node it names.
    pub fn children(&self) -> Vec<NodeId> {
        let mut children = Vec::new();
        match self {
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
                        if let PathStep::Index(indices) = step {
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
                        Selector::Name { args, .. } | Selector::Bound(args) => {
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
}

// The tags of the blob, the positions of NODE_KINDS in ir.ts.
pub(crate) mod tag {
    pub const NUMBER: i32 = 0;
    pub const DECIMAL: i32 = 1;
    pub const STRING: i32 = 2;
    pub const IDENTIFIER: i32 = 3;
    pub const APPLY: i32 = 4;
    pub const OPERATOR_REFERENCE: i32 = 5;
    pub const LAMBDA: i32 = 6;
    pub const AND: i32 = 7;
    pub const OR: i32 = 8;
    pub const PRIME: i32 = 9;
    pub const UNCHANGED: i32 = 10;
    pub const ENABLED: i32 = 11;
    pub const IF: i32 = 12;
    pub const CASE: i32 = 13;
    pub const LET: i32 = 14;
    pub const FORALL: i32 = 15;
    pub const EXISTS: i32 = 16;
    pub const UNBOUNDED_QUANTIFIER: i32 = 17;
    pub const CHOOSE: i32 = 18;
    pub const SET_ENUMERATION: i32 = 19;
    pub const SET_FILTER: i32 = 20;
    pub const SET_MAP: i32 = 21;
    pub const TUPLE: i32 = 22;
    pub const FUNCTION_CONSTRUCTION: i32 = 23;
    pub const FUNCTION_SET: i32 = 24;
    pub const RECORD: i32 = 25;
    pub const RECORD_SET: i32 = 26;
    pub const EXCEPT: i32 = 27;
    pub const EXCEPT_AT: i32 = 28;
    pub const FUNCTION_APPLICATION: i32 = 29;
    pub const BRACKET: i32 = 30;
    pub const FIELD_ACCESS: i32 = 31;
    pub const PRODUCT: i32 = 32;
    pub const ALWAYS: i32 = 33;
    pub const EVENTUALLY: i32 = 34;
    pub const BOX_ACTION: i32 = 35;
    pub const ANGLE_ACTION: i32 = 36;
    pub const WEAK_FAIRNESS: i32 = 37;
    pub const STRONG_FAIRNESS: i32 = 38;
    pub const LABEL: i32 = 39;
    pub const SUBEXPRESSION: i32 = 40;
    pub const REFERENCE: i32 = 64;
    pub const DEFINITION: i32 = 65;
    /// The one flag a node's tag word may carry above its tag.
    pub const FLAG: i32 = 1 << 8;
    /// Where a definition's flags start in its tag word.
    pub const DEFINITION_FLAGS: i32 = 8;
}

// The numbers of the other sections.
pub(crate) mod code {
    pub const RESOLUTION_NONE: i32 = 0;
    pub const RESOLUTION_VARIABLE: i32 = 1;
    pub const RESOLUTION_CONSTANT: i32 = 2;
    pub const RESOLUTION_DEFINITION: i32 = 3;
    pub const RESOLUTION_BUILTIN: i32 = 4;
    pub const SCOPE_VALUE: i32 = 0;
    pub const SCOPE_THUNK: i32 = 1;
    pub const SCOPE_CLOSURE: i32 = 2;
    pub const SCOPE_OPAQUE: i32 = 3;
    pub const ATOM_STATE: i32 = 0;
    pub const ATOM_ACTION: i32 = 1;
    pub const ATOM_ENABLED: i32 = 2;
    pub const ENABLED_UNKNOWN: i32 = -2;
    pub const ENABLED_ALL: i32 = -1;
    pub const LIVE_FALSE: i32 = 0;
    pub const LIVE_TRUE: i32 = 1;
    pub const LIVE_STATE: i32 = 2;
    pub const LIVE_ENABLED: i32 = 3;
    pub const LIVE_ACTION: i32 = 4;
    pub const LIVE_NOT: i32 = 5;
    pub const LIVE_ALWAYS: i32 = 6;
    pub const LIVE_EVENTUALLY: i32 = 7;
    pub const LIVE_NEXT: i32 = 8;
    pub const LIVE_AND: i32 = 9;
    pub const LIVE_OR: i32 = 10;
    pub const FALSE: i32 = 0;
    pub const TRUE: i32 = 1;
    pub const INTEGER: i32 = 2;
    pub const STRING: i32 = 3;
    pub const MODEL_VALUE: i32 = 4;
    pub const SET: i32 = 5;
    pub const FUNCTION: i32 = 6;
    pub const INTERVAL_FUNCTION: i32 = 7;
}
