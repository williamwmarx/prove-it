//! The semantic nodes of SANY's `tla2sany.semantic` package that its XMLExporter writes out, with
//! the fields the export and SANY's level checking read: a port of `src/sany/nodes.ts`.
//!
//! The nodes live in one arena, `Graph`, and name each other by `NodeId`, their index in it. A
//! node's `uid` is SANY's UID, which counts every node SANY creates, some of which the graph never
//! holds (the first set of builtins), so the two differ. The sets and maps of `LevelFields` keep
//! the order of insertion, as TypeScript's `Set` and `Map` do.

use std::rc::Rc;

use crate::hash::FastMap;
use crate::ordered_map::OrderedMap;

pub type Name = Rc<str>;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct NodeId(pub u32);

/// SANY's Location: the module and the first and last characters.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SanyLocation {
    pub file: Name,
    pub begin_line: u32,
    pub begin_column: u32,
    pub end_line: u32,
    pub end_column: u32,
}

/// Where a message points: SANY's unknown location, a whole module, or a location.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MessageLocation {
    Unknown,
    Module(Name),
    At(SanyLocation),
}

/// An error or warning SANY reports.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SanyMessage {
    pub location: MessageLocation,
    pub text: String,
    pub is_warning: bool,
    /// The ErrorCode SANY files a message under, where another check files the same text.
    pub code: Option<&'static str>,
}

/// `Errors.addMessage`: SANY keeps one copy of each message.
pub fn add_sany_message(messages: &mut Vec<SanyMessage>, message: SanyMessage) {
    if !messages.contains(&message) {
        messages.push(message);
    }
}

/// `Location.toString`.
pub fn format_sany_location(location: &MessageLocation) -> String {
    match location {
        MessageLocation::Unknown => "Unknown location".to_owned(),
        MessageLocation::Module(name) => format!("In module {name}"),
        MessageLocation::At(location)
            if location.begin_line == 0
                && location.begin_column == 0
                && location.end_line == 0
                && location.end_column == 0 =>
        {
            format!("In module {}", location.file)
        }
        MessageLocation::At(location) => format!(
            "line {}, col {} to line {}, col {} of module {}",
            location.begin_line,
            location.begin_column,
            location.end_line,
            location.end_column,
            location.file
        ),
    }
}

/// An insertion-ordered set of nodes, as a TypeScript `Set<SymbolNode>`.
pub type NodeSet = OrderedMap<NodeId, ()>;

/// SANY's ArgLevelParam: the level of argument `index` of operator `op` depends on `param`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ArgLevelParam {
    pub op: NodeId,
    pub index: usize,
    pub param: NodeId,
}

/// SANY's ParamAndPosition with its level in a SetOfArgLevelConstraints: the argument at
/// `position` of operator `param` must be allowed a level of at least `level`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ArgLevelConstraint {
    pub param: NodeId,
    pub position: usize,
    pub level: u8,
}

/// The fields of SANY's LevelNode. `level_checked` is 0 until levelCheck runs, and SANY exports a
/// level only for the nodes it has level-checked. The keys of `arg_level_params` are TypeScript's
/// `${op.id}:${index}:${param.id}`, and those of `arg_level_constraints` `${param.id}:${position}`.
#[derive(Clone, Debug, Default)]
pub struct LevelFields {
    pub level_checked: u32,
    pub level: u8,
    pub level_params: NodeSet,
    pub all_params: NodeSet,
    pub non_leibniz_params: NodeSet,
    pub arg_level_params: OrderedMap<ArgLevelParam, ArgLevelParam>,
    pub level_correct: bool,
    /// SetOfLevelConstraints: the highest level each parameter may have.
    pub level_constraints: OrderedMap<NodeId, u8>,
    pub arg_level_constraints: OrderedMap<(NodeId, usize), ArgLevelConstraint>,
}

/// SANY's kinds of declared symbols, from `tla2sany.semantic.ASTConstants`.
pub const CONSTANT_DECL_KIND: u32 = 2;
pub const VARIABLE_DECL_KIND: u32 = 3;
pub const NEW_CONSTANT_KIND: u32 = 24;

#[derive(Clone, Debug)]
pub struct FormalParam {
    pub name: Name,
    pub arity: usize,
    pub location: Option<SanyLocation>,
}

#[derive(Clone, Debug)]
pub struct OpDecl {
    pub name: Name,
    pub arity: usize,
    pub decl_kind: u32,
    pub location: SanyLocation,
    pub module: NodeId,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DefKind {
    UserDefined,
    BuiltIn,
    ModuleInstance,
    NumberedProofStep,
}

#[derive(Clone, Debug)]
pub struct OpDef {
    pub def_kind: DefKind,
    pub name: Name,
    pub arity: usize,
    pub params: Option<Vec<NodeId>>,
    pub body: Option<NodeId>,
    pub is_local: bool,
    pub location: SanyLocation,
    pub module: Option<NodeId>,
    pub source: Option<NodeId>,
    pub pre_comments: Vec<String>,
    pub is_defined: bool,
    pub in_recursive: bool,
    pub in_recursive_section: bool,
    pub recursive_section: i32,
    pub let_in_level: u32,
    pub weights: Vec<u8>,
    pub is_leibniz_arg: Option<Vec<bool>>,
    pub is_leibniz: bool,
    pub op_level_cond: Option<Vec<Vec<Vec<bool>>>>,
    pub max_levels: Vec<u8>,
    pub min_max_level: Option<Vec<Vec<u8>>>,
    pub labels: OrderedMap<Name, NodeId>,
    /// The DEFINE, USE, HIDE or INSTANCE step that a NumberedProofStep definition names.
    pub step: Option<NodeId>,
}

#[derive(Clone, Debug)]
pub struct ThmOrAssumpDef {
    pub name: Name,
    pub is_theorem: bool,
    pub body: NodeId,
    pub params: Vec<NodeId>,
    pub is_local: bool,
    pub location: SanyLocation,
    pub module: NodeId,
    pub source: Option<NodeId>,
    pub labels: OrderedMap<Name, NodeId>,
    pub is_leibniz_arg: Vec<bool>,
    pub is_leibniz: bool,
    pub op_level_cond: Vec<Vec<Vec<bool>>>,
    pub max_levels: Vec<u8>,
    pub min_max_level: Vec<Vec<u8>>,
}

/// A module. Its level fields are the node's `LevelFields` (`level_correct`, `arg_level_params`,
/// `level_constraints`, `arg_level_constraints`).
#[derive(Clone, Debug)]
pub struct Module {
    pub name: Name,
    pub location: SanyLocation,
    pub extendees: Vec<NodeId>,
    pub context: Context,
    pub top_level: Vec<NodeId>,
    pub definitions: Vec<NodeId>,
    pub op_defs_in_recursive_section: Vec<NodeId>,
    pub is_level_checked: bool,
    /// ModuleNode.getRecords: the record constructors and sets of records generated for it.
    pub records: Vec<NodeId>,
}

#[derive(Clone, Debug)]
pub struct OpAppl {
    pub operator: NodeId,
    pub operands: Vec<Option<NodeId>>,
    pub unbounded: Option<Vec<NodeId>>,
    pub bounded: Option<Vec<Vec<NodeId>>>,
    pub tuple_ors: Option<Vec<bool>>,
    pub ranges: Vec<NodeId>,
    pub location: SanyLocation,
    /// Generator.nullOAN, whose operator, nullODN, has no kind the XMLExporter can export.
    pub is_null: bool,
    /// The null SANY generates for an operator it cannot resolve.
    pub is_absent: bool,
}

#[derive(Clone, Debug)]
pub struct Decimal {
    pub mantissa: String,
    pub exponent: String,
    pub integral_part: String,
    pub fractional_part: String,
    pub location: SanyLocation,
}

#[derive(Clone, Debug)]
pub struct LetIn {
    pub op_defs: Vec<NodeId>,
    pub instances: Vec<NodeId>,
    pub body: NodeId,
    pub context: Context,
    pub location: SanyLocation,
}

#[derive(Clone, Debug)]
pub struct Label {
    pub name: Name,
    pub params: Vec<NodeId>,
    pub body: NodeId,
    pub labels: OrderedMap<Name, NodeId>,
    pub is_assume_prove: bool,
    pub location: SanyLocation,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Subst {
    pub op: NodeId,
    pub expr: NodeId,
    pub is_implicit: bool,
}

#[derive(Clone, Debug)]
pub struct SubstIn {
    /// APSubstIn, whose body is an ASSUME/PROVE, rather than SubstIn.
    pub is_assume_prove: bool,
    pub substs: Vec<Subst>,
    pub body: NodeId,
    pub instantiating_module: NodeId,
    pub instantiated_module: NodeId,
    pub location: SanyLocation,
}

#[derive(Clone, Debug)]
pub struct Instance {
    pub name: Option<Name>,
    pub is_local: bool,
    pub params: Vec<NodeId>,
    pub module: NodeId,
    pub substs: Vec<Subst>,
    pub location: SanyLocation,
}

#[derive(Clone, Debug)]
pub struct Theorem {
    pub definition: Option<NodeId>,
    pub body: NodeId,
    pub proof: Option<NodeId>,
    pub is_suffices: bool,
    pub location: SanyLocation,
}

#[derive(Clone, Debug)]
pub struct LeafProof {
    pub facts: Vec<NodeId>,
    pub defs: Vec<NodeId>,
    pub is_omitted: bool,
    pub is_only: bool,
    pub location: SanyLocation,
}

#[derive(Clone, Debug)]
pub struct NonLeafProof {
    pub steps: Vec<NodeId>,
    pub instances: Vec<NodeId>,
    pub proof_level: u32,
    pub location: SanyLocation,
}

#[derive(Clone, Debug)]
pub struct AssumeProve {
    pub assumptions: Vec<NodeId>,
    pub goal: NodeId,
    pub is_suffices: bool,
    pub is_boxed: bool,
    pub location: SanyLocation,
}

#[derive(Clone, Debug)]
pub struct UseOrHide {
    pub facts: Vec<NodeId>,
    pub defs: Vec<NodeId>,
    pub is_only: bool,
    pub is_hide: bool,
    pub location: SanyLocation,
}

/// A node's kind with its own fields, one variant per interface of `nodes.ts`.
#[derive(Clone, Debug)]
pub enum NodeKind {
    FormalParam(FormalParam),
    OpDecl(OpDecl),
    OpDef(Box<OpDef>),
    ThmOrAssumpDef(Box<ThmOrAssumpDef>),
    Module(Box<Module>),
    OpAppl(OpAppl),
    Numeral {
        value: String,
        location: SanyLocation,
    },
    String {
        value: String,
        location: SanyLocation,
    },
    Decimal(Decimal),
    LetIn(LetIn),
    Label(Label),
    OpArg {
        op: NodeId,
        location: SanyLocation,
    },
    At {
        except: NodeId,
        component: NodeId,
        location: SanyLocation,
    },
    SubstIn(SubstIn),
    Instance(Instance),
    Assume {
        definition: Option<NodeId>,
        body: NodeId,
        location: SanyLocation,
    },
    Theorem(Theorem),
    LeafProof(LeafProof),
    DefStep {
        defs: Vec<NodeId>,
        location: SanyLocation,
    },
    NonLeafProof(NonLeafProof),
    NewSymb {
        declaration: NodeId,
        set: Option<NodeId>,
        location: SanyLocation,
    },
    AssumeProve(AssumeProve),
    UseOrHide(UseOrHide),
}

#[derive(Clone, Debug)]
pub struct Node {
    /// SANY's UID.
    pub uid: u32,
    pub levels: LevelFields,
    pub kind: NodeKind,
}

impl Node {
    /// The node's name, for the symbols: FormalParam, OpDecl, OpDef, ThmOrAssumpDef and Module.
    pub fn symbol_name(&self) -> Option<&Name> {
        match &self.kind {
            NodeKind::FormalParam(node) => Some(&node.name),
            NodeKind::OpDecl(node) => Some(&node.name),
            NodeKind::OpDef(node) => Some(&node.name),
            NodeKind::ThmOrAssumpDef(node) => Some(&node.name),
            NodeKind::Module(node) => Some(&node.name),
            _ => None,
        }
    }

    pub fn is_symbol(&self) -> bool {
        self.symbol_name().is_some()
    }

    /// The node's location, where it has one (a FormalParam may not).
    pub fn location(&self) -> Option<&SanyLocation> {
        match &self.kind {
            NodeKind::FormalParam(node) => node.location.as_ref(),
            NodeKind::OpDecl(node) => Some(&node.location),
            NodeKind::OpDef(node) => Some(&node.location),
            NodeKind::ThmOrAssumpDef(node) => Some(&node.location),
            NodeKind::Module(node) => Some(&node.location),
            NodeKind::OpAppl(node) => Some(&node.location),
            NodeKind::Numeral { location, .. }
            | NodeKind::String { location, .. }
            | NodeKind::OpArg { location, .. }
            | NodeKind::At { location, .. }
            | NodeKind::Assume { location, .. }
            | NodeKind::DefStep { location, .. }
            | NodeKind::NewSymb { location, .. } => Some(location),
            NodeKind::Decimal(node) => Some(&node.location),
            NodeKind::LetIn(node) => Some(&node.location),
            NodeKind::Label(node) => Some(&node.location),
            NodeKind::SubstIn(node) => Some(&node.location),
            NodeKind::Instance(node) => Some(&node.location),
            NodeKind::Theorem(node) => Some(&node.location),
            NodeKind::LeafProof(node) => Some(&node.location),
            NodeKind::NonLeafProof(node) => Some(&node.location),
            NodeKind::AssumeProve(node) => Some(&node.location),
            NodeKind::UseOrHide(node) => Some(&node.location),
        }
    }

    /// `getSymbolArity`.
    pub fn symbol_arity(&self) -> usize {
        match &self.kind {
            NodeKind::FormalParam(node) => node.arity,
            NodeKind::OpDecl(node) => node.arity,
            NodeKind::OpDef(node) => node.arity,
            NodeKind::ThmOrAssumpDef(node) => node.params.len(),
            _ => 0,
        }
    }

    /// `isAbsent`.
    pub fn is_absent(&self) -> bool {
        matches!(&self.kind, NodeKind::OpAppl(node) if node.is_absent)
    }
}

/// The arena of a specification's nodes.
#[derive(Clone, Debug, Default)]
pub struct Graph {
    pub nodes: Vec<Node>,
}

impl Graph {
    /// Adds a node with SANY's UID `uid` and fresh level fields.
    pub fn add(&mut self, uid: u32, kind: NodeKind) -> NodeId {
        let id = NodeId(u32::try_from(self.nodes.len()).expect("fewer than 2^32 nodes"));
        self.nodes.push(Node {
            uid,
            levels: LevelFields::default(),
            kind,
        });
        id
    }

    pub fn node(&self, id: NodeId) -> &Node {
        &self.nodes[id.0 as usize]
    }

    pub fn node_mut(&mut self, id: NodeId) -> &mut Node {
        &mut self.nodes[id.0 as usize]
    }

    pub fn kind(&self, id: NodeId) -> &NodeKind {
        &self.node(id).kind
    }

    pub fn levels(&self, id: NodeId) -> &LevelFields {
        &self.node(id).levels
    }

    pub fn levels_mut(&mut self, id: NodeId) -> &mut LevelFields {
        &mut self.node_mut(id).levels
    }

    pub fn op_def(&self, id: NodeId) -> Option<&OpDef> {
        match &self.node(id).kind {
            NodeKind::OpDef(node) => Some(node),
            _ => None,
        }
    }

    pub fn op_def_mut(&mut self, id: NodeId) -> Option<&mut OpDef> {
        match &mut self.node_mut(id).kind {
            NodeKind::OpDef(node) => Some(node),
            _ => None,
        }
    }

    pub fn module(&self, id: NodeId) -> Option<&Module> {
        match &self.node(id).kind {
            NodeKind::Module(node) => Some(node),
            _ => None,
        }
    }

    pub fn module_mut(&mut self, id: NodeId) -> Option<&mut Module> {
        match &mut self.node_mut(id).kind {
            NodeKind::Module(node) => Some(node),
            _ => None,
        }
    }

    /// `addToContext` of the symbol `symbol` to the context of `module`.
    pub fn add_to_module_context(&mut self, module: NodeId, symbol: NodeId) {
        let (key, hash_key) = get_symbol_key(self.node(symbol));
        let module = self.module_mut(module).expect("a module");
        module.context.add(key, &hash_key, symbol);
    }

    /// `ModuleNode.getOpDefs`: the definitions in the order they joined the context, without
    /// builtins and module instances.
    pub fn get_op_defs(&self, module: NodeId) -> Vec<NodeId> {
        let context = &self.module(module).expect("a module").context;
        context
            .symbols
            .iter()
            .copied()
            .filter(|&symbol| {
                matches!(&self.node(symbol).kind,
                    NodeKind::OpDef(node) if node.def_kind == DefKind::UserDefined)
            })
            .collect()
    }

    /// `ModuleNode.getConstantDecls` and `getVariableDecls`, which reverse the Hashtable's order.
    pub fn get_declarations(&self, module: NodeId, decl_kind: u32) -> Vec<NodeId> {
        let context = &self.module(module).expect("a module").context;
        let mut declarations: Vec<NodeId> = context
            .get_hashtable_values()
            .into_iter()
            .filter(|&symbol| {
                matches!(&self.node(symbol).kind,
                    NodeKind::OpDecl(node) if node.decl_kind == decl_kind)
            })
            .collect();
        declarations.reverse();
        declarations
    }

    pub fn get_thm_or_assump_defs(&self, module: NodeId) -> Vec<NodeId> {
        let context = &self.module(module).expect("a module").context;
        context
            .symbols
            .iter()
            .copied()
            .filter(|&symbol| matches!(&self.node(symbol).kind, NodeKind::ThmOrAssumpDef(_)))
            .collect()
    }
}

/// The key a symbol has in a context, and the name its hash is of: a module's key is apart from
/// the other symbols' so that a module and an operator may share a name.
pub fn get_symbol_key(symbol: &Node) -> (Name, Name) {
    let name = symbol.symbol_name().expect("a symbol").clone();
    match &symbol.kind {
        NodeKind::Module(_) => (Rc::from(format!("{MODULE_KEY_PREFIX}{name}")), name),
        _ => (name.clone(), name),
    }
}

const MODULE_KEY_PREFIX: &str = "\u{0}module ";

/// `java.lang.String.hashCode`, over UTF-16 code units.
pub fn get_java_hash(text: &str) -> i32 {
    text.encode_utf16().fold(0i32, |hash, unit| {
        hash.wrapping_mul(31).wrapping_add(i32::from(unit))
    })
}

#[derive(Clone, Debug)]
struct HashtableEntry {
    hash: i32,
    value: NodeId,
}

/// SANY's Context: a `java.util.Hashtable` from names to symbols, whose iteration order SANY's
/// lists of constants, variables and instantiated definitions follow, and the symbols in the order
/// they were added. The buckets hold entries' indices in Java's order; `positions` finds an entry
/// by its key and is never iterated.
#[derive(Clone, Debug)]
pub struct Context {
    buckets: Vec<Vec<usize>>,
    entries: Vec<HashtableEntry>,
    positions: FastMap<Name, usize>,
    threshold: usize,
    pub symbols: Vec<NodeId>,
}

impl Default for Context {
    /// A `java.util.Hashtable` with its default capacity of 11 and load factor of 0.75.
    fn default() -> Self {
        Context {
            buckets: vec![Vec::new(); 11],
            entries: Vec::new(),
            positions: FastMap::default(),
            threshold: 8,
            symbols: Vec::new(),
        }
    }
}

fn get_bucket_index(hash: i32, length: usize) -> usize {
    (hash & 0x7fff_ffff) as usize % length
}

impl Context {
    fn rehash(&mut self) {
        let capacity = self.buckets.len() * 2 + 1;
        let mut buckets = vec![Vec::new(); capacity];
        for bucket in self.buckets.iter().rev() {
            for &entry in bucket {
                let index = get_bucket_index(self.entries[entry].hash, capacity);
                buckets[index].insert(0, entry);
            }
        }
        self.buckets = buckets;
        self.threshold = capacity * 3 / 4;
    }

    /// `putHashtableValue`: a key always comes with the same `hash_key`, its symbol's name.
    fn put(&mut self, key: Name, hash_key: &str, value: NodeId) {
        if let Some(&position) = self.positions.get(&key) {
            self.entries[position].value = value;
            return;
        }
        if self.positions.len() >= self.threshold {
            self.rehash();
        }
        let hash = get_java_hash(hash_key);
        let position = self.entries.len();
        self.entries.push(HashtableEntry { hash, value });
        let bucket = get_bucket_index(hash, self.buckets.len());
        self.buckets[bucket].insert(0, position);
        self.positions.insert(key, position);
    }

    /// `addToContext`, given the symbol's key and name (`get_symbol_key`).
    pub fn add(&mut self, key: Name, hash_key: &str, symbol: NodeId) {
        self.put(key, hash_key, symbol);
        self.symbols.push(symbol);
    }

    /// `getContextSymbol`.
    pub fn get_symbol(&self, name: &str) -> Option<NodeId> {
        self.positions
            .get(name)
            .map(|&position| self.entries[position].value)
    }

    /// `getContextModule`.
    pub fn get_module(&self, name: &str) -> Option<NodeId> {
        self.get_symbol(&format!("{MODULE_KEY_PREFIX}{name}"))
    }

    /// The values in the order of `Hashtable.elements()`, from the last bucket to the first.
    pub fn get_hashtable_values(&self) -> Vec<NodeId> {
        self.buckets
            .iter()
            .rev()
            .flat_map(|bucket| bucket.iter().map(|&entry| self.entries[entry].value))
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn java_hash_matches_string_hash_code() {
        assert_eq!(get_java_hash(""), 0);
        assert_eq!(get_java_hash("a"), 97);
        assert_eq!(get_java_hash("Init"), 2_283_824);
        assert_eq!(get_java_hash("polygenelubricants"), i32::MIN);
    }

    #[test]
    fn hashtable_enumerates_as_java_does() {
        // Ten keys rehash the table once; the order is what `getHashtableValues` gives.
        let mut context = Context::default();
        let names = [
            "x", "y", "z", "Init", "Next", "Spec", "TypeOK", "vars", "a", "b",
        ];
        for (index, name) in names.iter().enumerate() {
            context.add(Rc::from(*name), name, NodeId(index as u32));
        }
        let values: Vec<u32> = context
            .get_hashtable_values()
            .iter()
            .map(|id| id.0)
            .collect();
        assert_eq!(values, [5, 6, 3, 7, 2, 9, 1, 8, 0, 4]);
        assert_eq!(context.get_symbol("Next"), Some(NodeId(4)));
    }
}
