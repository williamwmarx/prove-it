//! A port of `src/sany/generator.ts`: the semantic graph SANY builds for a specification and its
//! modules, in the order SANY analyzes them, with SANY's UIDs.
//!
//! `generateSanySpecification`'s loader is `Loader`, its state across modules `SpecGenerator`, and
//! the closures of `generateModule` are the methods of `ModuleGenerator`: those of the first part
//! of `generateModule` here, its expressions in `expressions.rs`, its definitions, instances and
//! units in `definitions.rs`, and its proofs in `proofs.rs`.

mod definitions;
mod expressions;
mod proofs;

use std::rc::Rc;
use std::sync::OnceLock;

use crate::TlcVersion;
use crate::ast::{
    Assumed, Bound, BoundPattern, Expr, Expression, ExpressionKind, Location, Module, ModuleUnit,
    Position, Statement, SymbolLevel,
};
use crate::hash::{FastMap, FastSet};
use crate::levels::TEMPORAL_LEVEL;
use crate::ordered_map::OrderedMap;
use crate::sany::builtins::{create_builtins, get_builtin_location};
use crate::sany::nodes::{
    CONSTANT_DECL_KIND, Context, DefKind, FormalParam, Graph, MessageLocation, NEW_CONSTANT_KIND,
    Name, Node, NodeId, NodeKind, OpAppl, OpDef, SanyLocation, SanyMessage, SubstIn,
    VARIABLE_DECL_KIND, add_sany_message, format_sany_location, get_symbol_key,
};
use crate::sany::selectors::{
    SelectorGenerator, SelectorItem, SelectorOp, get_selector_items, is_general_id,
    selector_to_node,
};
use crate::sany::source::{
    SanyReading, SanyReadings, SourceFile, TokenSpan, create_source_file, find_name_tokens,
    find_token, get_argument_span, get_expression_span, get_matching_index, get_pre_comments,
    get_range_span, get_span_location, get_token_index, get_token_location, is_token,
    read_sany_text,
};
use crate::sany::{Result, SanySpecification, not_yet};
use crate::sany_parse_error::get_sany_parse_error;
use crate::tlc_data::SANY_OPERATOR_SYNONYMS;

/// The canonical name of each synonym, the later one where two lists name the same synonym.
fn get_synonyms() -> &'static FastMap<&'static str, &'static str> {
    static SYNONYMS: OnceLock<FastMap<&'static str, &'static str>> = OnceLock::new();
    SYNONYMS.get_or_init(|| {
        SANY_OPERATOR_SYNONYMS
            .iter()
            .flat_map(|synonyms| synonyms[1..].iter().map(|synonym| (*synonym, synonyms[0])))
            .collect()
    })
}

/// `resolveSynonym`: tla2sany.parser.Operators.resolveSynonym, applied to each part of a name like
/// I!\cup.
fn resolve_synonym(name: &str) -> Name {
    let parts: Vec<&str> = name
        .split('!')
        .map(|part| {
            get_synonyms()
                .get(part)
                .copied()
                .unwrap_or(if part == "~" { "\\lnot" } else { part })
        })
        .collect();
    Rc::from(parts.join("!"))
}

/// `AssumeProveScope`: the fields of SANY's AssumeProveNode that tell whether a reference to a
/// clause lies in the scope of a declaration in the clauses before it. See AssumeProveNode.java.
/// `is_declared_before[i]` is AssumeProveNode.inScopeOfDecl: whether any of the first i clauses is
/// a NEW. `has_goal` tells whether the ASSUME/PROVE is the statement of a named theorem or step,
/// whose `is_suffices` and `is_in_proof` decide where its declarations are visible.
#[derive(Clone, Debug)]
struct AssumeProveScope {
    is_declared_before: Vec<bool>,
    has_goal: bool,
    is_suffices: bool,
    is_in_proof: bool,
}

/// An `AssumeProveScope` in `ModuleGenerator::scopes`, which the TypeScript shares by reference.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ScopeId(usize);

/// `AssumeProveState`: Generator.assumeProveDepth, inScopeOfAPDecl, currentGoal and
/// currentGoalClause, where the generator is among nested ASSUME/PROVEs: the depth, whether each
/// level declares a symbol, and the goal and clause a label lies in.
#[derive(Clone, Debug, Default)]
struct AssumeProveState {
    depth: usize,
    is_declared: Vec<bool>,
    goal: Option<ScopeId>,
    goal_clause: usize,
}

/// `LabelGoal`.
#[derive(Clone, Copy, Debug)]
struct LabelGoal {
    scope: ScopeId,
    clause: usize,
}

/// `NEW_SYMBOL_KINDS`: the declaration kind and level of a NEW symbol of each level.
#[expect(dead_code, reason = "generate_new_symbol in proofs.rs is a stub")]
fn get_new_symbol_kind(level: SymbolLevel) -> (u32, u8) {
    match level {
        SymbolLevel::Constant => (NEW_CONSTANT_KIND, 0),
        SymbolLevel::Variable => (25, 1),
        SymbolLevel::State => (26, 1),
        SymbolLevel::Action => (27, 2),
        SymbolLevel::Temporal => (28, 3),
    }
}

/// `isIdentifier`: whether SANY names an operator by an identifier rather than by a symbol.
fn is_identifier(name: &str) -> bool {
    !name.is_empty()
        && name
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
}

/// `isSelector`: whether an operator name selects through an instance, as M!Op does, unlike the
/// infix !!.
fn is_selector(name: &str) -> bool {
    name != "!!" && name.contains('!')
}

/// What `generate_sany_specification` takes besides the texts (`SanyGenerationOptions`).
/// `root_file_name` is the name of the root module's file, which SANY requires to match the
/// module's name, and `root_file_path` the path SANY's caller gives it, which SANY names when it
/// cannot parse the file. `root_extendees` are the modules TLC adds to the root module's EXTENDS
/// for its post conditions. `on_module` is called after each external module, in the order SANY
/// analyzes them, with the graph, the module and the messages so far, for SANY's level check.
#[derive(Default)]
pub struct GenerationOptions<'a> {
    pub root_file_name: Option<Name>,
    pub root_file_path: Option<String>,
    pub root_extendees: Option<Vec<Name>>,
    pub on_module: Option<&'a ModuleHook>,
}

/// `onModule`: what runs after SANY generates a module, given the graph, the module and the
/// messages so far.
pub type ModuleHook = dyn Fn(&mut Graph, NodeId, &mut Vec<SanyMessage>);

/// `ModuleDependencies`: the modules a file extends and instantiates, as SANY's ParseUnit collects
/// them, and the module of that file which first names each.
#[derive(Default)]
pub(crate) struct ModuleDependencies {
    pub(crate) extendees: Vec<Name>,
    pub(crate) instancees: Vec<Name>,
    pub(crate) importers: FastMap<Name, Name>,
}

/// A context of the symbol table: a module's, which the module's node holds, or one of the
/// generator's own. `is_assume` marks the contexts in which SANY's $$InAssume marks the scope of
/// an ordinary ASSUME's assumptions (`assumeContexts`), and travels with the context.
#[derive(Clone, Debug)]
enum ContextSlot {
    Module(NodeId),
    Local(LocalContext),
}

#[derive(Clone, Debug, Default)]
struct LocalContext {
    context: Context,
    #[expect(dead_code, reason = "generate_assume_prove in proofs.rs is a stub")]
    is_assume: bool,
}

/// `SymbolTable`.
#[derive(Clone, Debug, Default)]
struct SymbolTable {
    contexts: Vec<ContextSlot>,
}

/// `BoundSymbols`.
#[derive(Clone, Debug, Default)]
struct BoundSymbols {
    bounded: Vec<Vec<NodeId>>,
    tuple_ors: Vec<bool>,
    ranges: Vec<NodeId>,
}

/// `OpApplBinding`.
#[derive(Clone, Debug, Default)]
struct OpApplBinding {
    unbounded: Option<Vec<NodeId>>,
    bounded: Option<Vec<Vec<NodeId>>>,
    tuple_ors: Option<Vec<bool>>,
    ranges: Option<Vec<NodeId>>,
}

impl From<BoundSymbols> for OpApplBinding {
    fn from(bounds: BoundSymbols) -> OpApplBinding {
        OpApplBinding {
            unbounded: None,
            bounded: Some(bounds.bounded),
            tuple_ors: Some(bounds.tuple_ors),
            ranges: Some(bounds.ranges),
        }
    }
}

/// `UnresolvedName`: a module name that SpecObj.loadSpec has yet to resolve, with the module that
/// imports it and the module of that file whose EXTENDS or INSTANCE names it.
struct UnresolvedName {
    name: Name,
    importer: Name,
    naming_module: Name,
}

/// `resolveSymbol` over a context of the symbol table.
fn get_slot_context<'g>(graph: &'g Graph, slot: &'g ContextSlot) -> &'g Context {
    match slot {
        ContextSlot::Module(module) => &graph.module(*module).expect("a module").context,
        ContextSlot::Local(local) => &local.context,
    }
}

/// `addToContext`.
fn add_to_context(graph: &Graph, context: &mut Context, symbol: NodeId) {
    let (key, hash_key) = get_symbol_key(graph.node(symbol));
    context.add(key, &hash_key, symbol);
}

/// `getSymbolArity`, which is -1 for a builtin that takes any number of arguments: a builtin
/// without `params`.
fn get_symbol_arity(graph: &Graph, symbol: NodeId) -> i32 {
    match graph.kind(symbol) {
        NodeKind::OpDef(definition)
            if definition.def_kind == DefKind::BuiltIn && definition.params.is_none() =>
        {
            -1
        }
        _ => i32::try_from(graph.node(symbol).symbol_arity()).expect("an arity below 2^31"),
    }
}

/// `getSymbolKind`: SANY's kind of a symbol, which a symbol that takes another's name must share.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SymbolKind {
    FormalParam,
    OpDecl(u32),
    OpDef(DefKind),
    ThmOrAssumpDef,
    Module,
    Other,
}

fn get_symbol_kind(symbol: &Node) -> SymbolKind {
    match &symbol.kind {
        NodeKind::FormalParam(_) => SymbolKind::FormalParam,
        NodeKind::OpDecl(declaration) => SymbolKind::OpDecl(declaration.decl_kind),
        NodeKind::OpDef(definition) => SymbolKind::OpDef(definition.def_kind),
        NodeKind::ThmOrAssumpDef(_) => SymbolKind::ThmOrAssumpDef,
        NodeKind::Module(_) => SymbolKind::Module,
        _ => SymbolKind::Other,
    }
}

/// `getKindName`: Context.kindOfNode.
#[expect(dead_code, reason = "process_extends_list in definitions.rs is a stub")]
fn get_kind_name(symbol: &Node) -> &'static str {
    match &symbol.kind {
        NodeKind::OpDef(_) | NodeKind::FormalParam(_) => "definition",
        _ => "declaration",
    }
}

/// `isSameOrigin`: SymbolNode.sameOriginallyDefinedInModule, two symbols are the same definition
/// of a module without parameters.
fn is_same_origin(graph: &Graph, symbol: NodeId, other: NodeId) -> bool {
    match (graph.kind(symbol), graph.kind(other)) {
        (NodeKind::OpDef(definition), NodeKind::OpDef(other_definition)) => {
            let source = definition.source.unwrap_or(symbol);
            if source != other_definition.source.unwrap_or(other) {
                return false;
            }
            graph
                .op_def(source)
                .and_then(|source| source.module)
                .is_none_or(|module| is_parameter_free(graph, module))
        }
        (NodeKind::ThmOrAssumpDef(definition), NodeKind::ThmOrAssumpDef(other_definition)) => {
            let source = definition.source.unwrap_or(symbol);
            let NodeKind::ThmOrAssumpDef(source_definition) = graph.kind(source) else {
                return false;
            };
            source == other_definition.source.unwrap_or(other)
                && is_parameter_free(graph, source_definition.module)
        }
        _ => false,
    }
}

/// `isParameterFree`.
fn is_parameter_free(graph: &Graph, module: NodeId) -> bool {
    let context = &graph.module(module).expect("a module").context;
    !context.get_hashtable_values().into_iter().any(|symbol| {
        matches!(graph.kind(symbol), NodeKind::OpDecl(declaration)
            if declaration.decl_kind == CONSTANT_DECL_KIND
                || declaration.decl_kind == VARIABLE_DECL_KIND)
    })
}

/// `getLetInstances`: the modules the LET instances of an expression instantiate.
fn get_let_instances(expression: &Expr, found: &mut Vec<Name>) {
    if let ExpressionKind::Let {
        instances: Some(instances),
        ..
    } = &expression.kind
    {
        found.extend(instances.iter().map(|instance| instance.module.clone()));
    }
    expression
        .children()
        .iter()
        .for_each(|child| get_let_instances(child, found));
}

/// `getStatementInstances`: those of a theorem or assumption's statement.
fn get_assumed_instances(assumed: &Assumed, found: &mut Vec<Name>) {
    match assumed {
        Assumed::Expression(expression) => get_let_instances(expression, found),
        Assumed::NewSymbol(_) => {}
        Assumed::AssumeProve(assume_prove) => {
            assume_prove
                .assumptions
                .iter()
                .for_each(|assumption| get_assumed_instances(assumption, found));
            get_let_instances(&assume_prove.conclusion, found);
        }
    }
}

/// `isInternalInstance`: SpecObj.instanceResolvesToInternalModule, SANY finds a module that the
/// root module instantiates among its inner modules only when its first top-level INSTANCE of the
/// module follows the inner module, and otherwise looks for a file.
fn is_internal_instance(module: &Module, name: &str) -> bool {
    let mut seen: FastSet<&str> = FastSet::default();
    for unit in &module.units {
        match unit {
            ModuleUnit::Module(inner) => {
                seen.insert(&inner.name);
            }
            ModuleUnit::Instance(instance) if &*instance.module == name => {
                return seen.contains(name);
            }
            _ => {}
        }
    }
    false
}

/// `getNumeralDigits`: the decimal digits of a numeral such as \hFF, which SANY keeps at any size.
fn get_numeral_digits(text: &str) -> String {
    const LIMB: u64 = 1_000_000_000;
    let (radix, digits) = match text.strip_prefix('\\') {
        Some(based) => {
            let radix = match based.bytes().next().map(|byte| byte.to_ascii_lowercase()) {
                Some(b'b') => 2,
                Some(b'o') => 8,
                _ => 16,
            };
            (radix, based.get(1..).unwrap_or(""))
        }
        None => (10, text),
    };
    // Little-endian limbs of nine decimal digits.
    let mut limbs: Vec<u64> = vec![0];
    for digit in digits.chars() {
        let mut carry = u64::from(digit.to_digit(radix).unwrap_or(0));
        for limb in &mut limbs {
            let value = *limb * u64::from(radix) + carry;
            *limb = value % LIMB;
            carry = value / LIMB;
        }
        if carry > 0 {
            limbs.push(carry);
        }
    }
    let mut decimal = limbs.last().expect("a limb").to_string();
    for limb in limbs.iter().rev().skip(1) {
        decimal.push_str(&format!("{limb:09}"));
    }
    decimal
}

/// `LabelScope`: an entry of SANY's LS stack, the labels of a definition, theorem or label and the
/// parameters bound within it around the expression being generated.
#[derive(Clone, Debug, Default)]
struct LabelScope {
    labels: OrderedMap<Name, NodeId>,
    params: Vec<Vec<NodeId>>,
}

/// `getDependencies`: ParseUnit.calculateContextWithinParseUnit lets a module know the inner
/// modules defined before it in the modules enclosing it and the inner modules of the modules it
/// extends, but not itself. SANY looks at a module's own EXTENDS and INSTANCEs before those of its
/// inner modules.
pub(crate) fn get_dependencies(module: &Rc<Module>) -> ModuleDependencies {
    fn visit(
        current: &Rc<Module>,
        is_root: bool,
        context: &FastMap<Name, Rc<Module>>,
        dependencies: &mut ModuleDependencies,
    ) {
        let is_external = |name: &Name| !context.contains_key(name);
        let mut add_imports = |names: Vec<Name>, is_extension: bool| {
            for name in names {
                dependencies
                    .importers
                    .entry(name.clone())
                    .or_insert_with(|| current.name.clone());
                if is_extension {
                    dependencies.extendees.push(name);
                } else {
                    dependencies.instancees.push(name);
                }
            }
        };
        add_imports(
            current
                .extends
                .iter()
                .filter(|name| is_external(name))
                .cloned()
                .collect(),
            true,
        );
        let mut instances = Vec::new();
        for unit in &current.units {
            match unit {
                ModuleUnit::Instance(instance) => instances.push(instance.module.clone()),
                ModuleUnit::Definition(definition) => {
                    get_let_instances(&definition.body, &mut instances)
                }
                ModuleUnit::Theorem(theorem) if is_root => match &theorem.statement {
                    Statement::Expression(expression) => {
                        get_let_instances(expression, &mut instances)
                    }
                    Statement::AssumeProve(assume_prove) => get_assumed_instances(
                        &Assumed::AssumeProve(assume_prove.clone()),
                        &mut instances,
                    ),
                },
                ModuleUnit::Assumption(assumption) if is_root => {
                    get_let_instances(&assumption.expression, &mut instances)
                }
                _ => {}
            }
        }
        add_imports(
            instances
                .into_iter()
                .filter(|name| is_external(name) && !is_internal_instance(current, name))
                .collect(),
            false,
        );
        let mut peers = context.clone();
        for inner in &current.modules {
            let mut inner_context = peers.clone();
            // ParseUnit.handleExtensions.
            let mut extenders: Vec<*const Module> = Vec::new();
            fn add_extended_inner_modules(
                extender: &Rc<Module>,
                extenders: &mut Vec<*const Module>,
                inner_context: &mut FastMap<Name, Rc<Module>>,
            ) {
                if extenders.contains(&Rc::as_ptr(extender)) {
                    return;
                }
                extenders.push(Rc::as_ptr(extender));
                for name in &extender.extends {
                    let Some(extendee) = inner_context.get(name).cloned() else {
                        continue;
                    };
                    for extendee_inner in &extendee.modules {
                        inner_context
                            .entry(extendee_inner.name.clone())
                            .or_insert_with(|| extendee_inner.clone());
                    }
                    add_extended_inner_modules(&extendee, extenders, inner_context);
                }
            }
            add_extended_inner_modules(inner, &mut extenders, &mut inner_context);
            visit(inner, false, &inner_context, dependencies);
            peers.insert(inner.name.clone(), inner.clone());
        }
    }
    let mut dependencies = ModuleDependencies::default();
    visit(module, true, &FastMap::default(), &mut dependencies);
    dependencies
}

/// `OPERATOR_ARGUMENT_KINDS` and `isOperatorArgument`: the expressions that can name an operator,
/// as Generator.generateExprOrOpArg tells them apart. A name such as K(1)!C, whose last part takes
/// no arguments, is a GeneralId too.
fn is_operator_argument(argument: &Expr) -> bool {
    match &argument.kind {
        ExpressionKind::Identifier { .. }
        | ExpressionKind::Subexpression { .. }
        | ExpressionKind::OperatorReference { .. }
        | ExpressionKind::Lambda { .. } => true,
        ExpressionKind::Apply { .. } => {
            get_selector_items(argument).is_some_and(|items| is_general_id(&items))
        }
        _ => false,
    }
}

/// `DefEntryParts`: the parts of a DEF clause entry that isn't a name, as Generator.genIdToSelector
/// reads them. `last_kind` is the kind of SANY's syntax node for the last part, or for a token its
/// text.
#[expect(dead_code, reason = "get_def_entry_parts in proofs.rs is a stub")]
#[derive(Clone, Debug)]
struct DefEntryParts {
    has_childless_first_child: Option<bool>,
    last: TokenSpan,
    last_kind: Option<String>,
}

/// `SYNTAX_KINDS`: the kind of the syntax node SANY's parser builds for an expression of each kind.
#[expect(dead_code, reason = "get_syntax_kind in proofs.rs is a stub")]
fn get_syntax_kind_of(expression: &Expression) -> Option<&'static str> {
    Some(match &expression.kind {
        ExpressionKind::Identifier { .. } | ExpressionKind::Subexpression { .. } => "N_GeneralId",
        ExpressionKind::Number { .. } => "N_Number",
        ExpressionKind::Decimal { .. } => "N_Real",
        ExpressionKind::SetEnumeration(_) => "N_SetEnumerate",
        ExpressionKind::SetFilter { .. } => "N_SubsetOf",
        ExpressionKind::SetMap { .. } => "N_SetOfAll",
        ExpressionKind::Tuple(_) => "N_Tuple",
        ExpressionKind::FunctionApplication { .. } => "N_FcnAppl",
        ExpressionKind::FunctionConstruction { .. } => "N_FcnConst",
        ExpressionKind::FunctionSet { .. } => "N_SetOfFcns",
        ExpressionKind::Record { is_set: false, .. } => "N_RcdConstructor",
        ExpressionKind::Record { is_set: true, .. } => "N_SetOfRcds",
        ExpressionKind::FieldAccess { .. } => "N_RecordComponent",
        ExpressionKind::Except { .. } => "N_Except",
        ExpressionKind::Prime(_) => "N_PostfixExpr",
        ExpressionKind::Always(_)
        | ExpressionKind::Eventually(_)
        | ExpressionKind::Enabled(_)
        | ExpressionKind::Unchanged(_) => "N_PrefixExpr",
        ExpressionKind::Quantified { .. } => "N_BoundedQuant",
        ExpressionKind::UnboundedQuantifier { .. } => "N_UnboundedQuant",
        ExpressionKind::Choose { .. } => "N_UnBoundedOrBoundedChoose",
        ExpressionKind::If { .. } => "N_IfThenElse",
        ExpressionKind::Case { .. } => "N_Case",
        ExpressionKind::Let { .. } => "N_LetIn",
        ExpressionKind::Action { .. } => "N_ActionExpr",
        ExpressionKind::Fairness { .. } => "N_FairnessExpr",
        _ => return None,
    })
}

/// `NESTED_FIRST_CHILD_KINDS`: the syntax nodes whose first child is a node with children of its
/// own. The first child of any other is a token, or a node without children.
#[expect(dead_code, reason = "has_childless_first_child in proofs.rs is a stub")]
const NESTED_FIRST_CHILD_KINDS: &[&str] = &[
    "N_GeneralId",
    "N_OpApplication",
    "N_PrefixExpr",
    "N_InfixExpr",
    "N_PostfixExpr",
    "N_FcnAppl",
    "N_RecordComponent",
];

const POSTFIX_OPERATOR_TEXTS: &[&str] = &["'", "^+", "^*", "^#"];

/// `getOperatorNodeKind`: SANY's syntax node for an operator (an `OperatorReference` or a `Lambda`)
/// that appears where an expression is required. The parser reads a prefix operator other than ~
/// and -. as a LAMBDA.
fn get_operator_node_kind(expression: &Expression, text: &str) -> &'static str {
    if POSTFIX_OPERATOR_TEXTS.contains(&text) {
        return "N_GenPostfixOp";
    }
    if matches!(expression.kind, ExpressionKind::Lambda { .. }) || text == "~" || text == "-." {
        "N_GenNonExpPrefixOp"
    } else {
        "N_GenInfixOp"
    }
}

/// `getBoundGroups`: the bound groups of a quantifier, set filter, set map or function. The parser
/// expands \A x, y \in S into a bound per name that shares the set, and SANY keeps one group.
fn get_bound_groups(bounds: &[Bound]) -> Vec<Vec<&Bound>> {
    let mut groups: Vec<Vec<&Bound>> = Vec::new();
    for bound in bounds {
        let is_same_group = groups.last().is_some_and(|last| {
            Rc::ptr_eq(&last[0].set, &bound.set)
                && matches!(bound.pattern, BoundPattern::Name { .. })
                && matches!(last[0].pattern, BoundPattern::Name { .. })
        });
        match groups.last_mut() {
            Some(last) if is_same_group => last.push(bound),
            _ => groups.push(vec![bound]),
        }
    }
    groups
}

/// A module's file and its syntax tree.
struct LoadedSource {
    file: Rc<SourceFile>,
    module: Rc<Module>,
}

/// The loader of `generateSanySpecification`: `parseSource`, `loadSource`,
/// `calculateDependencies`, SpecObj.loadSpec and `getModuleDependencies`.
struct Loader<'a> {
    options: &'a GenerationOptions<'a>,
    load_module: &'a dyn Fn(&str) -> Option<String>,
    root_name: Name,
    sources: FastMap<Name, Rc<LoadedSource>>,
    readings: SanyReadings,
    module_dependencies: FastMap<Name, Rc<ModuleDependencies>>,
    order: Vec<Name>,
    visiting: FastSet<Name>,
    path: Vec<Name>,
    resolutions: FastSet<(Name, Name)>,
}

impl Loader<'_> {
    /// `parseSource`: the parser's errors are not SANY's, so a module that fails to parse gets the
    /// report of SANY's parser, and the parser's own report where SANY's parser would accept it.
    fn parse_source(&mut self, name: &str, text: &str) -> Result<(Rc<SanyReading>, Rc<Module>)> {
        let file = match (&self.options.root_file_name, &self.options.root_file_path) {
            (Some(root), Some(path)) if &**root == name && !path.is_empty() => path.clone(),
            _ => format!("{name}.tla"),
        };
        let reading = read_sany_text(&mut self.readings, text);
        match &reading.module {
            Ok(module) => {
                let module = module.clone();
                Ok((reading, module))
            }
            Err(error) => {
                let parse_error = get_sany_parse_error(text, TlcVersion::Master)
                    .unwrap_or_else(|| format!("***Parse Error***\n{}", error.message));
                not_yet(format!(
                    "Could not parse module {name} from file {file}\n{parse_error}"
                ))
            }
        }
    }

    /// `parseFile`.
    fn parse_file(&mut self, name: &Name, text: &str) -> Result<Rc<LoadedSource>> {
        let (reading, module) = self.parse_source(name, text)?;
        if module.name != *name {
            return not_yet(format!(
                "File name '{name}' does not match the name '{}' of the top level module it contains.",
                module.name
            ));
        }
        let entry = Rc::new(LoadedSource {
            file: Rc::new(create_source_file(
                module.name.clone(),
                text,
                &reading.tokens,
            )),
            module,
        });
        self.sources.insert(name.clone(), entry.clone());
        Ok(entry)
    }

    fn is_loaded(&self, name: &str) -> bool {
        self.sources.contains_key(name)
    }

    /// `loadSource`.
    fn load_source(
        &mut self,
        name: &Name,
        text: Option<&str>,
        importer: Option<&Name>,
    ) -> Result<()> {
        if self.is_loaded(name) {
            return Ok(());
        }
        let Some(text) = text else {
            let importer = importer.map_or_else(|| "undefined".to_owned(), ToString::to_string);
            return not_yet(format!(
                "Cannot find source file for module {name} imported in module {importer}."
            ));
        };
        self.parse_file(name, text)?;
        Ok(())
    }

    /// `getSource`.
    fn get_source(&mut self, name: &Name) -> Result<Rc<LoadedSource>> {
        match self.sources.get(name) {
            Some(entry) => Ok(entry.clone()),
            None => self.parse_file(name, ""),
        }
    }

    /// `getModuleDependencies`: ParameterizedSpecObj.findOrCreateParsedUnit adds the post
    /// conditions' modules to the root module's own extendees, before those of its inner modules.
    /// Loading the specification asks for the dependencies of each module many times, so they are
    /// collected once.
    fn get_module_dependencies(&mut self, name: &Name) -> Result<Rc<ModuleDependencies>> {
        if let Some(cached) = self.module_dependencies.get(name) {
            return Ok(cached.clone());
        }
        let module = self.get_source(name)?.module.clone();
        let mut dependencies = get_dependencies(&module);
        if let Some(root_extendees) = self
            .options
            .root_extendees
            .as_ref()
            .filter(|_| *name == self.root_name)
        {
            let at = module.extends.len().min(dependencies.extendees.len());
            dependencies
                .extendees
                .splice(at..at, root_extendees.iter().cloned());
            for extendee in root_extendees {
                dependencies
                    .importers
                    .entry(extendee.clone())
                    .or_insert_with(|| name.clone());
            }
        }
        let dependencies = Rc::new(dependencies);
        self.module_dependencies
            .insert(name.clone(), dependencies.clone());
        Ok(dependencies)
    }

    /// `calculateDependencies`: SANY analyzes a module after the modules it extends and
    /// instantiates.
    fn calculate_dependencies(
        &mut self,
        name: &Name,
        text: Option<&str>,
        importer: Option<&Name>,
    ) -> Result<()> {
        // SpecObj.nonCircularityTest.
        if let Some(cycle_start) = self.path.iter().position(|entry| entry == name) {
            let cycle: Vec<String> = self.path[cycle_start..]
                .iter()
                .chain([name])
                .map(|file| format!("{file}.tla"))
                .collect();
            return not_yet(format!(
                "Circular dependency among .tla files; dependency cycle is:\n\n  {}",
                cycle.join(" --> ")
            ));
        }
        if !self.visiting.insert(name.clone()) {
            return Ok(());
        }
        self.path.push(name.clone());
        self.load_source(name, text, importer)?;
        let dependencies = self.get_module_dependencies(name)?;
        for dependency in dependencies
            .extendees
            .iter()
            .chain(&dependencies.instancees)
        {
            let text = (self.load_module)(dependency);
            self.calculate_dependencies(dependency, text.as_deref(), Some(name))?;
        }
        self.path.pop();
        self.order.push(name.clone());
        Ok(())
    }

    fn is_resolved(&self, importer: &Name, name: &Name) -> bool {
        self.resolutions.contains(&(importer.clone(), name.clone()))
    }

    /// `findUnresolved`: SpecObj.loadSpec resolves the first unresolved name it finds from the
    /// root, every extended module before any instantiated one, each in the context of the module
    /// that names it.
    fn find_unresolved(
        &mut self,
        name: &Name,
        is_extendee: bool,
        visited: &mut FastSet<Name>,
    ) -> Result<Option<UnresolvedName>> {
        if !self.is_loaded(name) || !visited.insert(name.clone()) {
            return Ok(None);
        }
        let dependencies = self.get_module_dependencies(name)?;
        let names = if is_extendee {
            &dependencies.extendees
        } else {
            &dependencies.instancees
        };
        if let Some(unresolved) = names
            .iter()
            .find(|dependency| !self.is_resolved(name, dependency))
        {
            return Ok(Some(UnresolvedName {
                name: unresolved.clone(),
                importer: name.clone(),
                naming_module: dependencies
                    .importers
                    .get(unresolved)
                    .unwrap_or(name)
                    .clone(),
            }));
        }
        for dependency in dependencies
            .extendees
            .iter()
            .chain(&dependencies.instancees)
        {
            if self.is_resolved(name, dependency)
                && let Some(found) = self.find_unresolved(dependency, is_extendee, visited)?
            {
                return Ok(Some(found));
            }
        }
        Ok(None)
    }

    fn find_next(&mut self) -> Result<Option<UnresolvedName>> {
        let root = self.root_name.clone();
        match self.find_unresolved(&root, true, &mut FastSet::default())? {
            Some(found) => Ok(Some(found)),
            None => self.find_unresolved(&root, false, &mut FastSet::default()),
        }
    }

    /// `loadSpecification`: SpecObj.loadSpec.
    fn load_specification(&mut self, root_source: &str) -> Result<()> {
        let root = self.root_name.clone();
        self.load_source(&root, Some(root_source), None)?;
        while let Some(next) = self.find_next()? {
            if !self.is_loaded(&next.name) {
                let text = (self.load_module)(&next.name);
                self.load_source(&next.name, text.as_deref(), Some(&next.naming_module))?;
            }
            self.resolutions.insert((next.importer, next.name));
        }
        Ok(())
    }
}

/// The state of `generateSanySpecification` that the generation of every module shares: the
/// graph, SANY's messages, the counter of SANY's UIDs, the UID of the nullOAN of the Generator of
/// the module being generated (`nullApplication`), the builtins and the external modules.
struct SpecGenerator {
    graph: Graph,
    messages: Vec<SanyMessage>,
    uid: u32,
    null_application_uid: u32,
    builtins: Vec<NodeId>,
    builtins_by_name: FastMap<Name, NodeId>,
    external_modules: FastMap<Name, NodeId>,
}

impl SpecGenerator {
    /// SANY numbers its semantic nodes as it creates them, which the UIDs of its XML export show:
    /// Context's static initializer creates the builtins, SANY.frontEndInitialize creates them
    /// again for the specification, and the Generator class creates its InAssumeDummyNode.
    fn new() -> SpecGenerator {
        let mut graph = Graph::default();
        let mut uid = 0;
        let mut get_uid = || {
            uid += 1;
            uid
        };
        create_builtins(&mut Graph::default(), &mut get_uid);
        let builtins = create_builtins(&mut graph, &mut get_uid);
        get_uid();
        let builtins_by_name = builtins
            .iter()
            .map(|&builtin| {
                let name = graph.node(builtin).symbol_name().expect("a name").clone();
                (name, builtin)
            })
            .collect();
        SpecGenerator {
            graph,
            messages: Vec::new(),
            uid,
            null_application_uid: 0,
            builtins,
            builtins_by_name,
            external_modules: FastMap::default(),
        }
    }

    /// `getId`.
    fn get_uid(&mut self) -> u32 {
        self.uid += 1;
        self.uid
    }

    /// `addError` and `addWarning`.
    fn add_message(&mut self, location: MessageLocation, text: String, is_warning: bool) {
        add_sany_message(
            &mut self.messages,
            SanyMessage {
                location,
                text,
                is_warning,
                code: None,
            },
        );
    }
}

/// `generateSanySpecification`: builds the semantic graph SANY builds for a specification and its
/// modules, in the order SANY analyzes them: a module after the modules it extends and
/// instantiates. SANY always generates the standard modules here.
pub fn generate_sany_specification(
    root_source: &str,
    load_module: &dyn Fn(&str) -> Option<String>,
    options: &GenerationOptions,
) -> Result<SanySpecification> {
    let mut spec = SpecGenerator::new();
    let mut loader = Loader {
        options,
        load_module,
        root_name: Rc::from(""),
        sources: FastMap::default(),
        readings: SanyReadings::default(),
        module_dependencies: FastMap::default(),
        order: Vec::new(),
        visiting: FastSet::default(),
        path: Vec::new(),
        resolutions: FastSet::default(),
    };
    loader.root_name = match &options.root_file_name {
        Some(name) => name.clone(),
        None => loader.parse_source("", root_source)?.1.name.clone(),
    };
    let root = loader.root_name.clone();
    loader.load_specification(root_source)?;
    loader.calculate_dependencies(&root, Some(root_source), None)?;
    let mut modules = Vec::new();
    for name in loader.order.clone() {
        // Each module's Generator creates its nullODN, nullOAN, nullOpArg and nullLabelNode.
        let null_uids: Vec<u32> = (0..4).map(|_| spec.get_uid()).collect();
        spec.null_application_uid = null_uids[1];
        let entry = loader.get_source(&name)?;
        // A module's context starts as a copy of SANY's global context of builtins, whose list of
        // symbols runs from the last builtin to the first.
        let mut context = Context::default();
        for &builtin in spec.builtins.iter().rev() {
            add_to_context(&spec.graph, &mut context, builtin);
        }
        let module = generate_module(
            &mut spec,
            &entry.module,
            &entry.file,
            None,
            Vec::new(),
            context,
        )?;
        spec.external_modules.insert(name, module);
        if let Some(on_module) = options.on_module {
            on_module(&mut spec.graph, module, &mut spec.messages);
        }
        modules.push(module);
    }
    Ok(SanySpecification {
        root: *modules.last().expect("the root module"),
        graph: spec.graph,
        modules,
        messages: spec.messages,
        builtins: spec.builtins,
    })
}

/// A function definition being generated, whose application in its body makes it recursive.
#[derive(Clone, Debug)]
struct RecursiveFunction {
    name: Name,
    node: NodeId,
}

/// `state` of `generateModule`: the LET/IN level and the RECURSIVE declarations not yet defined.
#[derive(Clone, Debug)]
struct RecursionState {
    cur_level: u32,
    unresolved_count: Vec<i32>,
    unresolved_sum: i32,
    recursive_section_count: i32,
}

/// `generateModule`'s closures and state. `module` is `currentModule`; `scopes` holds the
/// `AssumeProveScope`s, which `assume_prove_scopes` (keyed by AssumeProve nodes), `label_goals`
/// (keyed by Label nodes) and `assume_prove_state.goal` share.
struct ModuleGenerator<'a> {
    spec: &'a mut SpecGenerator,
    #[expect(dead_code, reason = "the units in definitions.rs are stubs")]
    ast: Rc<Module>,
    file: Rc<SourceFile>,
    module: NodeId,
    symbol_table: SymbolTable,
    state: RecursionState,
    functions: Vec<RecursiveFunction>,
    except_stack: Vec<NodeId>,
    except_spec_stack: Vec<NodeId>,
    label_scopes: Vec<LabelScope>,
    assume_prove_state: AssumeProveState,
    scopes: Vec<AssumeProveScope>,
    assume_prove_scopes: FastMap<NodeId, ScopeId>,
    label_goals: FastMap<NodeId, LabelGoal>,
    #[expect(dead_code, reason = "RECURSIVE in definitions.rs is a stub")]
    recursive_declarations: Vec<NodeId>,
}

/// `generateModule`: the module `ast` of `file`, inner to `parent` if any, whose symbol table is
/// `outer` and the module's own `context`.
fn generate_module(
    spec: &mut SpecGenerator,
    ast: &Rc<Module>,
    file: &Rc<SourceFile>,
    parent: Option<NodeId>,
    outer: Vec<ContextSlot>,
    context: Context,
) -> Result<NodeId> {
    let mut generator = ModuleGenerator::new(spec, ast, file, parent, outer, context);
    generator.process_extends_list()?;
    generator.process_units()?;
    Ok(generator.module)
}

impl<'a> ModuleGenerator<'a> {
    /// The start of `generateModule`: `currentModule`, which joins its parent's definitions.
    fn new(
        spec: &'a mut SpecGenerator,
        ast: &Rc<Module>,
        file: &Rc<SourceFile>,
        parent: Option<NodeId>,
        mut contexts: Vec<ContextSlot>,
        context: Context,
    ) -> ModuleGenerator<'a> {
        let uid = spec.get_uid();
        let location = get_span_location(file, get_unit_span(file, &ast.location));
        let module = spec.graph.add(
            uid,
            NodeKind::Module(Box::new(crate::sany::nodes::Module {
                name: ast.name.clone(),
                location,
                extendees: Vec::new(),
                context,
                top_level: Vec::new(),
                definitions: Vec::new(),
                op_defs_in_recursive_section: Vec::new(),
                is_level_checked: false,
                records: Vec::new(),
            })),
        );
        if let Some(parent) = parent {
            let parent = spec.graph.module_mut(parent).expect("a module");
            parent.definitions.push(module);
        }
        contexts.push(ContextSlot::Module(module));
        ModuleGenerator {
            spec,
            ast: ast.clone(),
            file: file.clone(),
            module,
            symbol_table: SymbolTable { contexts },
            state: RecursionState {
                cur_level: 0,
                unresolved_count: vec![0],
                unresolved_sum: 0,
                recursive_section_count: 0,
            },
            functions: Vec::new(),
            except_stack: Vec::new(),
            except_spec_stack: Vec::new(),
            label_scopes: Vec::new(),
            assume_prove_state: AssumeProveState::default(),
            scopes: Vec::new(),
            assume_prove_scopes: FastMap::default(),
            label_goals: FastMap::default(),
            recursive_declarations: Vec::new(),
        }
    }

    /// The `generateModule` of an inner module, whose symbol table extends this one's.
    #[expect(dead_code, reason = "process_units in definitions.rs is a stub")]
    fn generate_inner_module(&mut self, ast: &Rc<Module>) -> Result<NodeId> {
        let file = self.file.clone();
        let contexts = self.symbol_table.contexts.clone();
        generate_module(
            self.spec,
            ast,
            &file,
            Some(self.module),
            contexts,
            Context::default(),
        )
    }

    /// `addError` at a location.
    fn add_error(&mut self, location: &SanyLocation, text: impl Into<String>) {
        self.spec
            .add_message(MessageLocation::At(location.clone()), text.into(), false);
    }

    /// `addError` and `addWarning` at the location of a symbol, which may have none.
    fn add_symbol_message(&mut self, symbol: NodeId, text: String, is_warning: bool) {
        let location = self
            .spec
            .graph
            .node(symbol)
            .location()
            .cloned()
            .map_or(MessageLocation::Unknown, MessageLocation::At);
        self.spec.add_message(location, text, is_warning);
    }

    /// `formatSanyLocation` of a symbol's location.
    fn format_symbol_location(&self, symbol: NodeId) -> String {
        format_sany_location(
            &self
                .spec
                .graph
                .node(symbol)
                .location()
                .cloned()
                .map_or(MessageLocation::Unknown, MessageLocation::At),
        )
    }

    /// `pushLabelScope`.
    fn push_label_scope(&mut self) {
        self.label_scopes.push(LabelScope::default());
    }

    /// `popLabels`.
    fn pop_labels(&mut self) -> OrderedMap<Name, NodeId> {
        self.label_scopes
            .pop()
            .map(|scope| scope.labels)
            .unwrap_or_default()
    }

    /// `endProof`.
    #[expect(dead_code, reason = "the proofs in proofs.rs are stubs")]
    fn end_proof(&mut self, statement: NodeId) {
        if let Some(&scope) = self.assume_prove_scopes.get(&statement) {
            self.scopes[scope.0].is_in_proof = false;
        }
    }

    /// `getLocation`.
    fn get_location(&self, expression: &Expression) -> SanyLocation {
        get_span_location(&self.file, get_expression_span(&self.file, expression))
    }

    /// `getUnitSpan`.
    fn get_unit_span(&self, location: &Location) -> TokenSpan {
        get_unit_span(&self.file, location)
    }

    /// `resolveModule`.
    fn resolve_module(&self, name: &str) -> Option<NodeId> {
        self.symbol_table
            .contexts
            .iter()
            .rev()
            .find_map(|slot| get_slot_context(&self.spec.graph, slot).get_module(name))
            .filter(|&module| self.spec.graph.module(module).is_some())
            .or_else(|| self.spec.external_modules.get(name).copied())
    }

    /// `getModule`.
    #[expect(dead_code, reason = "the instances in definitions.rs are stubs")]
    fn get_module(&self, name: &str) -> Result<NodeId> {
        match self.resolve_module(name) {
            Some(module) => Ok(module),
            None => not_yet(format!("Could not find module {name}")),
        }
    }

    /// `withContext`, which gives the context back.
    fn with_context<T>(
        &mut self,
        context: LocalContext,
        generate: impl FnOnce(&mut Self) -> Result<T>,
    ) -> Result<(T, LocalContext)> {
        self.symbol_table.contexts.push(ContextSlot::Local(context));
        let result = generate(self)?;
        Ok((result, self.pop_local_context()?))
    }

    /// `symbolTable.contexts.pop()` of a context of the generator's own.
    fn pop_local_context(&mut self) -> Result<LocalContext> {
        match self.symbol_table.contexts.pop() {
            Some(ContextSlot::Local(context)) => Ok(context),
            _ => not_yet("a symbol table that pops a module's context"),
        }
    }

    /// `resolveSymbol`.
    fn resolve_symbol(&self, name: &str) -> Option<NodeId> {
        self.symbol_table
            .contexts
            .iter()
            .rev()
            .find_map(|slot| get_slot_context(&self.spec.graph, slot).get_symbol(name))
    }

    /// `addToContext(getTopContext(symbolTable), symbol)`.
    fn add_to_top_context(&mut self, symbol: NodeId) {
        match self.symbol_table.contexts.last_mut() {
            Some(ContextSlot::Module(module)) => {
                self.spec.graph.add_to_module_context(*module, symbol);
            }
            Some(ContextSlot::Local(local)) => {
                add_to_context(&self.spec.graph, &mut local.context, symbol);
            }
            None => {}
        }
    }

    /// `addSymbol`: SymbolTable.addSymbol, a symbol joins the innermost context unless its name is
    /// taken, which is an error unless the symbols agree in kind and arity, and then a warning
    /// unless they are the same definition of a module without parameters.
    fn add_symbol(&mut self, symbol: NodeId) {
        let graph = &self.spec.graph;
        let name = graph.node(symbol).symbol_name().expect("a symbol").clone();
        let binding = self.resolve_symbol(&name);
        if binding == Some(symbol) {
            return;
        }
        let Some(binding) = binding else {
            self.add_to_top_context(symbol);
            return;
        };
        let is_conflict = matches!(graph.kind(symbol), NodeKind::FormalParam(_))
            || get_symbol_kind(graph.node(binding)) != get_symbol_kind(graph.node(symbol))
            || get_symbol_arity(graph, binding) != get_symbol_arity(graph, symbol);
        let is_built_in = matches!(graph.kind(binding),
            NodeKind::OpDef(definition) if definition.def_kind == DefKind::BuiltIn);
        if is_built_in {
            self.add_symbol_message(
                symbol,
                format!("Symbol {name} is a built-in operator, and cannot be redefined."),
                false,
            );
            return;
        }
        if is_conflict {
            let text = format!(
                "Multiply-defined symbol '{name}': this definition or declaration conflicts \nwith the one at {}.",
                self.format_symbol_location(binding)
            );
            self.add_symbol_message(symbol, text, false);
        } else if !is_same_origin(graph, symbol, binding) {
            let text = format!(
                "Multiple declarations or definitions for symbol {name}.  \nThis duplicates the one at {}.",
                self.format_symbol_location(binding)
            );
            self.add_symbol_message(symbol, text, true);
        }
    }

    /// `createFormalParam`.
    fn create_formal_param(
        &mut self,
        name: Name,
        arity: usize,
        location: Option<SanyLocation>,
        is_added: bool,
    ) -> NodeId {
        let uid = self.spec.get_uid();
        let param = self.spec.graph.add(
            uid,
            NodeKind::FormalParam(FormalParam {
                name,
                arity,
                location,
            }),
        );
        if is_added {
            self.add_symbol(param);
        }
        param
    }

    /// The fields `createOpDef` gives a definition of `name` with `params` at `location`, which a
    /// caller overrides as `createOpDef`'s `fields` do.
    fn new_op_def(&self, name: Name, params: Vec<NodeId>, location: SanyLocation) -> OpDef {
        let count = params.len();
        OpDef {
            def_kind: DefKind::UserDefined,
            name,
            arity: count,
            params: Some(params),
            body: None,
            is_local: false,
            location,
            module: Some(self.module),
            source: None,
            pre_comments: Vec::new(),
            is_defined: true,
            in_recursive: false,
            in_recursive_section: false,
            recursive_section: -1,
            let_in_level: 0,
            weights: vec![0; count],
            is_leibniz_arg: Some(vec![true; count]),
            is_leibniz: true,
            op_level_cond: None,
            max_levels: vec![TEMPORAL_LEVEL; count],
            min_max_level: None,
            labels: OrderedMap::new(),
            step: None,
        }
    }

    /// `createOpDef`, given its fields (`new_op_def` and the caller's).
    fn create_op_def(&mut self, definition: OpDef) -> NodeId {
        let uid = self.spec.get_uid();
        self.spec
            .graph
            .add(uid, NodeKind::OpDef(Box::new(definition)))
    }

    /// `setRecursionFields`.
    #[expect(dead_code, reason = "the definitions in definitions.rs are stubs")]
    fn set_recursion_fields(&mut self, definition: NodeId) {
        let state = &self.state;
        let is_in_section = state.unresolved_sum > 0;
        let is_in_recursive_section = state
            .unresolved_count
            .get(state.cur_level as usize)
            .is_some_and(|&count| count > 0);
        let op_def = self
            .spec
            .graph
            .op_def_mut(definition)
            .expect("a definition");
        op_def.let_in_level = state.cur_level;
        if is_in_section {
            op_def.recursive_section = state.recursive_section_count;
            op_def.in_recursive_section = is_in_recursive_section;
            self.spec
                .graph
                .module_mut(self.module)
                .expect("a module")
                .op_defs_in_recursive_section
                .push(definition);
        }
    }

    /// `createOpAppl`.
    fn create_op_appl<O: Into<Option<NodeId>>>(
        &mut self,
        operator: NodeId,
        operands: impl IntoIterator<Item = O>,
        location: SanyLocation,
        binding: OpApplBinding,
    ) -> NodeId {
        let uid = self.spec.get_uid();
        self.add_op_appl(uid, operator, operands, location, binding)
    }

    /// `createOpAppl` with the UID `uid`.
    fn add_op_appl<O: Into<Option<NodeId>>>(
        &mut self,
        uid: u32,
        operator: NodeId,
        operands: impl IntoIterator<Item = O>,
        location: SanyLocation,
        binding: OpApplBinding,
    ) -> NodeId {
        self.spec.graph.add(
            uid,
            NodeKind::OpAppl(OpAppl {
                operator,
                operands: operands.into_iter().map(Into::into).collect(),
                unbounded: binding.unbounded,
                bounded: binding.bounded,
                tuple_ors: binding.tuple_ors,
                ranges: binding.ranges.unwrap_or_default(),
                location,
                is_null: false,
                is_absent: false,
            }),
        )
    }

    /// `createNullNode`: Generator.nullOAN, which SANY returns where it reported an error and
    /// carries on. It has no syntax tree node, so its location is that of the builtins.
    fn create_null_node(&mut self) -> NodeId {
        let operator = self.get_builtin("$Nop");
        let uid = self.spec.null_application_uid;
        let node = self.add_op_appl(
            uid,
            operator,
            Vec::<NodeId>::new(),
            get_builtin_location(),
            OpApplBinding::default(),
        );
        if let NodeKind::OpAppl(application) = &mut self.spec.graph.node_mut(node).kind {
            application.is_null = true;
        }
        node
    }

    /// `getBuiltin`, which the generator calls only with the names of builtins.
    fn get_builtin(&self, name: &str) -> NodeId {
        *self
            .spec
            .builtins_by_name
            .get(name)
            .unwrap_or_else(|| panic!("SANY has no builtin operator {name}"))
    }

    /// `applyBuiltin`.
    fn apply_builtin<O: Into<Option<NodeId>>>(
        &mut self,
        name: &str,
        operands: impl IntoIterator<Item = O>,
        location: SanyLocation,
        binding: OpApplBinding,
    ) -> NodeId {
        let operator = self.get_builtin(name);
        self.create_op_appl(operator, operands, location, binding)
    }

    /// `createString`.
    fn create_string(&mut self, value: &str, location: SanyLocation) -> NodeId {
        let uid = self.spec.get_uid();
        self.spec.graph.add(
            uid,
            NodeKind::String {
                value: value.to_owned(),
                location,
            },
        )
    }

    /// `createOpArg`.
    fn create_op_arg(&mut self, op: NodeId, location: SanyLocation) -> NodeId {
        let uid = self.spec.get_uid();
        self.spec.graph.add(uid, NodeKind::OpArg { op, location })
    }

    /// `resolveName`.
    fn resolve_name(&self, name: &str, location: &SanyLocation) -> Result<NodeId> {
        match self.resolve_symbol(&resolve_synonym(name)) {
            Some(symbol) if !matches!(self.spec.graph.kind(symbol), NodeKind::Module(_)) => {
                Ok(symbol)
            }
            _ => not_yet(format!(
                "Unknown operator: `{name}' at line {}, column {} of module {}",
                location.begin_line, location.begin_column, location.file
            )),
        }
    }

    /// `matchArguments`: OpDefNode.match, a definition takes as many arguments as it has
    /// parameters, which differs from its arity only where its RECURSIVE declaration has another,
    /// and an operator it takes must be given an operator of its arity that takes no operators.
    fn match_arguments(&mut self, operator: NodeId, operands: &[NodeId], location: &SanyLocation) {
        let graph = &self.spec.graph;
        let Some(definition) = graph
            .op_def(operator)
            .filter(|definition| definition.def_kind == DefKind::UserDefined)
        else {
            return;
        };
        let name = definition.name.clone();
        let params = definition.params.clone().unwrap_or_default();
        if params.len() != operands.len() {
            self.add_error(
                location,
                format!(
                    "Wrong number of arguments ({}) given to operator '{name}', \nwhich requires {} arguments.",
                    operands.len(),
                    params.len()
                ),
            );
            return;
        }
        for (index, (&param, &operand)) in params.iter().zip(operands).enumerate() {
            let graph = &self.spec.graph;
            let param_arity = get_symbol_arity(graph, param);
            let operand_op = match graph.kind(operand) {
                NodeKind::OpArg { op, .. } => Some(*op),
                _ => None,
            };
            if param_arity == 0 && operand_op.is_some() {
                self.add_error(
                    location,
                    format!(
                        "Operator used in argument number {} has incorrect number of arguments.",
                        index + 1
                    ),
                );
            }
            let graph = &self.spec.graph;
            let is_matching = operand_op.is_some_and(|op| {
                get_symbol_arity(graph, op) == param_arity
                    && !graph.op_def(op).is_some_and(|definition| {
                        definition
                            .params
                            .iter()
                            .flatten()
                            .any(|&parameter| get_symbol_arity(graph, parameter) > 0)
                    })
            });
            if param_arity > 0 && !is_matching {
                self.add_error(
                    location,
                    format!(
                        "Argument number {} to operator '{name}' \nshould be a {param_arity}-parameter operator.",
                        index + 1
                    ),
                );
            }
        }
    }

    /// `locateSelectorItems`: the parts of a selector at the tokens of the expression that SANY
    /// locates them at, from the name or selector itself to its parenthesized arguments. A
    /// selector other than a name or !(...) is spelled as its `name`.
    fn locate_selector_items(
        &self,
        items: Vec<SelectorItem>,
        span: TokenSpan,
    ) -> Vec<SelectorItem> {
        let file = &self.file;
        let mut cursor = span.start;
        items
            .into_iter()
            .map(|mut item| {
                let text = if item.op == SelectorOp::Null {
                    "("
                } else {
                    &item.name
                };
                let Some(index) = find_token(file, cursor, span.end, text) else {
                    return item;
                };
                if item.op == SelectorOp::Null {
                    let close = get_matching_index(file, index);
                    cursor = close + 1;
                    item.location = Some(get_span_location(
                        file,
                        TokenSpan {
                            start: index,
                            end: close,
                        },
                    ));
                    return item;
                }
                cursor = index + 1;
                item.location = Some(get_token_location(file, index));
                if item.args.is_none() || !is_token(file, index + 1, "(") {
                    return item;
                }
                let close = get_matching_index(file, index + 1);
                cursor = close + 1;
                item.args_location = Some(get_span_location(
                    file,
                    TokenSpan {
                        start: index + 1,
                        end: close,
                    },
                ));
                item
            })
            .collect()
    }

    /// `generateSelector`.
    fn generate_selector(
        &mut self,
        expression: &Expr,
        expected_arity: i32,
        is_fact: bool,
        is_def: bool,
    ) -> Result<NodeId> {
        let Some(items) = get_selector_items(expression) else {
            return not_yet("Expected a name");
        };
        let items = self.locate_selector_items(items, get_expression_span(&self.file, expression));
        let location = self.get_location(expression);
        selector_to_node(self, &items, expected_arity, is_fact, is_def, &location)
    }

    /// `generateSelectorExpression`.
    fn generate_selector_expression(&mut self, expression: &Expr) -> Result<NodeId> {
        let node = self.generate_selector(expression, 0, false, false)?;
        if !matches!(self.spec.graph.kind(node), NodeKind::OpAppl(_)) {
            return not_yet("Expected an expression");
        }
        Ok(node)
    }

    /// `checkRecursion`.
    fn check_recursion(&mut self, node: NodeId) {
        let NodeKind::OpAppl(application) = self.spec.graph.kind(node) else {
            return;
        };
        let name = self.spec.graph.node(application.operator).symbol_name();
        let Some(recursive) = self
            .functions
            .iter()
            .find(|entry| Some(&entry.name) == name)
            .map(|entry| entry.node)
        else {
            return;
        };
        let builtin = self.get_builtin("$RecursiveFcnSpec");
        if let NodeKind::OpAppl(application) = &mut self.spec.graph.node_mut(recursive).kind {
            application.operator = builtin;
        }
    }

    /// `generateBounds`: processQuantBoundArgs, SANY generates every bounding set before it
    /// declares the symbols, each named at its token between the end of the previous group and its
    /// set.
    fn generate_bounds(&mut self, bounds: &[Bound], search_start: usize) -> Result<BoundSymbols> {
        let ranges = get_bound_groups(bounds)
            .iter()
            .map(|group| self.generate_expression(&group[0].set))
            .collect::<Result<Vec<_>>>()?;
        Ok(self.generate_bounds_with_ranges(bounds, search_start, ranges))
    }

    /// `generateWithParams`: Generator.pushFormalParams, a label in the expression has to name the
    /// parameters it binds.
    fn generate_with_params(&mut self, params: Vec<NodeId>, expression: &Expr) -> Result<NodeId> {
        let scope = self.label_scopes.len().checked_sub(1);
        if let Some(scope) = scope {
            self.label_scopes[scope].params.push(params);
        }
        let node = self.generate_expression(expression)?;
        if let Some(scope) = scope {
            self.label_scopes[scope].params.pop();
        }
        Ok(node)
    }

    /// `generateLambda`.
    fn generate_lambda(&mut self, expression: &Expr) -> Result<NodeId> {
        let ExpressionKind::Lambda { params, body, .. } = &expression.kind else {
            return not_yet("Expected a LAMBDA");
        };
        let file = self.file.clone();
        let span = get_expression_span(&file, expression);
        let name_indexes = find_name_tokens(&file, span.start, span.end, params);
        let (lambda, _) = self.with_context(LocalContext::default(), |generator| {
            let params = params
                .iter()
                .enumerate()
                .map(|(index, name)| {
                    let location = get_token_location(&file, name_indexes[index]);
                    generator.create_formal_param(name.clone(), 0, Some(location), true)
                })
                .collect::<Vec<_>>();
            let body = generator.generate_with_params(params.clone(), body)?;
            let definition = OpDef {
                body: Some(body),
                pre_comments: get_pre_comments(&file, span.start),
                ..generator.new_op_def(Rc::from("LAMBDA"), params, get_span_location(&file, span))
            };
            Ok(generator.create_op_def(definition))
        })?;
        Ok(lambda)
    }

    /// `getOperatorArgumentName`: an operator symbol passed as an argument, such as SUBSET or -.,
    /// is desugared into a LAMBDA without a range.
    fn get_operator_argument_name(&self, argument: &Expr) -> Name {
        match &argument.kind {
            ExpressionKind::OperatorReference { operator, .. } => operator.clone(),
            ExpressionKind::Lambda { body, .. }
                if matches!(body.kind, ExpressionKind::Apply { .. }) =>
            {
                let ExpressionKind::Apply { operator, .. } = &body.kind else {
                    unreachable!("an Apply")
                };
                operator.clone()
            }
            _ => self.file.tokens[get_token_index(&self.file, argument.location.position())]
                .text
                .clone(),
        }
    }

    /// `generateOperatorArgument`: Generator.generateOpArg, after an error SANY gives its
    /// nullOpArg.
    #[expect(
        dead_code,
        reason = "process_substitutions in definitions.rs is a stub"
    )]
    fn generate_operator_argument(&mut self, argument: &Expr, target: NodeId) -> Result<NodeId> {
        let location = self.get_location(argument);
        if let ExpressionKind::Lambda { operator, .. } = &argument.kind {
            let op = match operator {
                None => self.generate_lambda(argument)?,
                Some(_) => {
                    self.resolve_name(&self.get_operator_argument_name(argument), &location)?
                }
            };
            return Ok(self.create_op_arg(op, location));
        }
        let target_node = self.spec.graph.node(target);
        let target_arity = get_symbol_arity(&self.spec.graph, target);
        if !is_operator_argument(argument) {
            let text = format!(
                "Arity {target_arity} operator (not an expression) is expected \nto substitute for CONSTANT '{}'.",
                target_node.symbol_name().expect("a symbol")
            );
            self.add_error(&location, text);
            return Ok(self.create_null_node());
        }
        if let ExpressionKind::OperatorReference { operator, .. } = &argument.kind {
            let op = self.resolve_name(operator, &location)?;
            return Ok(self.create_op_arg(op, location));
        }
        let node = self.generate_selector(argument, target_arity, false, false)?;
        match self.spec.graph.kind(node) {
            NodeKind::OpArg { .. } => Ok(node),
            NodeKind::OpAppl(application) if application.is_null => Ok(node),
            _ => not_yet(format!(
                "Expected an operator argument at line {}, column {}",
                location.begin_line, location.begin_column
            )),
        }
    }

    /// `generateArgument`: generateExprOrOpArg, an argument is an operator where the parameter
    /// takes arguments. SANY reports an argument that doesn't fit at the operator's name and
    /// carries on.
    fn generate_argument(
        &mut self,
        operator: NodeId,
        index: usize,
        argument: &Expr,
        operator_location: &SanyLocation,
    ) -> Result<NodeId> {
        let graph = &self.spec.graph;
        let operator_name = graph
            .node(operator)
            .symbol_name()
            .expect("a symbol")
            .clone();
        let expected_arity = graph
            .op_def(operator)
            .filter(|definition| {
                matches!(
                    definition.def_kind,
                    DefKind::UserDefined | DefKind::ModuleInstance
                )
            })
            .and_then(|definition| definition.params.as_ref()?.get(index).copied())
            .map_or(0, |param| get_symbol_arity(graph, param));
        if expected_arity == 0 {
            return self.generate_expression(argument);
        }
        let file = self.file.clone();
        let span = get_expression_span(&file, argument);
        let location = get_span_location(&file, span);
        let position = format!("{} (counting from 1)", index + 1);
        let argument_span = get_argument_span(&file, span);
        if argument_span != span || !is_operator_argument(argument) {
            self.add_error(
                &get_span_location(&file, argument_span),
                format!(
                    "An expression appears as argument number {position} to operator '{operator_name}', in a position an operator is required."
                ),
            );
            return Ok(self.create_null_node());
        }
        if matches!(
            argument.kind,
            ExpressionKind::Identifier { .. }
                | ExpressionKind::Subexpression { .. }
                | ExpressionKind::Apply { .. }
        ) {
            // The selector names the operator, or reports why not and gives SANY's nullOAN.
            let node = self.generate_selector(argument, expected_arity, false, false)?;
            return match self.spec.graph.kind(node) {
                NodeKind::OpArg { .. } | NodeKind::OpAppl(_) => Ok(node),
                _ => not_yet(format!(
                    "Expected an operator argument at {}",
                    format_sany_location(&MessageLocation::At(location))
                )),
            };
        }
        if let ExpressionKind::Lambda { operator: None, .. } = &argument.kind {
            let lambda = self.generate_lambda(argument)?;
            let arity = get_symbol_arity(&self.spec.graph, lambda);
            if arity == expected_arity {
                return Ok(self.create_op_arg(lambda, location));
            }
            self.add_error(
                operator_location,
                format!(
                    "Lambda expression with arity {arity} used as argument {} of operator `{operator_name}', \nbut an operator of arity {expected_arity} is required.",
                    index + 1
                ),
            );
            return Ok(self.create_null_node());
        }
        let name = self.get_operator_argument_name(argument);
        let Some(symbol) = self.resolve_symbol(&resolve_synonym(&name)) else {
            self.add_error(
                &location,
                format!("Could not find declaration or definition of symbol '{name}'."),
            );
            return Ok(self.create_null_node());
        };
        let arity = get_symbol_arity(&self.spec.graph, symbol);
        if arity == expected_arity {
            return Ok(self.create_op_arg(symbol, location));
        }
        let symbol_name = self
            .spec
            .graph
            .node(symbol)
            .symbol_name()
            .expect("a symbol")
            .clone();
        let text = format!(
            "Operator with incorrect arity passed as argument. \nOperator '{symbol_name}' of arity {arity} is argument number {position} to operator `{}', \nbut an operator of arity {expected_arity} was expected.",
            self.format_symbol_location(operator)
        );
        self.add_error(operator_location, text);
        Ok(self.create_null_node())
    }
}

/// `getUnitSpan`.
fn get_unit_span(file: &SourceFile, location: &Location) -> TokenSpan {
    match &location.range {
        Some(range) => get_range_span(file, range),
        None => {
            let index = get_token_index(file, location.position());
            TokenSpan {
                start: index,
                end: index,
            }
        }
    }
}

impl SelectorGenerator for ModuleGenerator<'_> {
    fn graph(&self) -> &Graph {
        &self.spec.graph
    }

    fn graph_mut(&mut self) -> &mut Graph {
        &mut self.spec.graph
    }

    fn resolve_symbol(&self, name: &str) -> Option<NodeId> {
        ModuleGenerator::resolve_symbol(self, name)
    }

    fn resolve_synonym(&self, name: &str) -> Name {
        resolve_synonym(name)
    }

    fn generate_expression(&mut self, expression: &Expr) -> Result<NodeId> {
        ModuleGenerator::generate_expression(self, expression)
    }

    fn generate_argument(
        &mut self,
        operator: NodeId,
        index: usize,
        argument: &Expr,
        location: &SanyLocation,
    ) -> Result<NodeId> {
        ModuleGenerator::generate_argument(self, operator, index, argument, location)
    }

    fn create_op_appl(
        &mut self,
        operator: NodeId,
        operands: Vec<NodeId>,
        location: &SanyLocation,
    ) -> Result<NodeId> {
        let node = ModuleGenerator::create_op_appl(
            self,
            operator,
            operands.iter().copied(),
            location.clone(),
            OpApplBinding::default(),
        );
        self.match_arguments(operator, &operands, location);
        Ok(node)
    }

    fn create_op_arg(&mut self, operator: NodeId, location: &SanyLocation) -> NodeId {
        ModuleGenerator::create_op_arg(self, operator, location.clone())
    }

    fn create_formal_param(
        &mut self,
        name: Name,
        arity: usize,
        location: Option<SanyLocation>,
    ) -> NodeId {
        ModuleGenerator::create_formal_param(self, name, arity, location, false)
    }

    fn create_lambda(
        &mut self,
        params: Vec<NodeId>,
        body: NodeId,
        location: &SanyLocation,
    ) -> NodeId {
        let position = Position {
            line: location.begin_line,
            column: location.begin_column,
        };
        let definition = OpDef {
            body: Some(body),
            pre_comments: get_pre_comments(&self.file, get_token_index(&self.file, position)),
            ..self.new_op_def(Rc::from("LAMBDA"), params, location.clone())
        };
        self.create_op_def(definition)
    }

    fn copy_subst_in(&mut self, prefix: NodeId, body: NodeId) -> NodeId {
        let NodeKind::SubstIn(SubstIn {
            substs,
            instantiating_module,
            instantiated_module,
            location,
            ..
        }) = self.spec.graph.kind(prefix).clone()
        else {
            panic!("a SubstIn");
        };
        self.create_subst_in(
            false,
            substs,
            body,
            instantiated_module,
            location,
            instantiating_module,
        )
    }

    fn get_builtin(&self, name: &str) -> NodeId {
        ModuleGenerator::get_builtin(self, name)
    }

    fn add_error(&mut self, location: &SanyLocation, text: String) -> NodeId {
        ModuleGenerator::add_error(self, location, text);
        self.create_null_node()
    }

    fn is_out_of_label_scope(&self, label: NodeId) -> bool {
        self.label_goals.get(&label).is_some_and(|goal| {
            let scope = &self.scopes[goal.scope.0];
            scope
                .is_declared_before
                .get(goal.clause)
                .copied()
                .unwrap_or(false)
                && scope.is_suffices == scope.is_in_proof
        })
    }

    fn is_out_of_clause_scope(&self, assume_prove: NodeId, position: usize) -> bool {
        self.assume_prove_scopes
            .get(&assume_prove)
            .is_some_and(|scope| {
                let scope = &self.scopes[scope.0];
                position
                    .checked_sub(1)
                    .and_then(|index| scope.is_declared_before.get(index))
                    .copied()
                    .unwrap_or(false)
                    && (!scope.has_goal || scope.is_suffices == scope.is_in_proof)
            })
    }
}

#[cfg(test)]
mod tests {
    use super::{SpecGenerator, resolve_synonym};

    #[test]
    fn resolves_synonyms_in_each_part_of_a_name() {
        assert_eq!(&*resolve_synonym("I!\\cup"), "I!\\union");
        assert_eq!(&*resolve_synonym("~"), "\\lnot");
        assert_eq!(&*resolve_synonym("!!"), "!!");
    }

    #[test]
    fn numbers_the_builtins_after_those_of_the_global_context() {
        let spec = SpecGenerator::new();
        // 72 builtins with 77 phony parameters each time, then the InAssumeDummyNode.
        assert_eq!(spec.graph.node(spec.builtins[0]).uid, 150);
        assert_eq!(spec.uid, 299);
    }
}
