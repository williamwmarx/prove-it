//! Name resolution, as `src/resolve.ts`: binds each name of a module to the symbol it names,
//! writing on the AST what the TypeScript resolver writes (the key of a module's symbol in place of
//! its name, and a local binding's resolution), and reports SANY's semantic errors as it goes.

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use crate::ast::*;
use crate::errors::{FrontError, SanyError, SyntaxError, format_range};
use crate::hash::{FastMap, FastSet};
use crate::ordered_map::OrderedMap;
use crate::recursive::check_recursive;

pub type Result<T> = std::result::Result<T, FrontError>;

/// The kinds of symbol SANY tells apart when it binds a name twice. A parameter is also a bound
/// name, and a NEW symbol has a kind for each level.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SymbolKind {
    Builtin,
    Constant,
    Variable,
    Definition,
    Instance,
    Theorem,
    Parameter,
    New(SymbolLevel),
}

/// A symbol a module binds: `key` names it among all the modules' symbols, `params` holds the
/// arity of each parameter of a defined operator, and `range` is where SANY reports it.
#[derive(Clone, Debug)]
pub struct ModuleSymbol {
    pub key: Name,
    pub kind: SymbolKind,
    pub arity: usize,
    pub params: Option<Rc<[usize]>>,
    pub range: Option<Range>,
}

pub type Symbols = OrderedMap<Name, ModuleSymbol>;

/// What a binding is to `isBindable`.
#[derive(Clone, Debug)]
struct Binding {
    kind: SymbolKind,
    arity: usize,
    params: Option<Rc<[usize]>>,
    range: Option<Range>,
}

impl From<&ModuleSymbol> for Binding {
    fn from(symbol: &ModuleSymbol) -> Binding {
        Binding {
            kind: symbol.kind,
            arity: symbol.arity,
            params: symbol.params.clone(),
            range: symbol.range.clone(),
        }
    }
}

/// A named theorem or proof step whose parts a name such as `foo!lab` or `<1>2!1` selects.
/// `is_in_proof` holds while SANY analyzes the proof of the theorem or step.
#[derive(Debug)]
struct Goal {
    statement: Statement,
    is_suffices: bool,
    is_in_proof: Cell<bool>,
}

/// A local name (`LocalName`), or a name the module binds from `position` on (`ModuleBinding`).
/// `is_pending` holds for an operator a RECURSIVE declaration names until its definition.
/// `is_non_fact` holds for the name of a USE, HIDE, DEFINE or INSTANCE step, and `unselectable`
/// is SANY's error for the name of a step that asserts no expression used as one.
#[derive(Debug)]
struct Local {
    name: Name,
    kind: SymbolKind,
    arity: usize,
    params: Option<Rc<[usize]>>,
    range: RefCell<Option<Range>>,
    parent: Scope,
    goal: Option<Rc<Goal>>,
    is_pending: Cell<bool>,
    is_non_fact: bool,
    /// The name of a DEFINE step, which a DEF clause may name.
    is_definition_step: bool,
    unselectable: Option<&'static str>,
    position: Position,
    /// The parameters of a function a LET defines, which SANY checks its applications against.
    function_params: Option<usize>,
}

type Scope = Option<Rc<Local>>;

impl Local {
    fn new(name: Name, binding: Binding, parent: Scope) -> Local {
        Local {
            name,
            kind: binding.kind,
            arity: binding.arity,
            params: binding.params,
            range: RefCell::new(binding.range),
            parent,
            goal: None,
            is_pending: Cell::new(false),
            is_non_fact: false,
            is_definition_step: false,
            unselectable: None,
            position: MODULE_START,
            function_params: None,
        }
    }

    fn binding(&self) -> Binding {
        Binding {
            kind: self.kind,
            arity: self.arity,
            params: self.params.clone(),
            range: self.range.borrow().clone(),
        }
    }
}

pub type ErrorList = Rc<RefCell<Vec<SanyError>>>;

/// The module an INSTANCE instantiates: its declarations, the names the INSTANCE adds, and the
/// module that instantiates it.
pub struct InstancedModule {
    pub declarations: Vec<Declaration>,
    pub symbols: Symbols,
    pub instancer: Name,
}

pub type GetInstance<'a> = Rc<dyn Fn(&Rc<Instance>) -> Result<InstancedModule> + 'a>;
pub type GetKey = Rc<dyn Fn(&Definition) -> Name>;

/// A name that selects nothing, the arguments SANY analyzes before it, and the error it reports.
type SelectionError = (Expr, Vec<Expr>, SanyError);

/// What the TypeScript front end keeps in `WeakSet`s and `WeakMap`s by node: the names that select
/// a subexpression (`selections`, `selectionErrors`), the arities of the names resolution renamed
/// (`renamedArities`), the names of the definitions instances copy (`sourceNames`), and the
/// expressions instances put in for declarations. A table
/// keeps each node it names, so no other node takes its address.
#[derive(Default)]
pub struct Tables {
    /// Whether the linker collects SANY's messages, for which an error that stops linking carries
    /// SANY's report.
    pub is_collecting: std::cell::Cell<bool>,
    selected: RefCell<FastMap<usize, Expr>>,
    source_names: RefCell<FastMap<usize, (Rc<Definition>, Name)>>,
    errors: RefCell<FastMap<usize, SelectionError>>,
    renamed_arities: RefCell<FastMap<usize, (Expr, usize)>>,
    substitutions: RefCell<FastMap<usize, Expr>>,
}

fn address(expression: &Expr) -> usize {
    Rc::as_ptr(expression) as usize
}

impl Tables {
    /// Notes an expression an INSTANCE puts in for a declaration of the module it instantiates.
    pub fn add_substitution(&self, expression: &Expr) {
        self.substitutions
            .borrow_mut()
            .insert(address(expression), expression.clone());
    }

    /// Whether an INSTANCE puts this expression in for a declaration, where TLC's `SubstInNode`
    /// keeps the declaration's node and binds it to the expression's value.
    pub fn is_substitution(&self, expression: &Expr) -> bool {
        self.substitutions
            .borrow()
            .contains_key(&address(expression))
    }

    /// `getSourceName`.
    pub fn get_source_name(&self, definition: &Rc<Definition>) -> Name {
        self.source_names
            .borrow()
            .get(&(Rc::as_ptr(definition) as usize))
            .map_or_else(|| definition.name.clone(), |entry| entry.1.clone())
    }

    /// `withSourceName`: a copy of a definition keeps the name of the definition it copies.
    pub fn with_source_name(
        &self,
        definition: Rc<Definition>,
        source: &Rc<Definition>,
    ) -> Rc<Definition> {
        let name = self.get_source_name(source);
        if name != definition.name {
            self.source_names
                .borrow_mut()
                .insert(Rc::as_ptr(&definition) as usize, (definition.clone(), name));
        }
        definition
    }

    pub fn add_selection(&self, expression: &Expr) {
        self.selected
            .borrow_mut()
            .insert(address(expression), expression.clone());
    }

    pub fn is_selection(&self, expression: &Expr) -> bool {
        self.selected.borrow().contains_key(&address(expression))
    }

    /// The error SANY reports for a name that selects nothing, and the arguments it analyzes
    /// before it.
    pub fn set_error(&self, expression: &Expr, args: Vec<Expr>, error: SanyError) {
        self.errors
            .borrow_mut()
            .insert(address(expression), (expression.clone(), args, error));
    }

    fn get_error(&self, expression: &Expr) -> Option<(Vec<Expr>, SanyError)> {
        self.errors
            .borrow()
            .get(&address(expression))
            .map(|entry| (entry.1.clone(), entry.2.clone()))
    }
}

/// The operators a module's LETs declare RECURSIVE, each with its LET's level and what it binds,
/// in the order SANY reads them (`recursiveDecls`).
type LetRecursive = Rc<RefCell<Vec<(usize, Rc<Declaration>, Rc<Local>)>>>;

/// What SANY reports while it goes on analyzing a unit of a module, and the scope it analyzes it
/// in (`Unit`).
#[derive(Clone)]
struct Unit<'a> {
    imported: Rc<Symbols>,
    /// Where the module declares each of its constants and variables, which a unit sees only
    /// after.
    declared: Rc<FastMap<Name, Position>>,
    /// The modules `SymbolTable.resolveModule` finds from the unit on, by where they begin to be
    /// found: the module itself and its extended modules, and each inner module from its own.
    modules: Rc<FastMap<Name, Position>>,
    get_instance: GetInstance<'a>,
    definitions: Rc<OrderedMap<Name, Rc<Definition>>>,
    get_key: GetKey,
    location: Position,
    self_definition: Option<Rc<Definition>>,
    facts: Rc<RefCell<FastSet<Name>>>,
    goals: Rc<FastMap<Name, Rc<Goal>>>,
    bindings: Rc<RefCell<OrderedMap<Name, Rc<Local>>>>,
    errors: ErrorList,
    warnings: ErrorList,
    /// In a definition, a named theorem, or a numbered step.
    has_label_scope: bool,
    /// In the scope of a NEW in a nested ASSUME.
    is_label_forbidden: bool,
    is_in_except: bool,
    /// The @ of an assertion step that continues the infix assertion of the step before it, which
    /// stands for that step's right side.
    step_at: Option<usize>,
    /// Resolving a fact, which may name any step.
    is_fact: bool,
    /// The names bound since the innermost definition, label, or step, which a label must take.
    label_params: Rc<Vec<Name>>,
    labels: Rc<RefCell<FastSet<Name>>>,
    /// In a definition generated for a LET INSTANCE, or a subexpression analyzed where it is
    /// defined.
    is_generated: bool,
    tables: Rc<Tables>,
    /// How many LETs enclose the unit's definitions (`curLevel`).
    let_level: usize,
    let_recursive: LetRecursive,
}

impl Unit<'_> {
    fn error(&self, location: String, message: String) {
        self.errors
            .borrow_mut()
            .push(SanyError { location, message });
    }

    fn with_label_params(&self, names: &[Name]) -> Self {
        let mut params = (*self.label_params).clone();
        params.extend(names.iter().cloned());
        Unit {
            label_params: Rc::new(params),
            ..self.clone()
        }
    }
}

pub const KEY_SEPARATOR: char = '@';

pub const MODULE_START: Position = Position { line: 0, column: 0 };

/// A key is a name, the separator, and an id, so the operator `@@` is not one.
pub fn is_key(name: &str) -> bool {
    name.rfind(KEY_SEPARATOR)
        .is_some_and(|index| index > 0 && index < name.len() - 1)
}

/// The operators SANY's symbol table holds before any module, beside `CORE_OPERATORS`.
pub const CORE_SYMBOLS: [&str; 3] = ["~>", "-+->", "\\cdot"];

fn core_symbols() -> Vec<(Name, ModuleSymbol)> {
    CORE_SYMBOLS
        .into_iter()
        .map(|name| {
            let name: Name = Rc::from(name);
            (
                name.clone(),
                ModuleSymbol {
                    key: name,
                    kind: SymbolKind::Builtin,
                    arity: 2,
                    params: None,
                    range: None,
                },
            )
        })
        .collect()
}

pub fn is_before(left: Position, right: Position) -> bool {
    left.line < right.line || (left.line == right.line && left.column < right.column)
}

pub fn get_arity(definition: &Definition) -> usize {
    match &definition.kind {
        DefinitionKind::Operator { params, .. } => params.len(),
        DefinitionKind::Function { .. } => 0,
    }
}

pub fn get_param_arities(definition: &Definition) -> Rc<[usize]> {
    match &definition.kind {
        DefinitionKind::Operator { params, .. } => params.iter().map(|param| param.arity).collect(),
        DefinitionKind::Function { .. } => Rc::from([]),
    }
}

fn is_instantiated(definition: &Definition) -> bool {
    definition.name.contains('!')
}

fn lookup_local(scope: &Scope, name: &str) -> Option<Rc<Local>> {
    let mut current = scope.clone();
    while let Some(local) = current {
        if &*local.name == name {
            return Some(local);
        }
        current = local.parent.clone();
    }
    None
}

/// A name the module binds before the unit and before the range, which a copy of a subexpression
/// that a reference selects keeps from its definition.
fn get_module_binding(name: &str, unit: &Unit, range: Option<&Range>) -> Option<Rc<Local>> {
    let binding = unit.bindings.borrow().get(name).cloned()?;
    (is_before(binding.position, unit.location)
        && range.is_none_or(|range| is_before(binding.position, range.start)))
    .then_some(binding)
}

fn is_same_range(left: Option<&Range>, right: Option<&Range>) -> bool {
    matches!((left, right), (Some(left), Some(right)) if left == right)
}

/// `SymbolTable.addSymbol`: rejects redefining a built-in, a bound name, or a symbol of another
/// kind or arity, and warns of any other duplicate. A symbol SANY never sees, such as a generated
/// one, binds.
fn is_bindable(name: &str, current: Option<&Binding>, added: &Binding, unit: &Unit) -> bool {
    let Some(current) = current else {
        return true;
    };
    if is_same_range(current.range.as_ref(), added.range.as_ref()) {
        return false;
    }
    let Some(range) = &added.range else {
        return true;
    };
    if unit.is_generated || (current.kind != SymbolKind::Builtin && current.range.is_none()) {
        return true;
    }
    let location = format_range(range);
    let existing = current
        .range
        .as_ref()
        .map_or_else(|| "undefined".to_owned(), format_range);
    if current.kind == SymbolKind::Builtin {
        unit.error(
            location,
            format!("Symbol {name} is a built-in operator, and cannot be redefined."),
        );
    } else if added.kind == SymbolKind::Parameter
        || current.kind != added.kind
        || current.arity != added.arity
    {
        unit.error(
            location,
            format!(
                "Multiply-defined symbol '{name}': this definition or declaration conflicts \nwith the one at {existing}."
            ),
        );
    } else {
        unit.warnings.borrow_mut().push(SanyError {
            location,
            message: format!(
                "Multiple declarations or definitions for symbol {name}.  \nThis duplicates the one at {existing}."
            ),
        });
    }
    false
}

fn find_current(
    scope: &Scope,
    name: &str,
    unit: &Unit,
    range: Option<&Range>,
) -> Option<Rc<Local>> {
    lookup_local(scope, name).or_else(|| get_module_binding(name, unit, range))
}

fn bind_name(scope: &Scope, name: &Name, added: Binding, unit: &Unit) -> Scope {
    let current =
        find_current(scope, name, unit, added.range.as_ref()).map(|local| local.binding());
    if is_bindable(name, current.as_ref(), &added, unit) {
        Some(Rc::new(Local::new(name.clone(), added, scope.clone())))
    } else {
        scope.clone()
    }
}

/// Binds the names of a module from the unit on.
fn bind_module_name(name: &Name, added: Binding, unit: &Unit) {
    let current = unit
        .bindings
        .borrow()
        .get(name)
        .map(|local| local.binding());
    if is_bindable(name, current.as_ref(), &added, unit) {
        let mut local = Local::new(name.clone(), added, None);
        local.position = unit.location;
        unit.bindings
            .borrow_mut()
            .insert(name.clone(), Rc::new(local));
    }
}

fn parameter(arity: usize, range: Option<Range>) -> Binding {
    Binding {
        kind: SymbolKind::Parameter,
        arity,
        params: None,
        range,
    }
}

fn bind_names(scope: &Scope, names: &[Name], ranges: &[Range], unit: &Unit) -> Scope {
    names
        .iter()
        .enumerate()
        .fold(scope.clone(), |parent, (index, name)| {
            bind_name(
                &parent,
                name,
                parameter(0, ranges.get(index).cloned()),
                unit,
            )
        })
}

fn bind_params(scope: &Scope, params: &[OperatorParam], unit: &Unit) -> Scope {
    params.iter().fold(scope.clone(), |parent, param| {
        bind_name(
            &parent,
            &param.name,
            parameter(
                param.arity,
                param
                    .location
                    .as_ref()
                    .and_then(|location| location.range.clone()),
            ),
            unit,
        )
    })
}

pub fn get_pattern_names(pattern: &BoundPattern) -> Vec<Name> {
    pattern.names().to_vec()
}

pub fn get_bound_names(bounds: &[Bound]) -> Vec<Name> {
    bounds
        .iter()
        .flat_map(|bound| bound.pattern.names().iter().cloned())
        .collect()
}

fn pattern_ranges(pattern: &BoundPattern) -> &[Range] {
    match pattern {
        BoundPattern::Name { ranges, .. } | BoundPattern::Tuple { ranges, .. } => ranges,
    }
}

fn get_visible_definition(name: &str, unit: &Unit) -> Option<Rc<Definition>> {
    let definition = unit.definitions.get(name)?;
    let is_self = unit
        .self_definition
        .as_ref()
        .is_some_and(|own| Rc::ptr_eq(own, definition));
    let is_visible = if is_self {
        matches!(definition.kind, DefinitionKind::Function { .. }) || definition.is_recursive
    } else {
        definition.is_recursive || is_before(definition.location.position(), unit.location)
    };
    is_visible.then(|| definition.clone())
}

fn find_symbol(name: &str, unit: &Unit) -> Option<ModuleSymbol> {
    match get_visible_definition(name, unit) {
        Some(definition) => Some(ModuleSymbol {
            key: (unit.get_key)(&definition),
            kind: SymbolKind::Definition,
            arity: get_arity(&definition),
            params: Some(get_param_arities(&definition)),
            range: None,
        }),
        None => {
            let is_declared_later = unit
                .declared
                .get(name)
                .is_some_and(|declared| !is_before(*declared, unit.location));
            if is_declared_later {
                return None;
            }
            unit.imported.get(name).cloned()
        }
    }
}

fn find_binding(name: &str, scope: &Scope, unit: &Unit) -> Option<Binding> {
    lookup_local(scope, name)
        .map(|local| local.binding())
        .or_else(|| find_symbol(name, unit).map(|symbol| Binding::from(&symbol)))
}

fn utf16_length(text: &str) -> u32 {
    text.encode_utf16().count() as u32
}

/// SANY reports a name at the range of its text.
fn get_name_range(location: &Location, name: &str) -> Range {
    SourceRange {
        module: location
            .range
            .as_ref()
            .map_or_else(|| Rc::from(""), |range| range.module.clone()),
        start: location.position(),
        end: Position {
            line: location.line,
            column: (location.column + utf16_length(name)).wrapping_sub(1),
        },
    }
}

fn get_spelling(expression: &Expression) -> Option<Name> {
    match &expression.kind {
        ExpressionKind::Identifier { spelling, .. }
        | ExpressionKind::Apply { spelling, .. }
        | ExpressionKind::OperatorReference { spelling, .. } => spelling.clone(),
        _ => None,
    }
}

pub fn get_selector_ranges(expression: &Expression) -> Option<&[Range]> {
    match &expression.kind {
        ExpressionKind::Identifier {
            selector_ranges, ..
        }
        | ExpressionKind::Apply {
            selector_ranges, ..
        } => selector_ranges.as_deref(),
        ExpressionKind::Subexpression {
            selector_ranges, ..
        } => Some(selector_ranges),
        _ => None,
    }
}

/// SANY reports a name at its tokens, such as `M ! ⊕` for `M!\oplus`.
fn get_spelled_name_range(expression: &Expression, name: &str) -> Range {
    let selector_range = match &expression.kind {
        ExpressionKind::OperatorReference { .. } => None,
        _ => get_selector_ranges(expression).and_then(|ranges| ranges.last()),
    };
    match selector_range {
        Some(range) => SourceRange {
            module: range.module.clone(),
            start: expression.location.position(),
            end: range.end,
        },
        None => get_name_range(
            &expression.location,
            get_spelling(expression).as_deref().unwrap_or(name),
        ),
    }
}

/// SANY reports an operator symbol applied to operands as one it cannot resolve.
fn get_fixity(expression: &Expression) -> Option<&'static str> {
    let ExpressionKind::Apply { args, .. } = &expression.kind else {
        return None;
    };
    match args.len() {
        2 => Some("infix"),
        1 if is_before(expression.location.position(), args[0].location.position()) => {
            Some("prefix")
        }
        1 => Some("postfix"),
        _ => None,
    }
}

/// SANY names an undefined operator symbol such as `+` differently from an undefined identifier.
fn is_operator_symbol(name: &str) -> bool {
    !name
        .chars()
        .next()
        .is_some_and(|first| first.is_alphabetic() || first.is_ascii_digit() || first == '_')
}

fn is_step_name(name: &str) -> bool {
    let bytes = name.as_bytes();
    bytes.first() == Some(&b'<')
        && bytes
            .get(1)
            .is_some_and(|second| second.is_ascii_digit() || *second == b'*')
}

pub fn get_operand_index(operand: &Operand, count: usize) -> Option<usize> {
    match operand {
        Operand::Index(index) => {
            (*index >= 1.0 && *index <= count as f64).then(|| *index as usize - 1)
        }
        Operand::First => (count > 0).then_some(0),
        Operand::Last => (count == 2).then_some(1),
    }
}

/// The parts of a name such as `F(x)!l(y)`, each with its own arguments. `counts` holds the number
/// each part takes, when a part before the last takes some.
pub fn get_name_selectors(name: &str, args: &[Expr], counts: Option<&[usize]>) -> Vec<Selector> {
    let parts: Vec<&str> = name.split('!').collect();
    let part_counts: Vec<usize> = match counts {
        Some(counts) => counts.to_vec(),
        None => (0..parts.len())
            .map(|index| {
                if index == parts.len() - 1 {
                    args.len()
                } else {
                    0
                }
            })
            .collect(),
    };
    let mut start = 0;
    parts
        .iter()
        .enumerate()
        .map(|(index, part)| {
            let count = part_counts.get(index).copied().unwrap_or(0);
            let end = (start + count).min(args.len());
            let selector = Selector::Name {
                name: Rc::from(*part),
                args: args[start.min(args.len())..end].to_vec(),
            };
            start += count;
            selector
        })
        .collect()
}

fn get_selectors(reference: &Expression) -> Vec<Selector> {
    match &reference.kind {
        ExpressionKind::Subexpression { selectors, .. } => selectors.clone(),
        ExpressionKind::Identifier { .. } => {
            get_name_selectors(&reference.reference().unwrap_or_default(), &[], None)
        }
        ExpressionKind::Apply {
            args,
            argument_counts,
            ..
        } => get_name_selectors(
            &reference.reference().unwrap_or_default(),
            args,
            argument_counts.as_deref(),
        ),
        _ => Vec::new(),
    }
}

fn get_bound_sets(bounds: &[Bound]) -> Vec<Expr> {
    bounds
        .iter()
        .enumerate()
        .filter(|(index, bound)| *index == 0 || !Rc::ptr_eq(&bounds[index - 1].set, &bound.set))
        .map(|(_, bound)| bound.set.clone())
        .collect()
}

/// The names a binder binds, its body, and the sets it binds them to, which a selector such as
/// `!1` chooses from.
pub struct Binder {
    pub names: Vec<Name>,
    pub body: Expr,
    pub sets: Vec<Expr>,
}

pub fn get_binder(expression: &Expression) -> Option<Binder> {
    match &expression.kind {
        ExpressionKind::Quantified { bounds, body, .. }
        | ExpressionKind::FunctionConstruction { bounds, body } => Some(Binder {
            names: get_bound_names(bounds),
            body: body.clone(),
            sets: get_bound_sets(bounds),
        }),
        ExpressionKind::SetMap {
            expression: body,
            bounds,
        } => Some(Binder {
            names: get_bound_names(bounds),
            body: body.clone(),
            sets: get_bound_sets(bounds),
        }),
        ExpressionKind::SetFilter { bound, predicate } => Some(Binder {
            names: get_pattern_names(&bound.pattern),
            body: predicate.clone(),
            sets: vec![bound.set.clone()],
        }),
        ExpressionKind::Choose { pattern, set, body } => Some(Binder {
            names: get_pattern_names(pattern),
            body: body.clone(),
            sets: set.iter().cloned().collect(),
        }),
        ExpressionKind::UnboundedQuantifier { names, body, .. }
        | ExpressionKind::Lambda {
            params: names,
            body,
            ..
        } => Some(Binder {
            names: names.clone(),
            body: body.clone(),
            sets: Vec::new(),
        }),
        _ => None,
    }
}

/// The operands that a selector such as `!1` chooses from, where they do not depend on bound
/// names.
pub fn get_operands(expression: &Expression) -> Option<Vec<Expr>> {
    let location = &expression.location;
    Some(match &expression.kind {
        ExpressionKind::Apply { args, .. } => args.clone(),
        ExpressionKind::Junction { operands, .. } => operands.clone(),
        ExpressionKind::If {
            condition,
            consequent,
            alternative,
        } => vec![condition.clone(), consequent.clone(), alternative.clone()],
        ExpressionKind::Tuple(elements) | ExpressionKind::SetEnumeration(elements) => {
            elements.clone()
        }
        ExpressionKind::Record { fields, .. } => {
            fields.iter().map(|field| field.value.clone()).collect()
        }
        ExpressionKind::FunctionApplication { function, args } => vec![
            function.clone(),
            if args.len() == 1 {
                args[0].clone()
            } else {
                Rc::new(Expression::new(
                    ExpressionKind::Tuple(args.clone()),
                    location.clone(),
                ))
            },
        ],
        ExpressionKind::FieldAccess { record, field } => vec![
            record.clone(),
            Rc::new(Expression::new(
                ExpressionKind::String {
                    value: field.clone(),
                },
                location.clone(),
            )),
        ],
        ExpressionKind::Prime(inner)
        | ExpressionKind::Unchanged(inner)
        | ExpressionKind::Enabled(inner)
        | ExpressionKind::Always(inner)
        | ExpressionKind::Eventually(inner) => vec![inner.clone()],
        ExpressionKind::Action {
            action, subscript, ..
        } => vec![action.clone(), subscript.clone()],
        ExpressionKind::Fairness {
            subscript, action, ..
        } => vec![subscript.clone(), action.clone()],
        ExpressionKind::FunctionSet { domain, range } => vec![domain.clone(), range.clone()],
        ExpressionKind::Product(factors) => factors.clone(),
        ExpressionKind::Except { function, .. } => vec![function.clone()],
        _ => return None,
    })
}

fn is_reference(expression: &Expression) -> bool {
    matches!(
        expression.kind,
        ExpressionKind::Identifier { .. }
            | ExpressionKind::Apply { .. }
            | ExpressionKind::Subexpression { .. }
    )
}

fn is_in_scope_of_declaration(assume_prove: &AssumeProve, clause: usize) -> bool {
    assume_prove.assumptions[..clause.min(assume_prove.assumptions.len())]
        .iter()
        .any(|assumption| matches!(assumption, Assumed::NewSymbol(_)))
}

fn find_label(expression: &Expr, name: &str) -> Option<Expr> {
    match &expression.kind {
        ExpressionKind::Label { name: label, .. } => (&**label == name).then(|| expression.clone()),
        ExpressionKind::Lambda { .. } => None,
        ExpressionKind::Let { body, .. } => find_label(body, name),
        _ => expression
            .children()
            .iter()
            .find_map(|child| find_label(child, name)),
    }
}

/// A clause of an ASSUME/PROVE, or the statement of a theorem or step, that a name selects part
/// of.
#[derive(Clone)]
enum Clause {
    Expression(Expr),
    NewSymbol(NewSymbol),
    AssumeProve(AssumeProve),
    /// A labeled ASSUME/PROVE, which the front end lets a name select only as a fact.
    Label(Name),
}

fn get_clauses(assume_prove: &AssumeProve) -> Vec<Clause> {
    assume_prove
        .assumptions
        .iter()
        .map(|assumption| match assumption {
            Assumed::Expression(expression) => Clause::Expression(expression.clone()),
            Assumed::NewSymbol(symbol) => Clause::NewSymbol(symbol.clone()),
            Assumed::AssumeProve(inner) => Clause::AssumeProve(inner.clone()),
            Assumed::Label { name, .. } => Clause::Label(name.clone()),
        })
        .chain([Clause::Expression(assume_prove.conclusion.clone())])
        .collect()
}

fn statement_clause(statement: &Statement) -> Clause {
    match statement {
        Statement::Expression(expression) => Clause::Expression(expression.clone()),
        Statement::AssumeProve(assume_prove) => Clause::AssumeProve(assume_prove.clone()),
    }
}

/// SANY drops a label in the scope of a NEW in a nested ASSUME, after it reports the label.
fn find_clause_label(clause: &Clause, name: &str, is_forbidden: bool) -> Option<Clause> {
    match clause {
        Clause::AssumeProve(assume_prove) => {
            get_clauses(assume_prove)
                .iter()
                .enumerate()
                .find_map(|(index, inner)| {
                    find_clause_label(
                        inner,
                        name,
                        is_forbidden || is_in_scope_of_declaration(assume_prove, index),
                    )
                })
        }
        _ if is_forbidden => None,
        Clause::NewSymbol(symbol) => symbol
            .set
            .as_ref()
            .and_then(|set| find_label(set, name))
            .map(Clause::Expression),
        Clause::Expression(expression) => find_label(expression, name).map(Clause::Expression),
        Clause::Label(label) => (&**label == name).then(|| clause.clone()),
    }
}

fn get_label_body(expression: &Expr) -> Expr {
    match &expression.kind {
        ExpressionKind::Label { body, .. } => get_label_body(body),
        _ => expression.clone(),
    }
}

fn get_operand_name(operand: &Operand) -> String {
    match operand {
        Operand::Index(index) => format!("argument selector {index}"),
        Operand::First => "<<".to_owned(),
        Operand::Last => ">>".to_owned(),
    }
}

const SCOPE_MESSAGE: &str =
    "within the scope of a declaration\n from outside that declaration's scope.";

fn is_literal(expression: &Expression) -> bool {
    matches!(
        expression.kind,
        ExpressionKind::Number { .. }
            | ExpressionKind::Decimal { .. }
            | ExpressionKind::String { .. }
    )
}

/// `Generator.selectorToNode` for a name that selects part of a theorem or step. A part in the
/// scope of a NEW in its ASSUME may be selected only within the proof of the theorem, or only
/// after the proof of a SUFFICES step. A label takes its own arguments, and an operand must exist,
/// unless the part selected depends on bound names. A fact may select an ASSUME/PROVE or a NEW
/// clause.
fn check_selection(
    reference: &Expr,
    selectors: &[Selector],
    goal: &Goal,
    scope: &Scope,
    unit: &Unit,
    is_fact: bool,
) -> Result<()> {
    let report = |index: Option<usize>, message: String| {
        let range = index
            .and_then(|index| get_selector_ranges(reference).and_then(|ranges| ranges.get(index)))
            .or(reference.location.range.as_ref());
        if let Some(range) = range {
            unit.error(format_range(range), message);
        }
    };
    let is_out_of_scope = goal.is_suffices == goal.is_in_proof.get();
    let statement = statement_clause(&goal.statement);
    let mut node = statement.clone();
    let mut is_goal = true;
    let mut is_suffices_open = goal.is_suffices;
    for (offset, selector) in selectors[1..].iter().enumerate() {
        let index = offset + 1;
        match selector {
            Selector::Name { name, args } => {
                if !matches!(selectors[index - 1], Selector::Name { .. }) {
                    let is_let = match &node {
                        Clause::Expression(expression) => {
                            matches!(get_label_body(expression).kind, ExpressionKind::Let { .. })
                        }
                        _ => false,
                    };
                    if !is_let {
                        report(
                            Some(index - 1),
                            "A name selector here must be from a LET clause.".to_owned(),
                        );
                    }
                    return Ok(());
                }
                let found = if index == 1 {
                    let clauses = match &statement {
                        Clause::AssumeProve(assume_prove) => get_clauses(assume_prove),
                        other => vec![other.clone()],
                    };
                    clauses.iter().enumerate().find_map(|(position, clause)| {
                        find_clause_label(clause, name, false).map(|label| (position, label))
                    })
                } else {
                    match &node {
                        Clause::Expression(expression) => match &expression.kind {
                            ExpressionKind::Label { body, .. } => {
                                find_label(body, name).map(|label| (0, Clause::Expression(label)))
                            }
                            _ => None,
                        },
                        _ => None,
                    }
                };
                let Some((position, label)) = found else {
                    report(Some(index), format!("Cannot find label `{name}'."));
                    return Ok(());
                };
                if index == 1
                    && let Clause::AssumeProve(assume_prove) = &statement
                    && is_in_scope_of_declaration(assume_prove, position)
                    && is_out_of_scope
                {
                    report(
                        Some(1),
                        format!(
                            "Accessing subexpression labeled `{name}' of ASSUME/PROVE clause {SCOPE_MESSAGE}"
                        ),
                    );
                    return Ok(());
                }
                let label = match label {
                    Clause::Expression(label) => label,
                    // `Generator.selectorToNode` returns a LabelNode of an ASSUME/PROVE as a fact.
                    _ if is_fact && args.is_empty() && index == selectors.len() - 1 => {
                        return Ok(());
                    }
                    _ => {
                        return Err(FrontError::NotYet(
                            "a labeled ASSUME/PROVE selected other than as a fact".to_owned(),
                        ));
                    }
                };
                let ExpressionKind::Label { params, .. } = &label.kind else {
                    return Ok(());
                };
                if args.len() != params.len() {
                    report(
                        Some(index),
                        format!("Label `{name}' used with wrong number of arguments."),
                    );
                    return Ok(());
                }
                node = Clause::Expression(label.clone());
                is_goal = false;
                is_suffices_open = false;
            }
            Selector::Operand(operand) => {
                let operand_name = get_operand_name(operand);
                if is_suffices_open {
                    if get_operand_index(operand, 1) != Some(0) {
                        report(
                            Some(index),
                            if matches!(node, Clause::AssumeProve(_)) {
                                "Accessing non-existent subexpression of a SUFFICES".to_owned()
                            } else {
                                format!("Nonexistent operand specified by `{operand_name}'.")
                            },
                        );
                        return Ok(());
                    }
                    is_suffices_open = false;
                    continue;
                }
                match &node {
                    Clause::NewSymbol(_) => return Ok(()),
                    Clause::Label(_) => {
                        return Err(FrontError::NotYet(
                            "a selection within a labeled ASSUME/PROVE".to_owned(),
                        ));
                    }
                    Clause::Expression(labeled) => {
                        let expression = get_label_body(labeled);
                        if is_literal(&expression) {
                            report(
                                Some(index),
                                "Selecting subexpression of expression that has none.".to_owned(),
                            );
                            return Ok(());
                        }
                        let kind = match &expression.kind {
                            ExpressionKind::Identifier { .. } => find_binding(
                                &expression.reference().unwrap_or_default(),
                                scope,
                                unit,
                            )
                            .map(|binding| binding.kind),
                            _ => None,
                        };
                        if matches!(kind, Some(SymbolKind::Variable | SymbolKind::New(_))) {
                            report(
                                Some(index),
                                format!(
                                    "Choosing operand `{operand_name}' of subexpression with no operands."
                                ),
                            );
                            return Ok(());
                        }
                        let operands = match &expression.kind {
                            ExpressionKind::Identifier { .. } => Some(Vec::new()),
                            _ => match get_binder(&expression).map(|binder| binder.sets) {
                                Some(sets) if !sets.is_empty() => Some(sets),
                                Some(_) => None,
                                None => match expression.kind {
                                    ExpressionKind::Except { .. } => None,
                                    _ => get_operands(&expression),
                                },
                            },
                        };
                        let Some(operands) = operands else {
                            return Ok(());
                        };
                        let Some(position) = get_operand_index(operand, operands.len()) else {
                            report(
                                Some(index),
                                format!("Nonexistent operand specified by `{operand_name}'."),
                            );
                            return Ok(());
                        };
                        node = Clause::Expression(operands[position].clone());
                        is_goal = false;
                    }
                    Clause::AssumeProve(assume_prove) => {
                        let clauses = get_clauses(assume_prove);
                        let Some(position) = get_operand_index(operand, clauses.len()) else {
                            report(
                                Some(index),
                                format!("Nonexistent operand specified by `{operand_name}'."),
                            );
                            return Ok(());
                        };
                        if is_in_scope_of_declaration(assume_prove, position)
                            && (!is_goal || is_out_of_scope)
                        {
                            report(
                                Some(index),
                                format!("Accessing ASSUME/PROVE clause {SCOPE_MESSAGE}"),
                            );
                            return Ok(());
                        }
                        let clause = clauses[position].clone();
                        if matches!(clause, Clause::NewSymbol(_)) && index != selectors.len() - 1 {
                            report(
                                Some(index),
                                "Selected a subexpression of a NEW clause of an ASSUME.".to_owned(),
                            );
                            return Ok(());
                        }
                        node = clause;
                        is_goal = false;
                    }
                }
            }
            _ => return Ok(()),
        }
    }
    if is_fact {
        return Ok(());
    }
    if matches!(node, Clause::Label(_)) {
        return Err(FrontError::NotYet(
            "a labeled ASSUME/PROVE selected as an expression".to_owned(),
        ));
    }
    if matches!(node, Clause::AssumeProve(_)) {
        report(
            None,
            "Selected ASSUME/PROVE instead of expression.".to_owned(),
        );
    }
    if matches!(node, Clause::NewSymbol(_)) {
        report(
            None,
            "Selected a NEW declaration as an expression or operator.".to_owned(),
        );
    }
    Ok(())
}

/// `Generator.generateLabel` reports a label where it may not appear, and skips the label's body.
fn is_label_reported(range: Option<&Range>, unit: &Unit) -> bool {
    let message = if unit.is_generated {
        None
    } else if !unit.has_label_scope {
        Some("Label not in definition or proof step.")
    } else if unit.is_label_forbidden {
        Some("Label not allowed within scope of declaration in nested ASSUME/PROVE.")
    } else if unit.is_in_except {
        Some("Labels inside EXCEPT clauses are not yet implemented.")
    } else {
        None
    };
    let (Some(message), Some(range)) = (message, range) else {
        return false;
    };
    unit.error(format_range(range), message.to_owned());
    true
}

/// `Generator.generateLabel` reports, after the label's body, each parameter that names no bound
/// name, then `formalParamsEqual` each parameter given twice, each name bound since the label
/// scope began that the label leaves out, and the parameters it adds, and then a label of a name
/// already used.
fn check_label(
    name: &Name,
    params: &[Name],
    param_ranges: &[Range],
    range: Option<&Range>,
    scope: &Scope,
    unit: &Unit,
) {
    let Some(range) = range else {
        return;
    };
    if unit.is_generated {
        return;
    }
    let location = format_range(range);
    let legal: Vec<Name> = params
        .iter()
        .enumerate()
        .filter(|(index, param)| {
            let is_legal =
                lookup_local(scope, param).is_some_and(|local| local.kind == SymbolKind::Parameter);
            if !is_legal && let Some(param_range) = param_ranges.get(*index) {
                unit.error(
                    format_range(param_range),
                    format!("Illegal parameter {param} of label `{name}'."),
                );
            }
            is_legal
        })
        .map(|(_, param)| param.clone())
        .collect();
    for (index, param) in legal.iter().enumerate() {
        if legal.iter().position(|other| other == param) != Some(index) {
            unit.error(
                location.clone(),
                format!("Repeated formal parameter {param} \nin label `{name}'."),
            );
        }
    }
    for param in unit.label_params.iter() {
        if !legal.contains(param) {
            unit.error(
                location.clone(),
                format!("Label {name} must contain formal parameter `{param}'."),
            );
        }
    }
    let mut extra: Vec<Name> = Vec::new();
    for param in &legal {
        if !unit.label_params.contains(param) && !extra.contains(param) {
            extra.push(param.clone());
        }
    }
    extra.extend(
        params
            .iter()
            .filter(|param| !legal.contains(param))
            .cloned(),
    );
    if !extra.is_empty() {
        unit.error(
            location.clone(),
            format!(
                "Label {name} declares extra parameter(s)  {}",
                extra
                    .iter()
                    .map(|param| format!("{param}  "))
                    .collect::<String>()
            ),
        );
    }
    if unit.labels.borrow().contains(name) {
        unit.error(location, format!("Duplicate label `{name}'."));
    }
    unit.labels.borrow_mut().insert(name.clone());
}

/// The unit of a label's body, which begins a label scope of its own.
fn get_label_unit<'a>(unit: &Unit<'a>) -> Unit<'a> {
    Unit {
        label_params: Rc::default(),
        labels: Rc::default(),
        ..unit.clone()
    }
}

/// Checks a name that selects part of a theorem or step, and tells whether it is one.
fn check_reference(expression: &Expr, scope: &Scope, unit: &Unit, is_fact: bool) -> Result<bool> {
    if !is_reference(expression) {
        return Ok(false);
    }
    let selectors = get_selectors(expression);
    let goal = match selectors.first() {
        Some(Selector::Name { name, .. }) if selectors.len() > 1 => lookup_local(scope, name)
            .and_then(|local| local.goal.clone())
            .or_else(|| unit.goals.get(name).cloned()),
        _ => None,
    };
    if let Some(goal) = &goal {
        check_selection(expression, &selectors, goal, scope, unit, is_fact)?;
    }
    Ok(goal.is_some())
}

fn apply_arity(expression: &Expression) -> usize {
    match &expression.kind {
        ExpressionKind::Apply { args, .. } => args.len(),
        _ => 0,
    }
}

/// `Generator.selectorToNode` reports an unknown operator and goes on without analyzing its
/// arguments, so its arity is undefined. It does the same for an operator given the wrong number
/// of arguments, and for a name that selects nothing, after the arguments of the parts before.
fn get_symbol_arity(
    expression: &Expr,
    name: &Name,
    scope: &Scope,
    unit: &Unit,
) -> Result<Option<usize>> {
    let location = &expression.location;
    if is_selection_reported(expression, scope, unit)? {
        return Ok(None);
    }
    if let Some(renamed) = unit
        .tables
        .renamed_arities
        .borrow()
        .get(&address(expression))
    {
        return Ok(Some(renamed.1));
    }
    if is_key(name) {
        return Ok(Some(apply_arity(expression)));
    }
    let local = lookup_local(scope, name);
    if local.as_ref().is_some_and(|local| local.is_non_fact) {
        unit.error(
            format_range(&get_spelled_name_range(expression, name)),
            "Step number of non-expression step used as an expression.".to_owned(),
        );
        return Ok(None);
    }
    // `Generator.selectorToNode` rejects a step that asserts no expression named as an
    // expression, after it checks the step's arguments, which it takes none of.
    if let Some(unselectable) = local.as_ref().and_then(|local| local.unselectable)
        && !unit.is_fact
    {
        if apply_arity(expression) > 0 {
            return Err(FrontError::NotYet(format!(
                "the step {name} given arguments named as an expression"
            )));
        }
        unit.error(
            format_range(&get_spelled_name_range(expression, name)),
            unselectable.to_owned(),
        );
        return Ok(None);
    }
    if check_reference(expression, scope, unit, false)? || (is_step_name(name) && local.is_some()) {
        return Ok(Some(apply_arity(expression)));
    }
    let is_operator_reference = matches!(expression.kind, ExpressionKind::OperatorReference { .. });
    if let Some(local) = local {
        if !is_operator_reference {
            expression.resolved.is_local.set(true);
        }
        return Ok(Some(local.arity));
    }
    if let Some(symbol) = find_symbol(name, unit) {
        *expression.resolved.key.borrow_mut() = Some(symbol.key.clone());
        unit.tables
            .renamed_arities
            .borrow_mut()
            .insert(address(expression), (expression.clone(), symbol.arity));
        return Ok(Some(symbol.arity));
    }
    // A name such as Inv!P1 selects the label P1 of a definition or theorem, which takes its own
    // arguments.
    let prefix = name.find('!').map_or("", |index| &name[..index]);
    let is_selected = !prefix.is_empty()
        && (lookup_local(scope, prefix).is_some()
            || find_symbol(prefix, unit).is_some()
            || unit.facts.borrow().contains(prefix));
    if is_selected {
        return Ok(Some(apply_arity(expression)));
    }
    let spelling = match &expression.kind {
        ExpressionKind::Identifier { .. } => None,
        _ => get_spelling(expression),
    }
    .unwrap_or_else(|| name.clone());
    let range = format_range(&if matches!(expression.kind, ExpressionKind::Apply { .. })
        && &*spelling == "-."
    {
        get_name_range(location, "-")
    } else {
        get_spelled_name_range(expression, name)
    });
    let current = find_current(scope, name, unit, None);
    // `Generator.selectorToNode` checks an INSTANCE's arguments, at the arguments or else at the
    // whole name, and then, but in a fact, that the name selects an operator of the module.
    if let Some(instance) = current
        .as_ref()
        .filter(|local| local.kind == SymbolKind::Instance)
    {
        let arguments_range = match &expression.kind {
            ExpressionKind::Apply {
                arguments_range, ..
            } => arguments_range.as_ref(),
            _ => None,
        };
        let (range, message) = if apply_arity(expression) == instance.arity {
            // A fact may name an instance, which `UseOrHideNode.factCheck` checks.
            if unit.is_fact {
                return Err(FrontError::NotYet(format!(
                    "the instance {name} named as a fact"
                )));
            }
            // SANY analyzes the arguments against the INSTANCE's parameters first
            // (`generateExprOrOpArg`), which the front end doesn't follow.
            if instance.arity != 0 {
                return Err(FrontError::NotYet(format!(
                    "the instance {name} applied to its arguments as an expression"
                )));
            }
            (
                Some(get_spelled_name_range(expression, name)),
                format!("Operator name {name} is incomplete."),
            )
        } else {
            (
                arguments_range.or(location.range.as_ref()).cloned(),
                format!("The operator {name} requires {} arguments.", instance.arity),
            )
        };
        let Some(range) = range else {
            return Err(FrontError::NotYet(format!(
                "the instance {name} named as an expression without a place"
            )));
        };
        unit.error(format_range(&range), message);
        return Ok(None);
    }
    // It rejects a theorem whose statement is an ASSUME/PROVE named as an expression, after it
    // checks the theorem's arguments, which it takes none of.
    let is_assume_prove = current
        .as_ref()
        .is_some_and(|local| local.kind == SymbolKind::Theorem)
        && unit
            .goals
            .get(name)
            .is_some_and(|goal| matches!(goal.statement, Statement::AssumeProve(_)));
    if is_assume_prove && !unit.is_fact && apply_arity(expression) == 0 {
        unit.error(
            format_range(&get_spelled_name_range(expression, name)),
            "ASSUME/PROVE used where an expression is required.".to_owned(),
        );
        return Ok(None);
    }
    // A theorem or an assumption whose statement is an expression is one SANY takes, which the
    // front end doesn't follow.
    let is_named = unit.facts.borrow().contains(name)
        || current.is_some_and(|local| local.binding().kind == SymbolKind::Theorem);
    if is_named {
        return Err(FrontError::NotYet(format!(
            "the name {name} of a theorem, an assumption or an instance as an expression"
        )));
    }
    if !is_operator_symbol(name) || is_step_name(name) {
        unit.error(range, format!("Unknown operator: `{name}'."));
        return Ok(None);
    }
    unit.error(
        range,
        format!("Could not find declaration or definition of symbol '{spelling}'."),
    );
    if let (Some(fixity), Some(full)) = (get_fixity(expression), &location.range) {
        unit.error(
            format_range(full),
            format!("Couldn't resolve {fixity} operator symbol `{spelling}'."),
        );
    }
    Ok(None)
}

fn resolve_bounds(bounds: &[Bound], scope: &Scope, unit: &Unit) -> Result<Scope> {
    for bound in bounds {
        resolve_expression(&bound.set, scope, unit)?;
    }
    Ok(bounds.iter().fold(scope.clone(), |current, bound| {
        bind_names(
            &current,
            bound.pattern.names(),
            pattern_ranges(&bound.pattern),
            unit,
        )
    }))
}

fn is_referenced(expression: &Expression, name: &str) -> bool {
    (matches!(expression.kind, ExpressionKind::Identifier { .. })
        && expression.reference().as_deref() == Some(name)
        && expression.is_locally_resolved())
        || expression
            .children()
            .iter()
            .any(|child| is_referenced(child, name))
}

/// Gives each reference to name in the expression the arity given.
fn set_reference_arities(expression: &Expr, name: &str, arity: usize, tables: &Tables) {
    if matches!(
        expression.kind,
        ExpressionKind::Identifier { .. } | ExpressionKind::Apply { .. }
    ) && expression.reference().as_deref() == Some(name)
    {
        tables
            .renamed_arities
            .borrow_mut()
            .insert(address(expression), (expression.clone(), arity));
    }
    for child in expression.children() {
        set_reference_arities(&child, name, arity, tables);
    }
}

fn mark_recursive_constructions(expression: &Expression, name: &str) {
    if let ExpressionKind::FunctionConstruction { body, .. } = &expression.kind
        && is_referenced(body, name)
    {
        expression.resolved.is_recursive.set(true);
    }
    for child in expression.children() {
        mark_recursive_constructions(&child, name);
    }
}

/// `Generator.processOperator` binds the parameters, reports a name already bound unless a
/// RECURSIVE declaration of this level awaits the definition, analyzes the body, and then binds the
/// name. `processFunction` binds the bound names before it looks up the name, and binds the name
/// only where nothing else does. `recursive` holds the declarations of this level. Tells whether to
/// bind the name.
fn resolve_definition(
    definition: &Rc<Definition>,
    scope: &Scope,
    outer: &Unit,
    recursive: &[Rc<Local>],
) -> Result<bool> {
    let is_function = matches!(definition.kind, DefinitionKind::Function { .. });
    let unit = Unit {
        has_label_scope: true,
        label_params: Rc::new(match &definition.kind {
            DefinitionKind::Function { bounds } => get_bound_names(bounds),
            DefinitionKind::Operator { .. } => Vec::new(),
        }),
        labels: Rc::default(),
        ..outer.clone()
    };
    let name = &definition.name;
    let range = definition.location.range.as_ref();
    let report = |message: String| {
        if let Some(range) = range
            && !unit.is_generated
        {
            unit.error(format_range(range), message);
        }
    };
    let inner = match &definition.kind {
        DefinitionKind::Function { bounds } => resolve_bounds(bounds, scope, &unit)?,
        DefinitionKind::Operator { params, .. } => bind_params(scope, params, &unit),
    };
    let current = find_current(&inner, name, &unit, range);
    let is_declared = current.as_ref().is_some_and(|current| {
        current.is_pending.get() && recursive.iter().any(|item| Rc::ptr_eq(item, current))
    });
    if current
        .as_ref()
        .is_some_and(|current| current.is_pending.get())
        && !is_declared
    {
        report(format!(
            "Recursive {} {name} defined at wrong LET/IN level.",
            if is_function { "function" } else { "operator" }
        ));
    } else if is_function
        && is_declared
        && current.as_ref().is_some_and(|current| current.arity != 0)
    {
        report(format!(
            "Function {name} has operator arguments in its RECURSIVE declaration."
        ));
    } else if current.is_some() && !is_declared {
        report(if is_function {
            format!("Function name `{name}' already defined or declared.")
        } else {
            format!("Operator {name} already defined or declared.")
        });
    }
    // SANY analyzes the body with the arity of the RECURSIVE declaration, and compares only the
    // arity of the last parameter.
    if let (Some(current), DefinitionKind::Operator { params, .. }, true) = (
        current.as_ref().filter(|_| is_declared),
        &definition.kind,
        unit.tables.is_collecting.get(),
    ) && (current.arity != params.len() || params.last().is_some_and(|param| param.arity != 0))
    {
        report(format!(
            "Definition of {name} has different arity than its RECURSIVE declaration."
        ));
        set_reference_arities(&definition.body, name, current.arity, &unit.tables);
    }
    if is_function {
        let own = Local::new(name.clone(), parameter(0, range.cloned()), inner);
        resolve_expression(&definition.body, &Some(Rc::new(own)), &unit)?;
        mark_recursive_constructions(&definition.body, name);
        definition
            .is_self_referential
            .set(Some(is_referenced(&definition.body, name)));
    } else {
        resolve_expression(&definition.body, &inner, &unit)?;
    }
    // A function whose RECURSIVE declaration has parameters leaves it undefined.
    if let Some(current) = &current
        && is_declared
        && !(is_function && current.arity != 0)
    {
        current.is_pending.set(false);
        *current.range.borrow_mut() = range.cloned();
        return Ok(false);
    }
    if is_function {
        return Ok(current.is_none());
    }
    let existing = find_current(scope, name, &unit, range).map(|local| local.binding());
    Ok(is_bindable(
        name,
        existing.as_ref(),
        &Binding {
            kind: SymbolKind::Definition,
            arity: get_arity(definition),
            params: None,
            range: range.cloned(),
        },
        &unit,
    ))
}

/// Binds the operators a LET declares RECURSIVE as `processRecursive` does, with the arity of the
/// declaration, and records them with the LET's level. Returns the scope and what they bind.
/// `check_recursive` has left only definitions with the declaration's shape.
fn bind_let_recursive(
    recursive: &[Rc<Declaration>],
    definitions: &[Rc<Definition>],
    scope: &Scope,
    unit: &Unit,
) -> Result<(Scope, Vec<Rc<Local>>)> {
    let mut declared = scope.clone();
    let mut locals = Vec::new();
    if recursive.is_empty() {
        return Ok((declared, locals));
    }
    if unit.is_generated {
        return Err(FrontError::NotYet(
            "a LET with RECURSIVE declarations analyzed again".to_owned(),
        ));
    }
    for declaration in recursive {
        if find_current(&declared, &declaration.name, unit, None).is_some() {
            return Err(FrontError::NotYet(format!(
                "a LET that declares RECURSIVE {}, a name already bound",
                declaration.name
            )));
        }
        let is_defined = definitions
            .iter()
            .any(|definition| definition.name == declaration.name);
        let local = Rc::new(Local {
            is_pending: Cell::new(true),
            ..Local::new(
                declaration.name.clone(),
                Binding {
                    kind: SymbolKind::Definition,
                    arity: declaration.arity,
                    params: Some(Rc::from(vec![0; declaration.arity])),
                    // Where SANY reports a second declaration of it.
                    range: (!is_defined)
                        .then(|| declaration.location.range.clone())
                        .flatten(),
                },
                declared,
            )
        });
        let mut records = unit.let_recursive.borrow_mut();
        if !records
            .iter()
            .any(|(_, recorded, _)| Rc::ptr_eq(recorded, declaration))
        {
            records.push((unit.let_level, declaration.clone(), local.clone()));
        }
        locals.push(local.clone());
        declared = Some(local);
    }
    Ok((declared, locals))
}

/// SANY analyzes an INSTANCE in a LET where it appears, before the definitions that follow it,
/// which tla-ts generates at its location and analyzes without reporting.
fn resolve_definitions(
    definitions: &[Rc<Definition>],
    scope: &Scope,
    unit: &Unit,
    instances: &[Rc<Instance>],
    declared_recursive: &[Rc<Local>],
) -> Result<Scope> {
    let recursive = declared_recursive;
    let declared = scope.clone();
    let mut pending: Vec<Rc<Instance>> = if unit.is_generated {
        Vec::new()
    } else {
        instances.to_vec()
    };
    let resolve_instances = |current: Scope,
                             pending: &mut Vec<Rc<Instance>>,
                             is_due: &dyn Fn(&Instance) -> bool|
     -> Result<Scope> {
        let count = pending
            .iter()
            .position(|instance| !is_due(instance))
            .unwrap_or(pending.len());
        pending
            .drain(..count)
            .collect::<Vec<_>>()
            .iter()
            .try_fold(current, |parent, instance| {
                resolve_local_instance(instance, &parent, unit)
            })
    };
    let mut resolved = declared;
    for definition in definitions {
        let previous = resolved.clone();
        let current = if is_key(&definition.name) {
            previous
        } else {
            resolve_instances(previous, &mut pending, &|instance| {
                !is_before(definition.location.position(), instance.location.position())
            })?
        };
        let local = Local::new(
            definition.name.clone(),
            Binding {
                kind: SymbolKind::Definition,
                arity: get_arity(definition),
                params: None,
                range: definition.location.range.clone(),
            },
            current.clone(),
        );
        if is_instantiated(definition) {
            resolved = Some(Rc::new(local));
            continue;
        }
        let is_instanced = instances
            .iter()
            .any(|instance| instance.location == definition.location);
        let is_generated = unit.is_generated || definition.is_local || is_key(&definition.name);
        let inner = if is_instanced {
            Unit {
                is_generated: true,
                errors: Rc::default(),
                warnings: Rc::default(),
                ..unit.clone()
            }
        } else if is_generated {
            Unit {
                is_generated,
                ..unit.clone()
            }
        } else {
            unit.clone()
        };
        resolved = if resolve_definition(definition, &current, &inner, recursive)? {
            Some(Rc::new(Local {
                params: Some(get_param_arities(definition)),
                function_params: get_function_params(definition),
                ..local
            }))
        } else {
            current
        };
    }
    resolve_instances(resolved, &mut pending, &|_| true)
}

/// The INSTANCE that a name such as `K!C` starts with, whose arguments SANY requires at its name.
fn find_instance(name: &str, scope: &Scope, unit: &Unit) -> Option<(Name, usize)> {
    let prefix = name.split('!').next().unwrap_or(name);
    if prefix == name {
        return None;
    }
    let binding = find_current(scope, prefix, unit, None)?;
    (binding.kind == SymbolKind::Instance).then(|| (Rc::from(prefix), binding.arity))
}

/// `Generator.selectorToNode` reports an INSTANCE given the wrong number of arguments at its name,
/// as in `K!C` or `K(1, 2)!C`, and goes on without analyzing them. Tells whether it reports one.
fn is_instance_arity_reported(expression: &Expression, scope: &Scope, unit: &Unit) -> bool {
    let (count, first_range) = match &expression.kind {
        ExpressionKind::Identifier { .. } => (0, None),
        ExpressionKind::Apply {
            argument_counts,
            argument_ranges,
            ..
        } => (
            argument_counts
                .as_ref()
                .and_then(|counts| counts.first().copied())
                .unwrap_or(0),
            argument_ranges
                .as_ref()
                .and_then(|ranges| ranges.first().cloned().flatten()),
        ),
        _ => return false,
    };
    let Some((name, arity)) =
        find_instance(&expression.reference().unwrap_or_default(), scope, unit)
    else {
        return false;
    };
    if count == arity {
        return false;
    }
    if let Some(range) = first_range.as_ref().or(expression.location.range.as_ref()) {
        unit.error(
            format_range(range),
            format!("The operator {name} requires {arity} arguments."),
        );
    }
    true
}

/// `Generator.generateExprOrOpArg` analyzes an argument as an expression, unless a defined operator
/// takes an operator in its place, which a name, a built-in operator, or a LAMBDA of the
/// parameter's arity must give. `OpDefNode#match` then reports each argument that gives no such
/// operator, or one whose own parameters take operators. tla-ts lets an operator whose parameters
/// it does not know take any argument.
fn resolve_apply(expression: &Expr, scope: &Scope, unit: &Unit) -> Result<()> {
    let ExpressionKind::Apply {
        args,
        arguments_range,
        selector_ranges,
        ..
    } = &expression.kind
    else {
        return Ok(());
    };
    if is_instance_arity_reported(expression, scope, unit) {
        return Ok(());
    }
    let operator = expression.reference().unwrap_or_default();
    let callee = find_binding(&operator, scope, unit);
    let Some(arity) = get_symbol_arity(expression, &operator, scope, unit)? else {
        return Ok(());
    };
    if arity != args.len() {
        let instance_arity = find_instance(&operator, scope, unit).map_or(0, |instance| instance.1);
        unit.error(
            format_range(
                &arguments_range
                    .clone()
                    .unwrap_or_else(|| get_spelled_name_range(expression, &operator)),
            ),
            format!(
                "The operator {operator} requires {} arguments.",
                arity as i64 - instance_arity as i64
            ),
        );
        return Ok(());
    }
    let params: Option<Rc<[usize]>> = match &callee {
        None => None,
        Some(callee) if callee.kind == SymbolKind::Definition => callee.params.clone(),
        Some(_) => Some(Rc::from([])),
    };
    let Some(params) = params else {
        for arg in args {
            resolve_argument(arg, scope, unit)?;
        }
        return Ok(());
    };
    let report = |range: Option<&Range>, message: String| {
        if let Some(range) = range {
            unit.error(format_range(range), message);
        }
    };
    let mut matched = Vec::with_capacity(args.len());
    for (index, arg) in args.iter().enumerate() {
        let expected = params.get(index).copied().unwrap_or(0);
        let range = arg.location.range.as_ref();
        if expected == 0 {
            // SANY fails on an operator here with an internal error, so tla-ts words it as it
            // does for a name.
            match &arg.kind {
                ExpressionKind::Lambda {
                    operator: Some(operator),
                    ..
                } => report(
                    range,
                    format!("The operator {operator} requires 1 arguments."),
                ),
                ExpressionKind::Lambda { .. } if range.is_some() => report(
                    range,
                    "LAMBDA expression used where an expression is required.".to_owned(),
                ),
                ExpressionKind::OperatorReference { operator, .. } => {
                    let name = arg.reference().unwrap_or_else(|| operator.clone());
                    if let Some(arg_arity) = get_symbol_arity(arg, &name, scope, unit)? {
                        report(
                            range,
                            format!(
                                "The operator {} requires {arg_arity} arguments.",
                                arg.reference().unwrap_or_default()
                            ),
                        );
                    }
                }
                _ => resolve_expression(arg, scope, unit)?,
            }
            matched.push(true);
            continue;
        }
        // A name that selects a subexpression gives an operator of the names it leaves unbound.
        if let ExpressionKind::Lambda {
            params: lambda_params,
            operator: lambda_operator,
            ..
        } = &arg.kind
        {
            resolve_expression(arg, scope, unit)?;
            let is_matched = lambda_params.len() == expected;
            if !is_matched && unit.tables.is_selection(arg) {
                report(
                    range,
                    format!(
                        "Expected arity {expected} but found operator of arity {}.",
                        lambda_params.len()
                    ),
                );
            } else if !is_matched && range.is_some() && lambda_operator.is_none() {
                let at = selector_ranges
                    .as_ref()
                    .and_then(|ranges| ranges.last().cloned())
                    .unwrap_or_else(|| get_spelled_name_range(expression, &operator));
                report(
                    Some(&at),
                    format!(
                        "Lambda expression with arity {} used as argument {} of operator `{operator}', \nbut an operator of arity {expected} is required.",
                        lambda_params.len(),
                        index + 1
                    ),
                );
            }
            matched.push(is_matched);
            continue;
        }
        if matches!(arg.kind, ExpressionKind::Subexpression { .. }) {
            resolve_expression(arg, scope, unit)?;
            matched.push(true);
            continue;
        }
        // Generator.selectorToNode: a name such as K(1)!C names an operator, but none of its
        // parts may take arguments.
        if let ExpressionKind::Apply {
            argument_counts: Some(counts),
            selector_ranges: arg_selector_ranges,
            ..
        } = &arg.kind
            && counts.last() == Some(&0)
        {
            let position = counts.iter().position(|count| *count > 0);
            let arg_name = arg.reference().unwrap_or_default();
            let part = position
                .and_then(|position| arg_name.split('!').nth(position))
                .unwrap_or("undefined");
            report(
                position.and_then(|position| {
                    arg_selector_ranges
                        .as_ref()
                        .and_then(|ranges| ranges.get(position))
                }),
                format!("Selector `{part}' should not have argument(s)."),
            );
            matched.push(false);
            continue;
        }
        if !matches!(
            arg.kind,
            ExpressionKind::Identifier { .. } | ExpressionKind::OperatorReference { .. }
        ) {
            report(
                range,
                format!(
                    "An expression appears as argument number {} (counting from 1) to operator '{operator}', in a position an operator is required.",
                    index + 1
                ),
            );
            matched.push(false);
            continue;
        }
        let name = arg.reference().unwrap_or_default();
        // `get_symbol_arity` words a theorem, a step or an INSTANCE named as an expression, which
        // SANY checks against the expected arity first.
        if find_current(scope, &name, unit, None)
            .is_some_and(|local| matches!(local.kind, SymbolKind::Theorem | SymbolKind::Instance))
        {
            return Err(FrontError::NotYet(format!(
                "the theorem, step or instance {name} where an operator is required"
            )));
        }
        let arg_params = find_binding(&name, scope, unit).and_then(|binding| binding.params);
        let arg_arity = get_symbol_arity(arg, &name, scope, unit)?;
        if matches!(arg.kind, ExpressionKind::Identifier { .. })
            && let Some(arg_arity) = arg_arity
            && arg_arity != expected
        {
            report(
                Some(&get_spelled_name_range(arg, &name)),
                format!("Expected arity {expected} but found operator of arity {arg_arity}."),
            );
        }
        matched.push(
            arg_arity == Some(expected)
                && arg_params.is_none_or(|params| params.iter().all(|param| *param == 0)),
        );
    }
    for (index, is_matched) in matched.into_iter().enumerate() {
        if !is_matched {
            report(
                expression.location.range.as_ref(),
                format!(
                    "Argument number {} to operator '{operator}' \nshould be a {}-parameter operator.",
                    index + 1,
                    params
                        .get(index)
                        .map_or_else(|| "undefined".to_owned(), |param| param.to_string())
                ),
            );
        }
    }
    Ok(())
}

/// An argument may name an operator that takes arguments of its own.
fn resolve_argument(arg: &Expr, scope: &Scope, unit: &Unit) -> Result<()> {
    if matches!(arg.kind, ExpressionKind::Identifier { .. }) {
        get_symbol_arity(arg, &arg.reference().unwrap_or_default(), scope, unit)?;
        Ok(())
    } else {
        resolve_expression(arg, scope, unit)
    }
}

/// Reports the error of a name that selects nothing, after the arguments SANY analyzes before it.
fn is_selection_reported(expression: &Expr, scope: &Scope, unit: &Unit) -> Result<bool> {
    let Some((args, error)) = unit.tables.get_error(expression) else {
        return Ok(false);
    };
    for arg in &args {
        resolve_argument(arg, scope, unit)?;
    }
    unit.errors.borrow_mut().push(error);
    Ok(true)
}

// The parameters of a function definition: a bound each, a tuple of names one.
fn get_function_params(definition: &Definition) -> Option<usize> {
    match &definition.kind {
        DefinitionKind::Function { bounds } => Some(
            bounds
                .iter()
                .map(|bound| bound.pattern.names().len().min(1))
                .sum(),
        ),
        DefinitionKind::Operator { .. } => None,
    }
}

/// SANY rejects a function a module or a LET defines applied to several arguments, other than as
/// many as it has parameters; one argument may be a tuple of them.
fn check_function_arity(
    expression: &Expression,
    function: &Expression,
    count: usize,
    scope: &Scope,
    unit: &Unit,
) {
    if count < 2 {
        return;
    }
    let ExpressionKind::Identifier { name, .. } = &function.kind else {
        return;
    };
    let params = if function.is_locally_resolved() {
        lookup_local(scope, name).and_then(|local| local.function_params)
    } else {
        let key = function.reference().unwrap_or_default();
        unit.definitions
            .get(&key)
            .and_then(|definition| get_function_params(definition))
    };
    let Some(params) = params else {
        return;
    };
    if count != params
        && let Some(range) = &expression.location.range
    {
        unit.error(
            format_range(range),
            format!(
                "Function '{name}' is defined with {params} parameters, but is applied to {count} arguments."
            ),
        );
    }
}

fn resolve_all(expressions: &[Expr], scope: &Scope, unit: &Unit) -> Result<()> {
    for expression in expressions {
        resolve_expression(expression, scope, unit)?;
    }
    Ok(())
}

fn resolve_expression(expression: &Expr, scope: &Scope, unit: &Unit) -> Result<()> {
    if !unit.is_generated && unit.tables.is_selection(expression) {
        return resolve_expression(
            expression,
            scope,
            &Unit {
                is_generated: true,
                ..unit.clone()
            },
        );
    }
    match &expression.kind {
        ExpressionKind::Number { .. }
        | ExpressionKind::Decimal { .. }
        | ExpressionKind::String { .. } => Ok(()),
        // SANY's generator defines @ only in an EXCEPT's new value.
        ExpressionKind::ExceptAt => {
            if !unit.is_in_except
                && unit.step_at != Some(Rc::as_ptr(expression) as usize)
                && let Some(range) = &expression.location.range
            {
                unit.error(
                    format_range(range),
                    "@ used where its meaning is not defined.".to_owned(),
                );
            }
            Ok(())
        }
        ExpressionKind::Identifier { .. } => {
            if is_instance_arity_reported(expression, scope, unit) {
                return Ok(());
            }
            let name = expression.reference().unwrap_or_default();
            let arity = get_symbol_arity(expression, &name, scope, unit)?;
            if let Some(arity) = arity
                && arity > 0
            {
                unit.error(
                    format_range(&get_spelled_name_range(expression, &name)),
                    format!("The operator {name} requires {arity} arguments."),
                );
            }
            Ok(())
        }
        ExpressionKind::OperatorReference { .. } => {
            let name = expression.reference().unwrap_or_default();
            get_symbol_arity(expression, &name, scope, unit)?;
            Ok(())
        }
        ExpressionKind::Apply { .. } => resolve_apply(expression, scope, unit),
        ExpressionKind::Lambda {
            params,
            param_ranges,
            body,
            ..
        } => resolve_expression(
            body,
            &bind_names(scope, params, param_ranges.as_deref().unwrap_or(&[]), unit),
            &unit.with_label_params(params),
        ),
        ExpressionKind::Junction { operands, .. } => resolve_all(operands, scope, unit),
        ExpressionKind::Prime(inner)
        | ExpressionKind::Unchanged(inner)
        | ExpressionKind::Enabled(inner)
        | ExpressionKind::Always(inner)
        | ExpressionKind::Eventually(inner) => resolve_expression(inner, scope, unit),
        ExpressionKind::If {
            condition,
            consequent,
            alternative,
        } => resolve_all(
            &[condition.clone(), consequent.clone(), alternative.clone()],
            scope,
            unit,
        ),
        ExpressionKind::Case { arms, other } => {
            for arm in arms {
                resolve_expression(&arm.condition, scope, unit)?;
                resolve_expression(&arm.body, scope, unit)?;
            }
            match other {
                Some(other) => resolve_expression(other, scope, unit),
                None => Ok(()),
            }
        }
        ExpressionKind::Let {
            definitions,
            instances,
            recursive,
            body,
        } => {
            // `Generator.processLetIn` reads the definitions a level deeper, where an operator
            // declared RECURSIVE at another level is defined at the wrong one.
            let level = Unit {
                let_level: unit.let_level + 1,
                ..unit.clone()
            };
            let (declared, locals) = bind_let_recursive(recursive, definitions, scope, &level)?;
            let inner = resolve_definitions(
                definitions,
                &declared,
                &level,
                instances.as_deref().unwrap_or(&[]),
                &locals,
            )?;
            // `checkForUndefinedRecursiveOps`: at the end of the definitions of a LET that leaves
            // one undefined, SANY reports each operator declared RECURSIVE at that level and not
            // defined, of any LET it has read.
            if locals.iter().any(|local| local.is_pending.get()) {
                let reported: Vec<Rc<Declaration>> = unit
                    .let_recursive
                    .borrow()
                    .iter()
                    .filter(|(declared_level, _, local)| {
                        *declared_level == level.let_level && local.is_pending.get()
                    })
                    .map(|(_, declaration, _)| declaration.clone())
                    .collect();
                for declaration in reported {
                    let Some(range) = &declaration.location.range else {
                        return Err(FrontError::NotYet(
                            "a RECURSIVE declaration without a place".to_owned(),
                        ));
                    };
                    level.error(
                        format_range(range),
                        format!(
                            "Symbol {} declared in RECURSIVE statement but not defined.",
                            declaration.name
                        ),
                    );
                }
            }
            resolve_expression(body, &inner, unit)
        }
        ExpressionKind::Quantified { bounds, body, .. }
        | ExpressionKind::FunctionConstruction { bounds, body } => resolve_expression(
            body,
            &resolve_bounds(bounds, scope, unit)?,
            &unit.with_label_params(&get_bound_names(bounds)),
        ),
        ExpressionKind::UnboundedQuantifier {
            names,
            name_ranges,
            body,
            ..
        } => resolve_expression(
            body,
            &bind_names(scope, names, name_ranges, unit),
            &unit.with_label_params(names),
        ),
        ExpressionKind::Choose { pattern, set, body } => {
            if let Some(set) = set {
                resolve_expression(set, scope, unit)?;
            }
            let names = get_pattern_names(pattern);
            resolve_expression(
                body,
                &bind_names(scope, &names, pattern_ranges(pattern), unit),
                &unit.with_label_params(&names),
            )
        }
        ExpressionKind::SetEnumeration(elements) | ExpressionKind::Tuple(elements) => {
            resolve_all(elements, scope, unit)
        }
        ExpressionKind::SetFilter { bound, predicate } => resolve_expression(
            predicate,
            &resolve_bounds(std::slice::from_ref(bound), scope, unit)?,
            &unit.with_label_params(bound.pattern.names()),
        ),
        ExpressionKind::SetMap {
            expression: mapped,
            bounds,
        } => resolve_expression(
            mapped,
            &resolve_bounds(bounds, scope, unit)?,
            &unit.with_label_params(&get_bound_names(bounds)),
        ),
        ExpressionKind::FunctionSet { domain, range } => {
            resolve_all(&[domain.clone(), range.clone()], scope, unit)
        }
        ExpressionKind::Record { fields, .. } => {
            for (index, field) in fields.iter().enumerate() {
                if fields[..index]
                    .iter()
                    .any(|earlier| earlier.name == field.name)
                {
                    unit.error(
                        format_range(
                            &field
                                .location
                                .range
                                .clone()
                                .unwrap_or_else(|| get_name_range(&field.location, &field.name)),
                        ),
                        "Non-unique fields in constructor.".to_owned(),
                    );
                }
                resolve_expression(&field.value, scope, unit)?;
            }
            Ok(())
        }
        ExpressionKind::Except { function, updates } => {
            resolve_expression(function, scope, unit)?;
            for update in updates {
                for step in &update.path {
                    if let ExceptPathStep::Index(args) = step {
                        resolve_all(args, scope, unit)?;
                    }
                }
                resolve_expression(
                    &update.value,
                    scope,
                    &Unit {
                        is_in_except: true,
                        ..unit.clone()
                    },
                )?;
            }
            Ok(())
        }
        ExpressionKind::FunctionApplication { function, args } => {
            resolve_expression(function, scope, unit)?;
            resolve_all(args, scope, unit)?;
            check_function_arity(expression, function, args.len(), scope, unit);
            Ok(())
        }
        // tla-ts leaves the arguments of [e1, ..., en] unresolved, as SANY rejects it.
        ExpressionKind::Bracket(_) => Ok(()),
        ExpressionKind::FieldAccess { record, .. } => resolve_expression(record, scope, unit),
        ExpressionKind::Product(factors) => resolve_all(factors, scope, unit),
        ExpressionKind::Action {
            action, subscript, ..
        } => resolve_all(&[action.clone(), subscript.clone()], scope, unit),
        ExpressionKind::Fairness {
            subscript, action, ..
        } => resolve_all(&[subscript.clone(), action.clone()], scope, unit),
        ExpressionKind::Label {
            name,
            params,
            param_ranges,
            body,
        } => {
            if is_label_reported(expression.location.range.as_ref(), unit) {
                return Ok(());
            }
            resolve_expression(body, scope, &get_label_unit(unit))?;
            check_label(
                name,
                params,
                param_ranges,
                expression.location.range.as_ref(),
                scope,
                unit,
            );
            Ok(())
        }
        ExpressionKind::Subexpression { selectors, .. } => {
            if is_selection_reported(expression, scope, unit)? {
                return Ok(());
            }
            for selector in selectors {
                for arg in selector.args() {
                    resolve_argument(arg, scope, unit)?;
                }
            }
            check_reference(expression, scope, unit, false)?;
            Ok(())
        }
    }
}

/// `Generator.generateUseOrHide` looks up a fact that is a name as it looks up a name in an
/// expression, except that the name may select an ASSUME/PROVE or a NEW clause or name a theorem
/// or assumption, and analyzes any other fact as an expression.
fn check_facts(facts: &[Fact], scope: &Scope, unit: &Unit) -> Result<()> {
    for fact in facts {
        let fact = match fact {
            Fact::Expression(fact) => fact,
            Fact::Module { name, .. } if is_module_found(name, unit) => continue,
            // `generateUseOrHide` reports a module its symbol table doesn't hold, which no
            // recording shows.
            Fact::Module { .. } => {
                return Err(FrontError::NotYet(
                    "a module named as a fact that SANY may not find".to_owned(),
                ));
            }
        };
        if is_instance_arity_reported(fact, scope, unit)
            || check_reference(fact, scope, unit, true)?
        {
            continue;
        }
        let name = match fact.kind {
            ExpressionKind::Identifier { .. } | ExpressionKind::Apply { .. } => {
                fact.reference().unwrap_or_default()
            }
            _ => Rc::from(""),
        };
        if matches!(fact.kind, ExpressionKind::Identifier { .. })
            && lookup_local(scope, &name).is_some_and(|local| local.is_non_fact)
        {
            unit.error(
                format_range(&get_spelled_name_range(fact, &name)),
                "Step number of non-fact used as a fact".to_owned(),
            );
        } else if !unit.facts.borrow().contains(&name) {
            resolve_expression(
                fact,
                scope,
                &Unit {
                    is_fact: true,
                    ..unit.clone()
                },
            )?;
        }
    }
    Ok(())
}

/// `SymbolTable.resolveModule` finds a module of the unit's table, or, as `generateUseOrHide`
/// adds, the current module.
fn is_module_found(name: &str, unit: &Unit) -> bool {
    unit.modules
        .get(name)
        .is_some_and(|from| (from.line, from.column) <= (unit.location.line, unit.location.column))
}

/// `generateUseOrHide` rejects a DEF entry that names no defined operator, theorem or assumption:
/// an unknown name, which `selectorToNode` reports first, or a built-in operator, a constant, a
/// variable, a parameter or a NEW symbol. Tells whether an entry may be kept.
fn check_defs(defs: &[Fact], scope: &Scope, unit: &Unit) -> Result<bool> {
    let mut is_kept = false;
    for def in defs {
        let def = match def {
            Fact::Expression(def) => def,
            Fact::Module { name, .. } if is_module_found(name, unit) => {
                is_kept = true;
                continue;
            }
            // `generateUseOrHide` reports a module its symbol table doesn't hold, which no
            // recording shows.
            Fact::Module { .. } => {
                return Err(FrontError::NotYet(
                    "a module named in a DEF clause that SANY may not find".to_owned(),
                ));
            }
        };
        // SANY's parser rejects an entry in parentheses, which the front end doesn't word.
        if def
            .location
            .range
            .as_ref()
            .is_some_and(|range| range.start != def.location.position())
        {
            return Err(FrontError::NotYet(
                "a DEF clause entry in parentheses".to_owned(),
            ));
        }
        let name = match &def.kind {
            ExpressionKind::Identifier { name, .. } => name,
            // An operator symbol a module defines, such as Naturals' +, is kept; SANY's report of
            // any other is not followed.
            ExpressionKind::OperatorReference { operator, .. } => {
                let kind = find_current(scope, operator, unit, def.location.range.as_ref())
                    .map(|local| local.binding().kind);
                if kind != Some(SymbolKind::Definition) {
                    return Err(FrontError::NotYet(format!(
                        "a DEF clause entry {operator} that names no operator a module defines"
                    )));
                }
                is_kept = true;
                continue;
            }
            _ => {
                return Err(FrontError::NotYet(
                    "a DEF clause entry that is neither a name nor an operator symbol".to_owned(),
                ));
            }
        };
        // SANY takes the name of a DEFINE step (`selectorToNode`), and a selection that names a
        // definition; the front end follows no other.
        if name.starts_with('<') || name.contains('!') {
            let local = find_current(scope, name, unit, def.location.range.as_ref());
            let is_defined = local.is_some_and(|local| {
                local.is_definition_step
                    || (!name.starts_with('<') && local.kind == SymbolKind::Definition)
            });
            if !is_defined {
                return Err(FrontError::NotYet(format!(
                    "a DEF clause entry {name} that is no DEFINE step and selects no definition"
                )));
            }
            is_kept = true;
            continue;
        }
        let kind = find_current(scope, name, unit, def.location.range.as_ref())
            .map(|local| local.binding().kind);
        if matches!(
            kind,
            Some(SymbolKind::Definition | SymbolKind::Instance | SymbolKind::Theorem)
        ) {
            is_kept = true;
            continue;
        }
        let is_unknown = kind.is_none() && !unit.facts.borrow().contains(name);
        let is_rejected = matches!(
            kind,
            Some(
                SymbolKind::Builtin
                    | SymbolKind::Constant
                    | SymbolKind::Variable
                    | SymbolKind::Parameter
                    | SymbolKind::New(_)
            )
        );
        let (true, Some(range)) = (is_unknown || is_rejected, &def.location.range) else {
            return Err(FrontError::NotYet(format!(
                "a DEF clause entry {name} SANY may reject"
            )));
        };
        if is_unknown {
            unit.error(format_range(range), format!("Unknown operator: `{name}'."));
        }
        unit.error(
            format_range(range),
            "DEF clause entry should describe a defined operator.".to_owned(),
        );
    }
    Ok(is_kept)
}

/// SANY rejects a USE or HIDE that keeps no fact and no DEF entry.
fn check_use_or_hide(use_or_hide: &UseOrHide, scope: &Scope, unit: &Unit) -> Result<()> {
    check_facts(&use_or_hide.facts, scope, unit)?;
    if check_defs(&use_or_hide.defs, scope, unit)? || !use_or_hide.facts.is_empty() {
        return Ok(());
    }
    let Some(range) = &use_or_hide.location.range else {
        return Err(FrontError::NotYet(
            "an empty USE or HIDE without a place".to_owned(),
        ));
    };
    unit.error(
        format_range(range),
        "Empty USE or HIDE statement.".to_owned(),
    );
    Ok(())
}

fn resolve_new_symbol(symbol: &NewSymbol, scope: &Scope, unit: &Unit) -> Result<Scope> {
    if let Some(set) = &symbol.set {
        resolve_expression(set, scope, unit)?;
    }
    Ok(bind_name(
        scope,
        &symbol.name,
        Binding {
            kind: SymbolKind::New(symbol.level),
            arity: symbol.arity,
            params: None,
            range: symbol.name_range.clone(),
        },
        unit,
    ))
}

/// The NEW symbols of an ASSUME stay in scope for its conclusion and the proof that follows. SANY
/// forbids a label in the scope of a NEW in a nested ASSUME.
fn resolve_assume_prove(
    assume_prove: &AssumeProve,
    scope: &Scope,
    unit: &Unit,
    is_nested: bool,
) -> Result<Scope> {
    let mut current_scope = scope.clone();
    let mut current_unit = unit.clone();
    for assumption in &assume_prove.assumptions {
        match assumption {
            Assumed::NewSymbol(symbol) => {
                current_scope = resolve_new_symbol(symbol, &current_scope, &current_unit)?;
                if is_nested {
                    current_unit = Unit {
                        is_label_forbidden: true,
                        ..current_unit
                    };
                }
            }
            Assumed::AssumeProve(inner) => {
                resolve_assume_prove(inner, &current_scope, &current_unit, true)?;
            }
            Assumed::Label {
                name,
                body,
                location,
                ..
            } => {
                if !is_label_reported(location.range.as_ref(), &current_unit) {
                    resolve_assume_prove(
                        body,
                        &current_scope,
                        &get_label_unit(&current_unit),
                        true,
                    )?;
                    check_label(
                        name,
                        &[],
                        &[],
                        location.range.as_ref(),
                        &current_scope,
                        &current_unit,
                    );
                }
            }
            Assumed::Expression(expression) => {
                resolve_expression(expression, &current_scope, &current_unit)?;
            }
        }
    }
    resolve_expression(&assume_prove.conclusion, &current_scope, &current_unit)?;
    Ok(current_scope)
}

fn resolve_statement(statement: &Statement, scope: &Scope, unit: &Unit) -> Result<Scope> {
    match statement {
        Statement::AssumeProve(assume_prove) => {
            resolve_assume_prove(assume_prove, scope, unit, false)
        }
        Statement::Expression(expression) => {
            resolve_expression(expression, scope, unit)?;
            Ok(scope.clone())
        }
    }
}

/// SANY resolves the expressions of a proof, while its facts and DEF clauses may also name
/// theorems, assumptions, and modules.
fn resolve_proof(proof: Option<&Proof>, scope: &Scope, outer: &Unit) -> Result<()> {
    let unit = if outer.has_label_scope {
        Unit {
            has_label_scope: false,
            ..outer.clone()
        }
    } else {
        outer.clone()
    };
    match proof.map(|proof| &proof.kind) {
        // `generateLeafProof` rejects a BY that keeps no fact and no DEF entry.
        Some(ProofKind::By { facts, defs, .. }) => {
            check_facts(facts, scope, &unit)?;
            if check_defs(defs, scope, &unit)? || !facts.is_empty() {
                return Ok(());
            }
            let Some(range) = proof.and_then(|proof| proof.location.range.as_ref()) else {
                return Err(FrontError::NotYet("an empty BY without a place".to_owned()));
            };
            unit.error(format_range(range), "Empty BY".to_owned());
            Ok(())
        }
        Some(ProofKind::Steps { steps, .. }) => {
            let mut current = scope.clone();
            // Whether the assertion step before is infix, which an @ step continues.
            let mut is_previous_infix = false;
            for step in steps {
                let asserted = match &step.body {
                    StepBody::Assert {
                        is_suffices,
                        statement: Statement::Expression(expression),
                    } => Some((*is_suffices, expression)),
                    _ => None,
                };
                let step_at = match asserted {
                    Some((false, expression)) if is_previous_infix => get_step_at(expression),
                    _ => None,
                };
                let step_unit = Unit {
                    step_at,
                    ..unit.clone()
                };
                current = resolve_step(step, &current, &step_unit)?;
                is_previous_infix = match asserted {
                    Some((true, _)) => is_previous_infix,
                    Some((false, expression)) => is_infix_expression(expression),
                    None => false,
                };
            }
            Ok(())
        }
        _ => Ok(()),
    }
}

// `isInfixExpression`, as the expression's form gives it: an unbulleted junction, or an infix
// operator applied to two arguments.
fn is_infix_expression(expression: &Expression) -> bool {
    match &expression.kind {
        ExpressionKind::Junction { is_bulleted, .. } => !is_bulleted,
        ExpressionKind::Apply { operator, args, .. } => {
            args.len() == 2 && crate::parser::is_infix(operator)
        }
        _ => false,
    }
}

// The @ an assertion step `@ op e` takes for the right side of the infix step before it.
fn get_step_at(expression: &Expression) -> Option<usize> {
    if !is_infix_expression(expression) {
        return None;
    }
    let ExpressionKind::Apply { args, .. } = &expression.kind else {
        return None;
    };
    matches!(args[0].kind, ExpressionKind::ExceptAt).then(|| Rc::as_ptr(&args[0]) as usize)
}

/// A LET or a step binds the name of the INSTANCE after the names it adds.
fn resolve_local_instance(instance: &Rc<Instance>, scope: &Scope, unit: &Unit) -> Result<Scope> {
    let instanced = resolve_instance(instance, scope, unit)?;
    Ok(match &instance.name {
        None => instanced,
        Some(name) => bind_name(
            &instanced,
            name,
            Binding {
                kind: SymbolKind::Instance,
                arity: instance.params.len(),
                params: None,
                range: instance.location.range.clone(),
            },
            unit,
        ),
    })
}

fn theorem_local(
    name: &Name,
    parent: Scope,
    goal: Option<Rc<Goal>>,
    is_non_fact: bool,
    unselectable: Option<&'static str>,
) -> Scope {
    Some(Rc::new(Local {
        goal,
        is_non_fact,
        unselectable,
        ..Local::new(
            name.clone(),
            Binding {
                kind: SymbolKind::Theorem,
                arity: 0,
                params: None,
                range: None,
            },
            parent,
        )
    }))
}

/// `Generator.generateProof` binds the name of a step after its statement and before its proof, or
/// after the step where it takes no proof.
fn resolve_step(step: &ProofStep, scope: &Scope, unit: &Unit) -> Result<Scope> {
    let step_unit = if step.name.is_none() {
        unit.clone()
    } else {
        Unit {
            has_label_scope: true,
            label_params: Rc::default(),
            labels: Rc::default(),
            ..unit.clone()
        }
    };
    // What SANY says of the step's name used as an expression, where the step asserts none
    // (`Generator.selectorToNode`).
    let unselectable = match &step.body {
        StepBody::Assert {
            statement: Statement::AssumeProve(_),
            ..
        } => Some("ASSUME/PROVE used where an expression is required."),
        StepBody::Assert {
            is_suffices: true, ..
        } => Some("SUFFICES proof step selected instead of expression."),
        StepBody::Have(_) => Some("HAVE proof step selected instead of expression."),
        StepBody::Case(_) => Some("CASE proof step selected instead of expression."),
        StepBody::Take { .. } => Some("TAKE proof step selected instead of expression."),
        StepBody::Pick { .. } => Some("PICK proof step selected instead of expression."),
        StepBody::Witness(_) => Some("WITNESS proof step selected instead of expression."),
        StepBody::Qed => Some("QED step proof step selected instead of expression."),
        _ => None,
    };
    let bind_step = |parent: &Scope| match &step.name {
        None => parent.clone(),
        Some(name) => theorem_local(name, parent.clone(), None, false, unselectable),
    };
    let bind_non_fact_step = |parent: &Scope| match &step.name {
        None => parent.clone(),
        Some(name) => theorem_local(name, parent.clone(), None, true, None),
    };
    let proof = step.proof.as_deref();
    match &step.body {
        // The NEW symbols of a SUFFICES ASSUME are in scope after its proof, and those of any
        // other ASSUME in its proof.
        StepBody::Assert {
            is_suffices,
            statement,
        } => {
            let assumed = resolve_statement(statement, scope, &step_unit)?;
            let proof_scope = if *is_suffices { scope } else { &assumed };
            let Some(name) = &step.name else {
                resolve_proof(proof, proof_scope, unit)?;
                return Ok(if *is_suffices { assumed } else { scope.clone() });
            };
            let goal = Rc::new(Goal {
                statement: statement.clone(),
                is_suffices: *is_suffices,
                is_in_proof: Cell::new(true),
            });
            resolve_proof(
                proof,
                &theorem_local(
                    name,
                    proof_scope.clone(),
                    Some(goal.clone()),
                    false,
                    unselectable,
                ),
                unit,
            )?;
            goal.is_in_proof.set(false);
            Ok(theorem_local(
                name,
                if *is_suffices { assumed } else { scope.clone() },
                Some(goal),
                false,
                unselectable,
            ))
        }
        StepBody::UseOrHide(use_or_hide) => {
            check_use_or_hide(use_or_hide, scope, unit)?;
            Ok(bind_non_fact_step(scope))
        }
        StepBody::Instance(instance) => Ok(bind_non_fact_step(&resolve_local_instance(
            instance, scope, &step_unit,
        )?)),
        StepBody::Define { definitions, .. } => {
            let mut current = scope.clone();
            for definition in definitions {
                current = match definition {
                    DefinitionUnit::Instance(instance) => {
                        resolve_local_instance(instance, &current, &step_unit)?
                    }
                    DefinitionUnit::Definition(definition) => resolve_definitions(
                        std::slice::from_ref(definition),
                        &current,
                        unit,
                        &[],
                        &[],
                    )?,
                };
            }
            Ok(match &step.name {
                None => current,
                Some(name) => Some(Rc::new(Local {
                    is_non_fact: true,
                    is_definition_step: true,
                    ..Local::new(
                        name.clone(),
                        Binding {
                            kind: SymbolKind::Theorem,
                            arity: 0,
                            params: None,
                            range: None,
                        },
                        current,
                    )
                })),
            })
        }
        StepBody::Have(expression) | StepBody::Case(expression) => {
            resolve_expression(expression, scope, &step_unit)?;
            resolve_proof(proof, &bind_step(scope), unit)?;
            Ok(bind_step(scope))
        }
        StepBody::Witness(expressions) => {
            resolve_all(expressions, scope, &step_unit)?;
            Ok(bind_step(scope))
        }
        StepBody::Take {
            names,
            name_ranges,
            bounds,
        } => Ok(bind_step(&bind_names(
            &resolve_bounds(bounds, scope, &step_unit)?,
            names,
            name_ranges,
            &step_unit,
        ))),
        StepBody::Pick {
            names,
            name_ranges,
            bounds,
            body,
        } => {
            let picked = bind_names(
                &resolve_bounds(bounds, scope, &step_unit)?,
                names,
                name_ranges,
                &step_unit,
            );
            let mut params = (*step_unit.label_params).clone();
            params.extend(get_bound_names(bounds));
            params.extend(names.iter().cloned());
            resolve_expression(
                body,
                &picked,
                &Unit {
                    label_params: Rc::new(params),
                    ..step_unit.clone()
                },
            )?;
            resolve_proof(proof, &bind_step(scope), unit)?;
            Ok(bind_step(&picked))
        }
        StepBody::Qed => {
            resolve_proof(proof, &bind_step(scope), unit)?;
            Ok(bind_step(scope))
        }
    }
}

/// SANY binds the name of a theorem after its statement and before its proof.
fn resolve_theorem(theorem: &Theorem, unit: &Unit) -> Result<()> {
    let is_definition =
        theorem.name.is_some() && !matches!(theorem.statement, Statement::AssumeProve(_));
    let scope = if is_definition {
        None
    } else {
        resolve_statement(&theorem.statement, &None, unit)?
    };
    if let Some(name) = &theorem.name {
        bind_module_name(
            name,
            Binding {
                kind: SymbolKind::Theorem,
                arity: 0,
                params: None,
                range: theorem.location.range.clone(),
            },
            unit,
        );
    }
    let goal = unit
        .goals
        .get(theorem.name.as_deref().unwrap_or(""))
        .cloned();
    if let Some(goal) = &goal {
        goal.is_in_proof.set(true);
    }
    // `processTheorem` adds a theorem whose statement is an expression to the symbol table before
    // its proof, which may name it as one, so its proof is read after its definition.
    let proof_unit = match (&theorem.proof, is_definition) {
        (Some(proof), true) => Unit {
            location: proof.location.position(),
            ..unit.clone()
        },
        _ => unit.clone(),
    };
    resolve_proof(theorem.proof.as_ref(), &scope, &proof_unit)?;
    if let Some(goal) = &goal {
        goal.is_in_proof.set(false);
    }
    Ok(())
}

/// What SANY reports at a location as it links a module, such as a conflict between the modules it
/// extends.
#[derive(Clone)]
pub struct ModuleReport {
    pub location: Position,
    pub errors: ErrorList,
    pub warnings: ErrorList,
}

/// What resolution reads of the modules a module links to (`ModuleUnit` in `resolve.ts`).
#[derive(Clone)]
pub struct ModuleContext<'a> {
    pub imported: Rc<Symbols>,
    pub get_instance: GetInstance<'a>,
    /// The built-in operators and the names of the enclosing and extended modules.
    pub bound: Rc<Symbols>,
    pub definitions: Rc<OrderedMap<Name, Rc<Definition>>>,
    pub get_key: GetKey,
    /// The names each INSTANCE adds, by the INSTANCE's address.
    pub instanced: Rc<RefCell<FastMap<usize, Symbols>>>,
    /// The theorems and assumptions the extended and instantiated modules export.
    pub facts: Rc<RefCell<FastSet<Name>>>,
    pub reports: Rc<RefCell<Vec<ModuleReport>>>,
    pub warnings: ErrorList,
    pub tables: Rc<Tables>,
}

/// A named theorem or assumption is linked as a definition too.
pub fn is_theorem_definition(module: &Module, definition: &Definition) -> bool {
    module
        .theorems
        .iter()
        .map(|theorem| (&theorem.name, &theorem.location))
        .chain(
            module
                .assumptions
                .iter()
                .map(|assumption| (&assumption.name, &assumption.location)),
        )
        .any(|(name, location)| {
            name.as_ref() == Some(&definition.name)
                && location.line == definition.location.line
                && location.column == definition.location.column
        })
}

fn get_declared(module: &Module) -> Rc<FastMap<Name, Position>> {
    Rc::new(
        module
            .constants
            .iter()
            .chain(&module.variables)
            .map(|declaration| (declaration.name.clone(), declaration.location.position()))
            .collect(),
    )
}

fn create_symbols(module: &Module, imported: &Symbols) -> Symbols {
    let mut symbols: Symbols = core_symbols().into_iter().collect();
    for (name, symbol) in imported.iter() {
        symbols.insert(name.clone(), symbol.clone());
    }
    for constant in &module.constants {
        symbols.insert(
            constant.name.clone(),
            ModuleSymbol {
                key: constant.name.clone(),
                kind: SymbolKind::Constant,
                arity: constant.arity,
                params: None,
                range: None,
            },
        );
    }
    for variable in &module.variables {
        symbols.insert(
            variable.name.clone(),
            ModuleSymbol {
                key: variable.name.clone(),
                kind: SymbolKind::Variable,
                arity: 0,
                params: None,
                range: None,
            },
        );
    }
    symbols
}

/// `Generator.processSubst` analyzes the explicit substitutions in the order they appear, then the
/// implicit ones, and then reports each declaration left without one. The parameters of the
/// INSTANCE are in scope.
fn check_substitutions(
    instance: &Instance,
    declarations: &[Declaration],
    instancer: &str,
    outer: &Scope,
    unit: &Unit,
) -> Result<OrderedMap<Name, Expr>> {
    let scope = instance.params.iter().fold(outer.clone(), |parent, param| {
        Some(Rc::new(Local::new(
            param.name.clone(),
            parameter(param.arity, None),
            parent,
        )))
    });
    let resolve_substitute = |declaration: &Declaration,
                              expression: &Expr,
                              is_explicit: bool|
     -> Result<()> {
        if declaration.arity == 0 || !matches!(expression.kind, ExpressionKind::Identifier { .. }) {
            return resolve_expression(expression, &scope, unit);
        }
        let name = expression.reference().unwrap_or_default();
        let arity = get_symbol_arity(expression, &name, &scope, unit)?;
        if let Some(arity) = arity
            && arity != declaration.arity
        {
            let mut error = SyntaxError::new(format!(
                "An operator must be substituted for symbol '{}', and it must have arity {} in the instance of {} at line {}, column {}",
                declaration.name,
                declaration.arity,
                instance.module,
                instance.location.line,
                instance.location.column
            ));
            // Generator.checkSubstitutionForCorrectArity reports it at the substitute, which an
            // implicit substitution places at the INSTANCE. An explicit one SANY's selector
            // rejects first, at the substitute, so it reports the substitution in the builtins'
            // module.
            if let Some(range) = &expression.location.range
                && unit.tables.is_collecting.get()
                && !is_explicit
            {
                error.sany = SyntaxError::sany(vec![SanyError {
                    location: format_range(range),
                    message: format!(
                        "An operator must be substituted for symbol '{}', and it must have arity {}.",
                        declaration.name, declaration.arity
                    ),
                }])
                .sany;
            } else if let Some(range) = &expression.location.range
                && unit.tables.is_collecting.get()
            {
                error.sany = SyntaxError::sany(vec![
                    SanyError {
                        location: format_range(range),
                        message: format!(
                            "Expected arity {} but found operator of arity {arity}.",
                            declaration.arity
                        ),
                    },
                    SanyError {
                        location: "In module --TLA+ BUILTINS--".to_owned(),
                        message: format!(
                            "An operator must be substituted for symbol '{}', and it must have arity {}.",
                            declaration.name, declaration.arity
                        ),
                    },
                ])
                .sany;
            }
            return Err(error.into());
        }
        Ok(())
    };
    let mut substitutions: OrderedMap<Name, Expr> = OrderedMap::new();
    for substitution in &instance.substitutions {
        let name = &substitution.name;
        let Some(declaration) = declarations.iter().find(|item| &item.name == name) else {
            unit.error(
                format_range(&substitution.name_range),
                format!(
                    "Identifier '{name}' is not a legal target of a substitution. \nA legal target must be a declared CONSTANT or VARIABLE in the module being instantiated. \n(Also, check for warnings about multiple declarations of this same identifier.)"
                ),
            );
            continue;
        };
        let expression = &substitution.expression;
        resolve_substitute(declaration, expression, true)?;
        if !substitutions.contains_key(name) {
            substitutions.insert(name.clone(), expression.clone());
        } else if let Some(range) = &expression.location.range {
            unit.error(
                format_range(range),
                format!("Multiple substitutions for symbol '{name}' in substitution."),
            );
        }
    }
    let implicit: Vec<&Declaration> = declarations
        .iter()
        .filter(|declaration| !substitutions.contains_key(&declaration.name))
        .collect();
    let is_missing = |declaration: &Declaration| {
        lookup_local(&scope, &declaration.name).is_none()
            && find_symbol(&declaration.name, unit).is_none()
    };
    for declaration in implicit
        .iter()
        .filter(|declaration| !is_missing(declaration))
    {
        let expression = Rc::new(Expression::new(
            ExpressionKind::Identifier {
                name: declaration.name.clone(),
                spelling: None,
                selector_ranges: None,
            },
            instance.location.clone(),
        ));
        resolve_substitute(declaration, &expression, false)?;
        substitutions.insert(declaration.name.clone(), expression);
    }
    for declaration in implicit
        .iter()
        .filter(|declaration| is_missing(declaration))
    {
        if let (Some(range), Some(declared)) =
            (&instance.location.range, &declaration.location.range)
        {
            unit.error(
                format_range(range),
                format!(
                    "Substitution missing for symbol {} declared at {} \nand instantiated in module {instancer}.",
                    declaration.name,
                    format_range(declared)
                ),
            );
        }
    }
    Ok(substitutions)
}

/// `Generator.processSubst` analyzes an INSTANCE in a LET or a proof, which then binds the names
/// the INSTANCE adds.
fn resolve_instance(instance: &Rc<Instance>, scope: &Scope, unit: &Unit) -> Result<Scope> {
    let instanced = (unit.get_instance)(instance)?;
    check_substitutions(
        instance,
        &instanced.declarations,
        &instanced.instancer,
        scope,
        unit,
    )?;
    Ok(instanced
        .symbols
        .iter()
        .fold(scope.clone(), |parent, (name, symbol)| {
            bind_name(&parent, name, Binding::from(symbol), unit)
        }))
}

/// tla-ts reports what SANY goes on after with an INSTANCE of the module.
pub fn resolve_substitutions(
    instance: &Instance,
    declarations: &[Declaration],
    module: &Module,
    unit: &ModuleContext,
) -> Result<OrderedMap<Name, Expr>> {
    let imported = create_symbols(module, &unit.imported);
    let report = ModuleReport {
        location: instance.location.position(),
        errors: Rc::default(),
        warnings: Rc::default(),
    };
    unit.reports.borrow_mut().push(report.clone());
    let bindings: OrderedMap<Name, Rc<Local>> = imported
        .iter()
        .map(|(name, symbol)| {
            (
                name.clone(),
                Rc::new(Local::new(name.clone(), Binding::from(symbol), None)),
            )
        })
        .collect();
    check_substitutions(
        instance,
        declarations,
        &module.name,
        &None,
        &Unit {
            imported: Rc::new(imported),
            declared: get_declared(module),
            modules: Rc::default(),
            get_instance: unit.get_instance.clone(),
            definitions: unit.definitions.clone(),
            get_key: unit.get_key.clone(),
            location: instance.location.position(),
            self_definition: None,
            facts: Rc::default(),
            goals: Rc::default(),
            bindings: Rc::new(RefCell::new(bindings)),
            errors: report.errors,
            warnings: report.warnings,
            has_label_scope: false,
            is_label_forbidden: false,
            is_in_except: false,
            step_at: None,
            is_fact: false,
            label_params: Rc::default(),
            labels: Rc::default(),
            is_generated: false,
            tables: unit.tables.clone(),
            let_level: 0,
            let_recursive: Rc::default(),
        },
    )
}

pub type Check<'a> = Box<dyn FnOnce(&ErrorList, &ErrorList) -> Result<()> + 'a>;

/// A unit of a module SANY checks, at its location: it reports to its lists what SANY goes on
/// after, and fails with the error that stops it.
pub struct SemanticUnit<'a> {
    pub location: Position,
    pub check: Check<'a>,
}

/// SANY reports the errors of every unit it checks, in the order of the units in the module, after
/// the warnings it reports for the spec. An error tla-ts cannot word as SANY does yields to the
/// errors the unit reported before it. Returns the errors.
pub fn collect_semantic_errors(
    mut units: Vec<SemanticUnit<'_>>,
    warnings: &ErrorList,
) -> Result<Vec<SanyError>> {
    let mut errors: Vec<SanyError> = Vec::new();
    let add_unique = |list: &mut Vec<SanyError>, item: SanyError| {
        if list
            .iter()
            .all(|existing| existing.location != item.location || existing.message != item.message)
        {
            list.push(item);
        }
    };
    units.sort_by(|left, right| {
        if is_before(left.location, right.location) {
            std::cmp::Ordering::Less
        } else if is_before(right.location, left.location) {
            std::cmp::Ordering::Greater
        } else {
            std::cmp::Ordering::Equal
        }
    });
    for unit in units {
        let reported: ErrorList = Rc::default();
        let warned: ErrorList = Rc::default();
        if let Err(error) = (unit.check)(&reported, &warned) {
            let FrontError::Syntax(syntax) = &error else {
                return Err(error);
            };
            if syntax.sany.is_none() && reported.borrow().is_empty() {
                return Err(error);
            }
            if let Some(sany) = &syntax.sany {
                reported.borrow_mut().extend(sany.errors.iter().cloned());
            }
        }
        for item in reported.take() {
            add_unique(&mut errors, item);
        }
        for item in warned.take() {
            add_unique(&mut warnings.borrow_mut(), item);
        }
    }
    Ok(errors)
}

/// A RECURSIVE declaration, and what it binds.
type RecursiveDeclaration = (Rc<Declaration>, Rc<Local>);

/// SANY binds the names of a module in the order of its units, and reports a RECURSIVE declaration
/// that no definition follows at the end. Returns the errors.
pub fn resolve_module(module: &Module, unit: &ModuleContext) -> Result<Vec<SanyError>> {
    check_recursive(module)?;
    let symbols = Rc::new(create_symbols(module, &unit.imported));
    let facts: Rc<RefCell<FastSet<Name>>> = Rc::new(RefCell::new(
        unit.facts
            .borrow()
            .iter()
            .cloned()
            .chain(
                module
                    .theorems
                    .iter()
                    .filter_map(|theorem| theorem.name.clone()),
            )
            .chain(
                module
                    .assumptions
                    .iter()
                    .filter_map(|assumption| assumption.name.clone()),
            )
            .collect(),
    ));
    let goals: Rc<FastMap<Name, Rc<Goal>>> = Rc::new(
        module
            .theorems
            .iter()
            .filter_map(|theorem| match (&theorem.name, &theorem.statement) {
                (Some(name), Statement::AssumeProve(_)) => Some((
                    name.clone(),
                    Rc::new(Goal {
                        statement: theorem.statement.clone(),
                        is_suffices: false,
                        is_in_proof: Cell::new(false),
                    }),
                )),
                _ => None,
            })
            .collect(),
    );
    let bindings: Rc<RefCell<OrderedMap<Name, Rc<Local>>>> = Rc::new(RefCell::new(
        core_symbols()
            .into_iter()
            .chain(
                unit.bound
                    .iter()
                    .map(|(name, symbol)| (name.clone(), symbol.clone())),
            )
            .map(|(name, symbol)| {
                let local = Rc::new(Local::new(name.clone(), Binding::from(&symbol), None));
                (name, local)
            })
            .collect(),
    ));
    let recursive: Rc<RefCell<Vec<Rc<Local>>>> = Rc::default();
    let declarations: Rc<RefCell<Vec<RecursiveDeclaration>>> = Rc::default();
    let let_recursive: LetRecursive = Rc::default();
    let declared = get_declared(module);
    let modules: Rc<FastMap<Name, Position>> = Rc::new(
        module
            .modules
            .iter()
            .map(|inner| (inner.name.clone(), inner.location.position()))
            .chain(
                [&module.name]
                    .into_iter()
                    .chain(&module.extends)
                    .map(|name| (name.clone(), MODULE_START)),
            )
            .collect(),
    );
    let create_unit = |location: Position,
                       self_definition: Option<Rc<Definition>>,
                       errors: &ErrorList,
                       warnings: &ErrorList,
                       has_label_scope: bool| Unit {
        imported: symbols.clone(),
        declared: declared.clone(),
        modules: modules.clone(),
        get_instance: unit.get_instance.clone(),
        definitions: unit.definitions.clone(),
        get_key: unit.get_key.clone(),
        location,
        self_definition,
        facts: facts.clone(),
        goals: goals.clone(),
        bindings: bindings.clone(),
        errors: errors.clone(),
        warnings: warnings.clone(),
        has_label_scope,
        is_label_forbidden: false,
        is_in_except: false,
        step_at: None,
        is_fact: false,
        label_params: Rc::default(),
        labels: Rc::default(),
        is_generated: false,
        tables: unit.tables.clone(),
        let_level: 0,
        let_recursive: let_recursive.clone(),
    };
    let create_unit = &create_unit;
    let mut units: Vec<SemanticUnit<'_>> = Vec::new();
    for report in unit.reports.borrow().iter() {
        let report = report.clone();
        units.push(SemanticUnit {
            location: report.location,
            check: Box::new(move |errors, warnings| {
                errors
                    .borrow_mut()
                    .extend(report.errors.borrow().iter().cloned());
                warnings
                    .borrow_mut()
                    .extend(report.warnings.borrow().iter().cloned());
                Ok(())
            }),
        });
    }
    // Generator.checkIfInRecursiveSection: only definitions and instances may come between a
    // RECURSIVE declaration and the definition of what it declares. SANY reports it before the
    // unit's own errors.
    let mut pending: Vec<Name> = Vec::new();
    for item in &module.units {
        let (location, kind) = match item {
            ModuleUnit::Recursive(declared) => {
                pending.extend(declared.iter().map(|declaration| declaration.name.clone()));
                continue;
            }
            ModuleUnit::Definition(definition) => {
                if let Some(index) = pending.iter().position(|name| *name == definition.name) {
                    pending.remove(index);
                }
                continue;
            }
            ModuleUnit::Instance(_) => continue,
            ModuleUnit::Constants { location, .. } => (location, "A declaration"),
            ModuleUnit::Variables { location, .. } => (location, "A VARIABLE declaration"),
            ModuleUnit::Assumption(assumption) => (&assumption.location, "An ASSUME"),
            ModuleUnit::Theorem(theorem) => (&theorem.location, "A THEOREM"),
            ModuleUnit::Use(use_or_hide) => (&use_or_hide.location, "A USE or HIDE"),
            ModuleUnit::Module(inner) => (&inner.location, "A MODULE "),
        };
        if pending.is_empty() {
            continue;
        }
        // The nested module's end clears the section's count (`checkForUndefinedRecursiveOps`),
        // so the operator's definition after it drives the count below zero, and `endOpDefNode`
        // throws a WrongInvocationException, which TLC reports as a failed parse.
        if matches!(item, ModuleUnit::Module(_)) {
            return Err(FrontError::NotYet(
                "a module in a recursive section, where SANY's generator throws".to_owned(),
            ));
        }
        let Some(range) = location.range.clone() else {
            return Err(FrontError::NotYet(
                "a unit in a recursive section without a range".to_owned(),
            ));
        };
        units.push(SemanticUnit {
            location: location.position(),
            check: Box::new(move |errors, _| {
                errors.borrow_mut().push(SanyError {
                    location: format_range(&range),
                    message: format!(
                        "{kind} may not appear within a recursive definition section."
                    ),
                });
                Ok(())
            }),
        });
    }
    for (declared, kind) in [
        (&module.constants, SymbolKind::Constant),
        (&module.variables, SymbolKind::Variable),
    ] {
        for declaration in declared {
            units.push(SemanticUnit {
                location: declaration.location.position(),
                check: Box::new(move |errors, warnings| {
                    bind_module_name(
                        &declaration.name,
                        Binding {
                            kind,
                            arity: declaration.arity,
                            params: None,
                            range: declaration.location.range.clone(),
                        },
                        &create_unit(
                            declaration.location.position(),
                            None,
                            errors,
                            warnings,
                            false,
                        ),
                    );
                    Ok(())
                }),
            });
        }
    }
    for item in &module.units {
        let ModuleUnit::Recursive(recursive_declarations) = item else {
            continue;
        };
        for declaration in recursive_declarations {
            let recursive = recursive.clone();
            let declarations = declarations.clone();
            let bindings = bindings.clone();
            units.push(SemanticUnit {
                location: declaration.location.position(),
                check: Box::new(move |_, _| {
                    let binding = Rc::new(Local {
                        is_pending: Cell::new(true),
                        position: declaration.location.position(),
                        ..Local::new(
                            declaration.name.clone(),
                            Binding {
                                kind: SymbolKind::Definition,
                                arity: declaration.arity,
                                params: None,
                                range: declaration.location.range.clone(),
                            },
                            None,
                        )
                    });
                    // `check_recursive` leaves no other binding of the name after the declaration.
                    if bindings.borrow().contains_key(&declaration.name) {
                        return Err(FrontError::NotYet(format!(
                            "a module-level RECURSIVE declaration of {}, a name already bound",
                            declaration.name
                        )));
                    }
                    bindings
                        .borrow_mut()
                        .insert(declaration.name.clone(), binding.clone());
                    recursive.borrow_mut().push(binding.clone());
                    declarations
                        .borrow_mut()
                        .push((declaration.clone(), binding));
                    Ok(())
                }),
            });
        }
    }
    for definition in &module.definitions {
        let recursive = recursive.clone();
        let bindings = bindings.clone();
        units.push(SemanticUnit {
            location: definition.location.position(),
            check: Box::new(move |errors, warnings| {
                let inner = create_unit(
                    definition.location.position(),
                    Some(definition.clone()),
                    errors,
                    warnings,
                    true,
                );
                if is_theorem_definition(module, definition) {
                    resolve_expression(&definition.body, &None, &inner)?;
                } else if resolve_definition(definition, &None, &inner, &recursive.borrow())? {
                    let mut local = Local::new(
                        definition.name.clone(),
                        Binding {
                            kind: SymbolKind::Definition,
                            arity: get_arity(definition),
                            params: None,
                            range: definition.location.range.clone(),
                        },
                        None,
                    );
                    local.position = definition.location.position();
                    bindings
                        .borrow_mut()
                        .insert(definition.name.clone(), Rc::new(local));
                }
                Ok(())
            }),
        });
    }
    for instance in &module.instances {
        let instanced = unit.instanced.clone();
        units.push(SemanticUnit {
            location: instance.location.position(),
            check: Box::new(move |errors, warnings| {
                let inner =
                    create_unit(instance.location.position(), None, errors, warnings, false);
                bind_params(&None, &instance.params, &inner);
                if let Some(symbols) = instanced.borrow().get(&(Rc::as_ptr(instance) as usize)) {
                    for (name, symbol) in symbols.iter() {
                        bind_module_name(name, Binding::from(symbol), &inner);
                    }
                }
                if let Some(name) = &instance.name {
                    bind_module_name(
                        name,
                        Binding {
                            kind: SymbolKind::Instance,
                            arity: instance.params.len(),
                            params: None,
                            range: instance.location.range.clone(),
                        },
                        &inner,
                    );
                }
                Ok(())
            }),
        });
    }
    for assumption in &module.assumptions {
        units.push(SemanticUnit {
            location: assumption.location.position(),
            check: Box::new(move |errors, warnings| {
                let inner = create_unit(
                    assumption.location.position(),
                    None,
                    errors,
                    warnings,
                    assumption.name.is_some(),
                );
                resolve_expression(&assumption.expression, &None, &inner)?;
                if let Some(name) = &assumption.name {
                    bind_module_name(
                        name,
                        Binding {
                            kind: SymbolKind::Theorem,
                            arity: 0,
                            params: None,
                            range: assumption.location.range.clone(),
                        },
                        &inner,
                    );
                }
                Ok(())
            }),
        });
    }
    for theorem in &module.theorems {
        units.push(SemanticUnit {
            location: theorem.location.position(),
            check: Box::new(move |errors, warnings| {
                resolve_theorem(
                    theorem,
                    &create_unit(
                        theorem.location.position(),
                        None,
                        errors,
                        warnings,
                        theorem.name.is_some(),
                    ),
                )
            }),
        });
    }
    for use_or_hide in &module.uses {
        units.push(SemanticUnit {
            location: use_or_hide.location.position(),
            check: Box::new(move |errors, warnings| {
                let unit = create_unit(
                    use_or_hide.location.position(),
                    None,
                    errors,
                    warnings,
                    false,
                );
                check_use_or_hide(use_or_hide, &None, &unit)
            }),
        });
    }
    let end = module
        .location
        .range
        .as_ref()
        .map_or_else(|| module.location.position(), |range| range.end);
    let pending = declarations.clone();
    units.push(SemanticUnit {
        location: end,
        check: Box::new(move |errors, _| {
            for (declaration, binding) in pending.borrow().iter() {
                if let Some(range) = &declaration.location.range
                    && binding.is_pending.get()
                {
                    errors.borrow_mut().push(SanyError {
                        location: format_range(range),
                        message: format!(
                            "Symbol {} declared in RECURSIVE statement but not defined.",
                            declaration.name
                        ),
                    });
                }
            }
            Ok(())
        }),
    });
    collect_semantic_errors(units, &unit.warnings)
}
