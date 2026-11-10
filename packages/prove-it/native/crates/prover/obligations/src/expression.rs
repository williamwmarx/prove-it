//! tlapm's expression IR (E_t) with de Bruijn indices, and the visitors that map over it (Visit).
//! A port of `src/obligations/expression.ts`.
//!
//! Expressions and hypotheses are `Rc`-shared and immutable, as the TypeScript objects are; where
//! the TypeScript keys a cache by an object's identity, the Rust keys it by the `Rc`'s pointer.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use crate::errors::Result;
use crate::pragma::{OldMethod, PragmaSetting};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Locus {
    pub file: Rc<str>,
    pub start_line: u32,
    pub start_column: u32,
    pub end_line: u32,
    pub end_column: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Channel {
    Toolbox,
    ToolboxOnly,
    Stderr,
    Stdout,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObligationWarning {
    pub text: String,
    pub channel: Channel,
}

/// `Warn`: where the obligations report a warning.
pub type Warn<'a> = dyn FnMut(ObligationWarning) + 'a;

pub fn get_locus_position(locus: &Locus) -> String {
    let end = i64::from(locus.end_column) - 1;
    if locus.start_line != locus.end_line {
        return format!(
            "line {}, character {} to line {}, character {}",
            locus.start_line, locus.start_column, locus.end_line, end
        );
    }
    if i64::from(locus.start_column) >= end {
        format!(
            "line {}, character {}",
            locus.start_line, locus.start_column
        )
    } else {
        format!(
            "line {}, characters {}-{}",
            locus.start_line, locus.start_column, end
        )
    }
}

pub fn get_locus_text(locus: &Locus) -> String {
    format!(
        "File {}, {}",
        crate::errors::quote_json(&locus.file),
        get_locus_position(locus)
    )
}

pub fn get_location_text(locus: Option<&Locus>) -> String {
    locus.map_or_else(|| "<unknown location>".to_owned(), get_locus_text)
}

pub fn get_at_prefix(locus: Option<&Locus>) -> String {
    format!("{}:\n", get_location_text(locus))
}

pub fn get_error_note(locus: Option<&Locus>, message: &str) -> ObligationWarning {
    ObligationWarning {
        text: format!("{}Error: {}", get_at_prefix(locus), message),
        channel: Channel::Stderr,
    }
}

pub fn get_locus_prefix(locus: Option<&Locus>) -> String {
    locus.map_or_else(String::new, |locus| {
        format!("{} :\n", get_locus_text(locus))
    })
}

macro_rules! builtins {
    ($($name:ident),* $(,)?) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
        pub enum Builtin {
            $($name,)*
        }

        impl Builtin {
            /// The name the TypeScript gives it, which is tlapm's constructor's.
            pub fn name(self) -> &'static str {
                match self {
                    $(Self::$name => builtins!(@name $name),)*
                }
            }
        }
    };
    (@name TRUE) => { "TRUE" };
    (@name $name:ident) => { stringify!($name) };
}

builtins!(
    TRUE,
    FALSE,
    Implies,
    Equiv,
    Conj,
    Disj,
    Neg,
    Eq,
    Neq,
    STRING,
    BOOLEAN,
    SUBSET,
    UNION,
    DOMAIN,
    Subseteq,
    Mem,
    Notmem,
    Setminus,
    Cap,
    Cup,
    Prime,
    StrongPrime,
    Leadsto,
    ENABLED,
    UNCHANGED,
    Cdot,
    Actplus,
    BoxTrue,
    BoxFalse,
    Diamond,
    Nat,
    Int,
    Real,
    Plus,
    Minus,
    Uminus,
    Times,
    Ratio,
    Quotient,
    Remainder,
    Exp,
    Infinity,
    Lteq,
    Lt,
    Gteq,
    Gt,
    Divides,
    Range,
    Seq,
    Len,
    BSeq,
    Cat,
    Append,
    Head,
    Tail,
    SubSeq,
    SelectSeq,
    OneArg,
    Extend,
    Print,
    PrintT,
    Assert,
    JavaTime,
    TLCGet,
    TLCSet,
    Permutations,
    SortSeq,
    RandomElement,
    Any,
    ToString,
    Unprimable,
    Irregular,
);

/// `Shape`: an operator's arity, 0 for an expression.
pub type Shape = usize;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Level {
    Constant,
    State,
    Action,
    Temporal,
    Unknown,
}

#[derive(Clone, Debug)]
pub enum BoundDomain {
    NoDomain,
    Domain(Expr),
    Ditto,
}

#[derive(Clone, Debug)]
pub struct Bound {
    pub name: String,
    pub level: Level,
    pub domain: BoundDomain,
}

#[derive(Clone, Debug)]
pub enum Selector {
    Down,
    Number(usize),
    Left,
    Right,
    At,
    Instance(Vec<Expr>),
    Label { label: String, args: Vec<Expr> },
}

#[derive(Clone, Debug)]
pub enum ExceptPoint {
    Dot(String),
    Apply(Expr),
}

#[derive(Clone, Debug)]
pub struct ExceptSpec {
    pub trail: Vec<ExceptPoint>,
    pub value: Expr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct XlabelIndex {
    pub name: String,
    pub index: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ParenForm {
    Syntax,
    Nlabel {
        label: String,
        names: Vec<String>,
    },
    Xlabel {
        label: String,
        indices: Vec<XlabelIndex>,
    },
}

#[derive(Clone, Debug)]
pub struct Param {
    pub name: String,
    pub shape: Shape,
    pub location: Option<Locus>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Bullet {
    And,
    Or,
    Refs,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Quantifier {
    Forall,
    Exists,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Modal {
    Box,
    Dia,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Fairness {
    Weak,
    Strong,
}

#[derive(Clone, Debug)]
pub struct Field {
    pub name: String,
    pub value: Expr,
}

#[derive(Clone, Debug)]
pub struct CaseArm {
    pub condition: Expr,
    pub body: Expr,
}

/// An expression: `ExprCore & ExprProps`. `is_atomic` is `Expr.Deref.atomic`: a resolved
/// subexpression reference, which has no subexpressions.
pub type Expr = Rc<ExprNode>;

#[derive(Clone, Debug)]
pub struct ExprNode {
    pub core: ExprCore,
    pub location: Option<Locus>,
    pub is_atomic: bool,
}

/// `ExprProps`: the properties `at` carries from one node to another.
#[derive(Clone, Debug, Default)]
pub struct ExprProps {
    pub location: Option<Locus>,
    pub is_atomic: bool,
}

#[derive(Clone, Debug)]
pub enum ExprCore {
    Ix {
        index: usize,
    },
    Opaque {
        name: String,
    },
    Internal {
        builtin: Builtin,
    },
    Lambda {
        params: Vec<Param>,
        body: Expr,
    },
    Sequent {
        sequent: Sequent,
    },
    Bang {
        expression: Expr,
        selectors: Vec<Selector>,
    },
    Apply {
        operator: Expr,
        args: Vec<Expr>,
    },
    With {
        expression: Expr,
        method: OldMethod,
    },
    If {
        condition: Expr,
        consequent: Expr,
        alternative: Expr,
    },
    List {
        bullet: Bullet,
        items: Vec<Expr>,
    },
    Let {
        definitions: Vec<Defn>,
        body: Expr,
    },
    Quant {
        quantifier: Quantifier,
        bounds: Vec<Bound>,
        body: Expr,
    },
    Tquant {
        quantifier: Quantifier,
        names: Vec<String>,
        body: Expr,
    },
    Choose {
        name: String,
        domain: Option<Expr>,
        body: Expr,
    },
    SetSt {
        name: String,
        domain: Expr,
        body: Expr,
    },
    SetOf {
        element: Expr,
        bounds: Vec<Bound>,
    },
    SetEnum {
        elements: Vec<Expr>,
    },
    Product {
        factors: Vec<Expr>,
    },
    Tuple {
        elements: Vec<Expr>,
    },
    Fcn {
        bounds: Vec<Bound>,
        body: Expr,
    },
    FcnApp {
        function: Expr,
        args: Vec<Expr>,
    },
    Arrow {
        domain: Expr,
        range: Expr,
    },
    Rect {
        fields: Vec<Field>,
    },
    Record {
        fields: Vec<Field>,
    },
    Except {
        function: Expr,
        specs: Vec<ExceptSpec>,
    },
    Dot {
        expression: Expr,
        field: String,
    },
    Sub {
        modal: Modal,
        action: Expr,
        subscript: Expr,
    },
    Tsub {
        modal: Modal,
        action: Expr,
        subscript: Expr,
    },
    Fair {
        fairness: Fairness,
        subscript: Expr,
        action: Expr,
    },
    Case {
        arms: Vec<CaseArm>,
        other: Option<Expr>,
    },
    String {
        value: String,
    },
    Num {
        integer: String,
        fraction: String,
    },
    At {
        is_except: bool,
    },
    Parens {
        expression: Expr,
        form: ParenForm,
    },
}

impl ExprNode {
    pub fn props(&self) -> ExprProps {
        ExprProps {
            location: self.location.clone(),
            is_atomic: self.is_atomic,
        }
    }

    /// The same properties on another core: `{...expression, ...changes}` in the TypeScript.
    pub fn with_core(&self, core: ExprCore) -> Expr {
        Rc::new(Self {
            core,
            location: self.location.clone(),
            is_atomic: self.is_atomic,
        })
    }
}

/// A node with no properties.
pub fn expr(core: ExprCore) -> Expr {
    Rc::new(ExprNode {
        core,
        location: None,
        is_atomic: false,
    })
}

/// A node with a location and nothing else.
pub fn located(core: ExprCore, location: Option<Locus>) -> Expr {
    Rc::new(ExprNode {
        core,
        location,
        is_atomic: false,
    })
}

#[derive(Clone, Debug)]
pub struct Substitution {
    pub name: String,
    pub expression: Expr,
}

#[derive(Clone, Debug)]
pub struct InstanceDefinition {
    pub args: Vec<String>,
    pub module: String,
    pub substitutions: Vec<Substitution>,
    pub location: Option<Locus>,
}

#[derive(Clone, Debug)]
pub struct Defn {
    pub core: DefnCore,
    pub location: Option<Locus>,
}

#[derive(Clone, Debug)]
pub enum DefnCore {
    Recursive {
        name: String,
        shape: Shape,
    },
    Operator {
        name: String,
        body: Expr,
    },
    Instance {
        name: String,
        instance: InstanceDefinition,
    },
    Bpragma {
        name: String,
        body: Expr,
        methods: Vec<Vec<PragmaSetting>>,
    },
}

impl Defn {
    pub fn name(&self) -> &str {
        match &self.core {
            DefnCore::Recursive { name, .. }
            | DefnCore::Operator { name, .. }
            | DefnCore::Instance { name, .. }
            | DefnCore::Bpragma { name, .. } => name,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Visibility {
    Visible,
    Hidden,
}

/// When a fact holds: at every point of a behavior, or only at the current one.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Time {
    Now,
    Always,
}

/// A step or a DEFINE in a proof keeps the time of the scope it is made in.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum WhereDefined {
    Builtin,
    User,
    Proof(Time),
}

pub type Hyp = Rc<HypNode>;

#[derive(Clone, Debug)]
pub struct HypNode {
    pub core: HypCore,
    pub location: Option<Locus>,
}

#[derive(Clone, Debug)]
pub enum HypCore {
    Fresh {
        name: String,
        shape: Shape,
        level: Level,
        domain: Option<Expr>,
        domain_visibility: Visibility,
    },
    Flex {
        name: String,
    },
    Defn {
        definition: Defn,
        where_defined: WhereDefined,
        visibility: Visibility,
        is_local: bool,
        /// Module.Elab judges whether each module definition is constant. One that anonymization
        /// meets in a proof, such as a step or a DEFINE, has no judgment, so tlapm never counts
        /// it constant.
        is_constness_unset: bool,
    },
    Fact {
        expression: Expr,
        visibility: Visibility,
        time: Time,
        use_location: Option<Locus>,
    },
}

impl HypNode {
    /// The same location on another core.
    pub fn with_core(&self, core: HypCore) -> Hyp {
        Rc::new(Self {
            core,
            location: self.location.clone(),
        })
    }
}

pub fn hyp(core: HypCore) -> Hyp {
    Rc::new(HypNode {
        core,
        location: None,
    })
}

#[derive(Clone, Debug)]
pub struct Sequent {
    pub context: Vec<Hyp>,
    pub active: Expr,
}

/// tlapm's `core @@ from`, which takes the properties of from.
pub fn at(core: ExprCore, from: &ExprNode) -> Expr {
    from.with_core(core)
}

/// `at` from bare properties.
pub fn at_props(core: ExprCore, from: &ExprProps) -> Expr {
    Rc::new(ExprNode {
        core,
        location: from.location.clone(),
        is_atomic: from.is_atomic,
    })
}

pub fn get_hyp_name(hyp: &HypNode) -> Option<&str> {
    match &hyp.core {
        HypCore::Fresh { name, .. } | HypCore::Flex { name } => Some(name),
        HypCore::Defn { definition, .. } => Some(definition.name()),
        HypCore::Fact { .. } => None,
    }
}

/// `isBuiltinApply`: the arguments when the expression applies the builtin.
pub fn is_builtin_apply(expression: &ExprNode, builtin: Builtin) -> Option<&[Expr]> {
    match &expression.core {
        ExprCore::Apply { operator, args } => match operator.core {
            ExprCore::Internal { builtin: applied } if applied == builtin => Some(args),
            _ => None,
        },
        _ => None,
    }
}

pub fn apply_builtin(builtin: Builtin, args: Vec<Expr>, from: &ExprProps) -> Expr {
    at_props(
        ExprCore::Apply {
            operator: at_props(ExprCore::Internal { builtin }, from),
            args,
        },
        from,
    )
}

/// `exprifySequent`: the active expression alone when there is no context. The result is a core
/// in the TypeScript; here it is a whole node, the active expression itself when the context is
/// empty, so callers that take its properties should use `exprify_sequent_core`.
pub fn exprify_sequent_core(sequent: &Sequent) -> ExprCore {
    if sequent.context.is_empty() {
        sequent.active.core.clone()
    } else {
        ExprCore::Sequent {
            sequent: sequent.clone(),
        }
    }
}

/// A persistent context, newest hypothesis first, so binders extend it without copying.
#[derive(Debug)]
pub struct Scope {
    pub hyp: Hyp,
    pub rest: ScopeRef,
    pub size: usize,
}

pub type ScopeRef = Option<Rc<Scope>>;

pub fn adjoin(scope: &ScopeRef, hyp: &Hyp) -> ScopeRef {
    Some(Rc::new(Scope {
        hyp: hyp.clone(),
        rest: scope.clone(),
        size: scope.as_ref().map_or(0, |scope| scope.size) + 1,
    }))
}

pub fn adjoin_all(scope: &ScopeRef, hyps: &[Hyp]) -> ScopeRef {
    hyps.iter()
        .fold(scope.clone(), |current, hyp| adjoin(&current, hyp))
}

pub fn get_scope_size(scope: &ScopeRef) -> usize {
    scope.as_ref().map_or(0, |scope| scope.size)
}

pub fn get_scope_hyps(scope: &ScopeRef) -> Vec<Hyp> {
    let mut hyps = Vec::new();
    let mut current = scope.as_deref();
    while let Some(node) = current {
        hyps.push(node.hyp.clone());
        current = node.rest.as_deref();
    }
    hyps.reverse();
    hyps
}

/// The depth (0 for the newest) and the hypothesis of the newest one named `name`.
pub fn find_named(scope: &ScopeRef, name: &str) -> Option<(usize, Hyp)> {
    let mut depth = 0;
    let mut current = scope.as_deref();
    while let Some(node) = current {
        if get_hyp_name(&node.hyp) == Some(name) {
            return Some((depth, node.hyp.clone()));
        }
        depth += 1;
        current = node.rest.as_deref();
    }
    None
}

pub fn get_scope_at(scope: &ScopeRef, depth: usize) -> ScopeRef {
    let mut current = scope.clone();
    for _ in 0..depth {
        current = current?.rest.clone();
    }
    current
}

/// `mapAccumulate`: a fold that keeps each step's result.
pub fn map_accumulate<State, Item, Output>(
    state: State,
    items: &[Item],
    mut step: impl FnMut(State, &Item) -> Result<(State, Output)>,
) -> Result<(State, Vec<Output>)> {
    let mut results = Vec::with_capacity(items.len());
    let mut current = state;
    for item in items {
        let (next, result) = step(current, item)?;
        results.push(result);
        current = next;
    }
    Ok((current, results))
}

type PrefixTable<State> = HashMap<*const HypNode, (Hyp, Rc<MappedPrefix<State>>)>;

/// A mapped context prefix: the hypothesis its last key maps to, if any, and the state after it.
struct MappedPrefix<State> {
    state: State,
    hyp: Option<Hyp>,
    parent: Option<Rc<MappedPrefix<State>>>,
    /// Keyed by the key hypothesis's pointer. The key is kept alive beside the entry, so the
    /// pointer cannot be reused while the entry exists, which a `WeakMap` gives the TypeScript.
    next: RefCell<PrefixTable<State>>,
}

/// `createContextMap`: `mapAccumulate` over a context that maps each prefix of keys once, as the
/// obligations of a module share most of their context by identity. The input at each position
/// must depend on the keys up to it alone, and the step on the input, its key, and the state.
pub struct ContextMap<State, Step> {
    empty: Rc<MappedPrefix<State>>,
    step: Step,
}

pub struct MappedContext<State> {
    pub state: State,
    pub context: Vec<Hyp>,
}

impl<State: Clone, Step: FnMut(&State, &Hyp, &Hyp) -> Result<(State, Option<Hyp>)>>
    ContextMap<State, Step>
{
    pub fn new(initial: State, step: Step) -> Self {
        Self {
            empty: Rc::new(MappedPrefix {
                state: initial,
                hyp: None,
                parent: None,
                next: RefCell::new(HashMap::new()),
            }),
            step,
        }
    }

    /// Maps `keys`, with `inputs` (the keys themselves by default) as what each step reads.
    pub fn map(&mut self, keys: &[Hyp], inputs: Option<&[Hyp]>) -> Result<MappedContext<State>> {
        let inputs = inputs.unwrap_or(keys);
        let mut prefix = self.empty.clone();
        for (index, key) in keys.iter().enumerate() {
            let known = prefix
                .next
                .borrow()
                .get(&Rc::as_ptr(key))
                .map(|entry| entry.1.clone());
            if let Some(known) = known {
                prefix = known;
                continue;
            }
            let (state, hyp) = (self.step)(&prefix.state, &inputs[index], key)?;
            let mapped = Rc::new(MappedPrefix {
                state,
                hyp,
                parent: Some(prefix.clone()),
                next: RefCell::new(HashMap::new()),
            });
            prefix
                .next
                .borrow_mut()
                .insert(Rc::as_ptr(key), (key.clone(), mapped.clone()));
            prefix = mapped;
        }
        let mut context = Vec::new();
        let mut current = Some(prefix.clone());
        while let Some(node) = current {
            if let Some(hyp) = &node.hyp {
                context.push(hyp.clone());
            }
            current = node.parent.clone();
        }
        context.reverse();
        Ok(MappedContext {
            state: prefix.state.clone(),
            context,
        })
    }
}

pub fn get_fresh(name: &str, level: Level, shape: Shape) -> Hyp {
    hyp(HypCore::Fresh {
        name: name.to_owned(),
        shape,
        level,
        domain: None,
        domain_visibility: Visibility::Visible,
    })
}

pub fn get_bounded_fresh(name: &str, domain: Expr) -> Hyp {
    hyp(HypCore::Fresh {
        name: name.to_owned(),
        shape: 0,
        level: Level::Constant,
        domain: Some(domain),
        domain_visibility: Visibility::Visible,
    })
}

/// `getFact`. The TypeScript names the property `location`, which a `Fact` hypothesis reads as
/// its own location.
pub fn get_fact(
    expression: Expr,
    visibility: Visibility,
    time: Time,
    location: Option<Locus>,
) -> Hyp {
    Rc::new(HypNode {
        core: HypCore::Fact {
            expression,
            visibility,
            time,
            use_location: None,
        },
        location,
    })
}

/// What a quantifier binds each name as, as Visit.map does.
pub fn get_bound_fresh(bound: &Bound) -> Hyp {
    get_fresh(&bound.name, bound.level, 0)
}

/// What a LAMBDA binds each parameter as.
pub fn get_param_fresh(param: &Param) -> Hyp {
    get_fresh(&param.name, Level::Unknown, param.shape)
}

/// What a LET binds each definition as.
pub fn get_local_defn(definition: Defn) -> Hyp {
    hyp(HypCore::Defn {
        definition,
        where_defined: WhereDefined::User,
        visibility: Visibility::Visible,
        is_local: true,
        is_constness_unset: false,
    })
}

/// The node without its properties, as tlapm's `e.core`.
pub fn strip_props(expression: &Expr) -> Expr {
    if expression.location.is_none() && !expression.is_atomic {
        return expression.clone();
    }
    expr(expression.core.clone())
}

pub fn map_bound_domains(
    bounds: &[Bound],
    map: &mut dyn FnMut(&Expr) -> Result<Expr>,
) -> Result<Vec<Bound>> {
    bounds
        .iter()
        .map(|bound| {
            Ok(match &bound.domain {
                BoundDomain::Domain(expression) => Bound {
                    domain: BoundDomain::Domain(map(expression)?),
                    ..bound.clone()
                },
                _ => bound.clone(),
            })
        })
        .collect()
}

pub fn map_selector_args(
    selector: &Selector,
    map: &mut dyn FnMut(&Expr) -> Result<Expr>,
) -> Result<Selector> {
    Ok(match selector {
        Selector::Instance(args) => {
            Selector::Instance(args.iter().map(&mut *map).collect::<Result<_>>()?)
        }
        Selector::Label { label, args } => Selector::Label {
            label: label.clone(),
            args: args.iter().map(&mut *map).collect::<Result<_>>()?,
        },
        other => other.clone(),
    })
}

pub fn map_except_specs(
    specs: &[ExceptSpec],
    map: &mut dyn FnMut(&Expr) -> Result<Expr>,
) -> Result<Vec<ExceptSpec>> {
    specs
        .iter()
        .map(|spec| {
            let value = map(&spec.value)?;
            let trail = spec
                .trail
                .iter()
                .map(|point| {
                    Ok(match point {
                        ExceptPoint::Apply(expression) => ExceptPoint::Apply(map(expression)?),
                        ExceptPoint::Dot(field) => ExceptPoint::Dot(field.clone()),
                    })
                })
                .collect::<Result<_>>()?;
            Ok(ExceptSpec { trail, value })
        })
        .collect()
}

pub fn map_defn_body(
    definition: &Defn,
    map: &mut dyn FnMut(&Expr) -> Result<Expr>,
) -> Result<Defn> {
    let core = match &definition.core {
        DefnCore::Operator { name, body } => DefnCore::Operator {
            name: name.clone(),
            body: map(body)?,
        },
        DefnCore::Bpragma {
            name,
            body,
            methods,
        } => DefnCore::Bpragma {
            name: name.clone(),
            body: map(body)?,
            methods: methods.clone(),
        },
        _ => return Ok(definition.clone()),
    };
    Ok(Defn {
        core,
        location: definition.location.clone(),
    })
}

/// Which hypotheses of a sequent a visitor visits: `Visit.map_visible_hyp` binds hidden ones
/// without visiting them, and `Visit.map` visits them too.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Hyps {
    Visible,
    All,
}

pub fn map_hyp(hyp: &Hyp, map: &mut dyn FnMut(&Expr) -> Result<Expr>, hyps: Hyps) -> Result<Hyp> {
    match &hyp.core {
        HypCore::Fresh {
            name,
            shape,
            level,
            domain: Some(domain),
            domain_visibility,
        } => Ok(hyp.with_core(HypCore::Fresh {
            name: name.clone(),
            shape: *shape,
            level: *level,
            domain: Some(map(domain)?),
            domain_visibility: *domain_visibility,
        })),
        HypCore::Fresh { .. } | HypCore::Flex { .. } => Ok(hyp.clone()),
        HypCore::Defn { visibility, .. } | HypCore::Fact { visibility, .. }
            if hyps == Hyps::Visible && *visibility == Visibility::Hidden =>
        {
            Ok(hyp.clone())
        }
        HypCore::Defn {
            definition,
            where_defined,
            visibility,
            is_local,
            is_constness_unset,
        } => Ok(hyp.with_core(HypCore::Defn {
            definition: map_defn_body(definition, map)?,
            where_defined: *where_defined,
            visibility: *visibility,
            is_local: *is_local,
            is_constness_unset: *is_constness_unset,
        })),
        HypCore::Fact {
            expression,
            visibility,
            time,
            use_location,
        } => Ok(hyp.with_core(HypCore::Fact {
            expression: map(expression)?,
            visibility: *visibility,
            time: *time,
            use_location: use_location.clone(),
        })),
    }
}

/// `Visit.map`, threading a state through each binder: a scope or a substitution. Children map in
/// OCaml evaluation order, last constructor argument first, which decides the error tlapm reports.
pub fn map_scoped<State: Clone>(
    state: &State,
    expression: &Expr,
    map: &mut dyn FnMut(&State, &Expr) -> Result<Expr>,
    bind: &mut dyn FnMut(&State, &Hyp) -> State,
    hyps: Hyps,
) -> Result<Expr> {
    let bind_bounds = |bounds: &[Bound], bind: &mut dyn FnMut(&State, &Hyp) -> State| {
        bounds.iter().fold(state.clone(), |current, bound| {
            bind(&current, &get_bound_fresh(bound))
        })
    };
    let core = match &expression.core {
        ExprCore::Ix { .. }
        | ExprCore::Internal { .. }
        | ExprCore::Opaque { .. }
        | ExprCore::String { .. }
        | ExprCore::Num { .. }
        | ExprCore::At { .. } => return Ok(expression.clone()),
        ExprCore::Lambda { params, body } => {
            let inner = params.iter().fold(state.clone(), |current, param| {
                let fresh = get_param_fresh(param);
                let fresh = match &param.location {
                    Some(location) => Rc::new(HypNode {
                        core: fresh.core.clone(),
                        location: Some(location.clone()),
                    }),
                    None => fresh,
                };
                bind(&current, &fresh)
            });
            ExprCore::Lambda {
                params: params.clone(),
                body: map(&inner, body)?,
            }
        }
        ExprCore::Sequent { sequent } => {
            let (inner, context) =
                map_accumulate(state.clone(), &sequent.context, |current, hyp| {
                    let mapped = map_hyp(hyp, &mut |child| map(&current, child), hyps)?;
                    Ok((bind(&current, &mapped), mapped))
                })?;
            ExprCore::Sequent {
                sequent: Sequent {
                    context,
                    active: map(&inner, &sequent.active)?,
                },
            }
        }
        ExprCore::Let { definitions, body } => {
            let (inner, definitions) =
                map_accumulate(state.clone(), definitions, |current, definition| {
                    let mapped = map_defn_body(definition, &mut |body| map(&current, body))?;
                    Ok((bind(&current, &get_local_defn(mapped.clone())), mapped))
                })?;
            ExprCore::Let {
                definitions,
                body: map(&inner, body)?,
            }
        }
        ExprCore::Quant {
            quantifier,
            bounds,
            body,
        } => {
            let bounds = map_bound_domains(bounds, &mut |inner| map(state, inner))?;
            let inner = bind_bounds(&bounds, bind);
            ExprCore::Quant {
                quantifier: *quantifier,
                body: map(&inner, body)?,
                bounds,
            }
        }
        ExprCore::Fcn { bounds, body } => {
            let bounds = map_bound_domains(bounds, &mut |inner| map(state, inner))?;
            let inner = bind_bounds(&bounds, bind);
            ExprCore::Fcn {
                body: map(&inner, body)?,
                bounds,
            }
        }
        ExprCore::SetOf { element, bounds } => {
            let bounds = map_bound_domains(bounds, &mut |inner| map(state, inner))?;
            let inner = bind_bounds(&bounds, bind);
            ExprCore::SetOf {
                element: map(&inner, element)?,
                bounds,
            }
        }
        ExprCore::Tquant {
            quantifier,
            names,
            body,
        } => {
            let inner = names.iter().fold(state.clone(), |current, name| {
                bind(&current, &hyp(HypCore::Flex { name: name.clone() }))
            });
            ExprCore::Tquant {
                quantifier: *quantifier,
                names: names.clone(),
                body: map(&inner, body)?,
            }
        }
        ExprCore::Choose { name, domain, body } => {
            let domain = domain
                .as_ref()
                .map(|domain| map(state, domain))
                .transpose()?;
            let bound = match &domain {
                Some(domain) => get_bounded_fresh(name, domain.clone()),
                None => get_fresh(name, Level::Constant, 0),
            };
            let inner = bind(state, &bound);
            ExprCore::Choose {
                name: name.clone(),
                domain,
                body: map(&inner, body)?,
            }
        }
        ExprCore::SetSt { name, domain, body } => {
            let domain = map(state, domain)?;
            let inner = bind(state, &get_bounded_fresh(name, domain.clone()));
            ExprCore::SetSt {
                name: name.clone(),
                domain,
                body: map(&inner, body)?,
            }
        }
        ExprCore::Bang {
            expression: inner,
            selectors,
        } => {
            let selectors = selectors
                .iter()
                .map(|selector| map_selector_args(selector, &mut |arg| map(state, arg)))
                .collect::<Result<Vec<_>>>()?;
            ExprCore::Bang {
                expression: map(state, inner)?,
                selectors,
            }
        }
        ExprCore::Apply { operator, args } => {
            let args = map_all(state, args, map)?;
            ExprCore::Apply {
                operator: map(state, operator)?,
                args,
            }
        }
        ExprCore::With {
            expression: inner,
            method,
        } => ExprCore::With {
            expression: map(state, inner)?,
            method: method.clone(),
        },
        ExprCore::Dot {
            expression: inner,
            field,
        } => ExprCore::Dot {
            expression: map(state, inner)?,
            field: field.clone(),
        },
        ExprCore::Parens {
            expression: inner,
            form,
        } => ExprCore::Parens {
            expression: map(state, inner)?,
            form: form.clone(),
        },
        ExprCore::If {
            condition,
            consequent,
            alternative,
        } => {
            let alternative = map(state, alternative)?;
            let consequent = map(state, consequent)?;
            ExprCore::If {
                condition: map(state, condition)?,
                consequent,
                alternative,
            }
        }
        ExprCore::List { bullet, items } => ExprCore::List {
            bullet: *bullet,
            items: map_all(state, items, map)?,
        },
        ExprCore::SetEnum { elements } => ExprCore::SetEnum {
            elements: map_all(state, elements, map)?,
        },
        ExprCore::Tuple { elements } => ExprCore::Tuple {
            elements: map_all(state, elements, map)?,
        },
        ExprCore::Product { factors } => ExprCore::Product {
            factors: map_all(state, factors, map)?,
        },
        ExprCore::FcnApp { function, args } => {
            let args = map_all(state, args, map)?;
            ExprCore::FcnApp {
                function: map(state, function)?,
                args,
            }
        }
        ExprCore::Arrow { domain, range } => {
            let range = map(state, range)?;
            ExprCore::Arrow {
                domain: map(state, domain)?,
                range,
            }
        }
        ExprCore::Rect { fields } => ExprCore::Rect {
            fields: map_fields(state, fields, map)?,
        },
        ExprCore::Record { fields } => ExprCore::Record {
            fields: map_fields(state, fields, map)?,
        },
        ExprCore::Except { function, specs } => {
            let specs = map_except_specs(specs, &mut |inner| map(state, inner))?;
            ExprCore::Except {
                function: map(state, function)?,
                specs,
            }
        }
        ExprCore::Sub {
            modal,
            action,
            subscript,
        } => {
            let subscript = map(state, subscript)?;
            ExprCore::Sub {
                modal: *modal,
                action: map(state, action)?,
                subscript,
            }
        }
        ExprCore::Tsub {
            modal,
            action,
            subscript,
        } => {
            let subscript = map(state, subscript)?;
            ExprCore::Tsub {
                modal: *modal,
                action: map(state, action)?,
                subscript,
            }
        }
        ExprCore::Fair {
            fairness,
            subscript,
            action,
        } => {
            let subscript = map(state, subscript)?;
            ExprCore::Fair {
                fairness: *fairness,
                action: map(state, action)?,
                subscript,
            }
        }
        ExprCore::Case { arms, other } => {
            let other = other.as_ref().map(|other| map(state, other)).transpose()?;
            let arms = arms
                .iter()
                .map(|arm| {
                    let body = map(state, &arm.body)?;
                    Ok(CaseArm {
                        condition: map(state, &arm.condition)?,
                        body,
                    })
                })
                .collect::<Result<_>>()?;
            ExprCore::Case { arms, other }
        }
    };
    Ok(expression.with_core(core))
}

fn map_all<State>(
    state: &State,
    items: &[Expr],
    map: &mut dyn FnMut(&State, &Expr) -> Result<Expr>,
) -> Result<Vec<Expr>> {
    items.iter().map(|item| map(state, item)).collect()
}

fn map_fields<State>(
    state: &State,
    fields: &[Field],
    map: &mut dyn FnMut(&State, &Expr) -> Result<Expr>,
) -> Result<Vec<Field>> {
    fields
        .iter()
        .map(|field| {
            Ok(Field {
                name: field.name.clone(),
                value: map(state, &field.value)?,
            })
        })
        .collect()
}

/// `Visit.map` without a state: every child, the hidden hypotheses of an ASSUME included.
pub fn map_children(expression: &Expr, map: &mut dyn FnMut(&Expr) -> Result<Expr>) -> Result<Expr> {
    map_scoped(
        &(),
        expression,
        &mut |_, inner| map(inner),
        &mut |_, _| (),
        Hyps::All,
    )
}

pub fn get_children(expression: &Expr) -> Vec<Expr> {
    let mut children = Vec::new();
    // The visitor here cannot fail.
    let _ = map_children(expression, &mut |inner| {
        children.push(inner.clone());
        Ok(inner.clone())
    });
    children
}
