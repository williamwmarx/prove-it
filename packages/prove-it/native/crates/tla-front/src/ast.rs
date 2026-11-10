//! The AST of `src/ast.ts`. A node that TypeScript reaches from two places, such as the set of
//! `\A x, y \in S` or a theorem's statement that its name defines, is one `Rc` here, so later stages
//! see the same identities the TypeScript ones do.

use std::cell::{Cell, RefCell};
use std::rc::Rc;

pub type Name = Rc<str>;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Position {
    pub line: u32,
    pub column: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceRange {
    pub module: Name,
    pub start: Position,
    pub end: Position,
}

pub type Range = SourceRange;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Location {
    pub line: u32,
    pub column: u32,
    pub range: Option<Range>,
}

impl Location {
    pub fn position(&self) -> Position {
        Position {
            line: self.line,
            column: self.column,
        }
    }
}

pub type Expr = Rc<Expression>;

#[derive(Clone, Debug)]
pub struct Expression {
    pub kind: ExpressionKind,
    pub location: Location,
    pub resolved: Resolved,
}

/// What `resolve.ts` writes on a node of the TypeScript AST: the key a name resolves to, in place
/// of the name it is written with (`key`), its `LOCAL_RESOLUTION` (`is_local`), and a function
/// construction's `isRecursive`. A copy of a node carries them, as a copy made by spreading a
/// TypeScript node does.
#[derive(Clone, Debug, Default)]
pub struct Resolved {
    pub key: RefCell<Option<Name>>,
    pub is_local: Cell<bool>,
    pub is_recursive: Cell<bool>,
}

impl Expression {
    pub fn new(kind: ExpressionKind, location: Location) -> Expression {
        Expression {
            kind,
            location,
            resolved: Resolved::default(),
        }
    }

    /// The name of an `Identifier` or the operator of an `Apply` or `OperatorReference`, as
    /// resolution leaves it: the key of the symbol it names, once resolved.
    pub fn reference(&self) -> Option<Name> {
        let written = match &self.kind {
            ExpressionKind::Identifier { name, .. } => name,
            ExpressionKind::Apply { operator, .. }
            | ExpressionKind::OperatorReference { operator, .. } => operator,
            _ => return None,
        };
        Some(
            self.resolved
                .key
                .borrow()
                .clone()
                .unwrap_or_else(|| written.clone()),
        )
    }

    /// `isLocallyResolved`.
    pub fn is_locally_resolved(&self) -> bool {
        matches!(
            self.kind,
            ExpressionKind::Identifier { .. } | ExpressionKind::Apply { .. }
        ) && self.resolved.is_local.get()
    }
}

#[derive(Clone, Debug)]
pub enum BoundPattern {
    Name {
        name: Name,
        ranges: Vec<Range>,
    },
    Tuple {
        names: Vec<Name>,
        ranges: Vec<Range>,
    },
}

impl BoundPattern {
    pub fn names(&self) -> &[Name] {
        match self {
            BoundPattern::Name { name, .. } => std::slice::from_ref(name),
            BoundPattern::Tuple { names, .. } => names,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Bound {
    pub pattern: BoundPattern,
    pub set: Expr,
}

#[derive(Clone, Debug)]
pub struct CaseArm {
    pub condition: Expr,
    pub body: Expr,
}

#[derive(Clone, Debug)]
pub struct RecordField {
    pub name: Name,
    pub value: Expr,
    pub location: Location,
}

#[derive(Clone, Debug)]
pub enum ExceptPathStep {
    Field(Name),
    Index(Vec<Expr>),
}

#[derive(Clone, Debug)]
pub struct ExceptUpdate {
    pub path: Vec<ExceptPathStep>,
    pub value: Expr,
}

#[derive(Clone, Debug)]
pub enum Operand {
    Index(f64),
    First,
    Last,
}

#[derive(Clone, Debug)]
pub enum Selector {
    Name { name: Name, args: Vec<Expr> },
    Operand(Operand),
    Bound(Vec<Expr>),
    At,
    Colon,
}

impl Selector {
    pub fn args(&self) -> &[Expr] {
        match self {
            Selector::Name { args, .. } | Selector::Bound(args) => args,
            _ => &[],
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Quantifier {
    Forall,
    Exists,
}

#[derive(Clone, Debug)]
pub enum ExpressionKind {
    Number {
        value: f64,
        text: Name,
    },
    Decimal {
        text: Name,
    },
    String {
        value: Name,
    },
    /// `selector_ranges` holds the range of each part of a name such as `foo!lab`.
    Identifier {
        name: Name,
        spelling: Option<Name>,
        selector_ranges: Option<Vec<Range>>,
    },
    Apply {
        operator: Name,
        spelling: Option<Name>,
        args: Vec<Expr>,
        argument_counts: Option<Vec<usize>>,
        arguments_range: Option<Range>,
        selector_ranges: Option<Vec<Range>>,
        argument_ranges: Option<Vec<Option<Range>>>,
    },
    OperatorReference {
        operator: Name,
        spelling: Option<Name>,
    },
    Lambda {
        params: Vec<Name>,
        param_ranges: Option<Vec<Range>>,
        body: Expr,
        operator: Option<Name>,
    },
    /// `And` when `is_and`, else `Or`.
    Junction {
        is_and: bool,
        operands: Vec<Expr>,
        is_bulleted: bool,
        prefix_ends: Option<Vec<Position>>,
    },
    Prime(Expr),
    Unchanged(Expr),
    Enabled(Expr),
    Always(Expr),
    Eventually(Expr),
    If {
        condition: Expr,
        consequent: Expr,
        alternative: Expr,
    },
    Case {
        arms: Vec<CaseArm>,
        other: Option<Expr>,
    },
    Let {
        definitions: Vec<Rc<Definition>>,
        instances: Option<Vec<Rc<Instance>>>,
        body: Expr,
    },
    Quantified {
        quantifier: Quantifier,
        bounds: Vec<Bound>,
        body: Expr,
    },
    UnboundedQuantifier {
        quantifier: Quantifier,
        names: Vec<Name>,
        name_ranges: Vec<Range>,
        is_temporal: bool,
        body: Expr,
    },
    Choose {
        pattern: BoundPattern,
        set: Option<Expr>,
        body: Expr,
    },
    SetEnumeration(Vec<Expr>),
    SetFilter {
        bound: Bound,
        predicate: Expr,
    },
    SetMap {
        expression: Expr,
        bounds: Vec<Bound>,
    },
    Tuple(Vec<Expr>),
    FunctionConstruction {
        bounds: Vec<Bound>,
        body: Expr,
    },
    FunctionSet {
        domain: Expr,
        range: Expr,
    },
    /// `Record`, or `RecordSet` when `is_set`.
    Record {
        is_set: bool,
        fields: Vec<RecordField>,
    },
    Except {
        function: Expr,
        updates: Vec<ExceptUpdate>,
    },
    ExceptAt,
    FunctionApplication {
        function: Expr,
        args: Vec<Expr>,
    },
    Bracket(Vec<Expr>),
    FieldAccess {
        record: Expr,
        field: Name,
    },
    Product(Vec<Expr>),
    /// `BoxAction`, or `AngleAction` when not `is_box`.
    Action {
        is_box: bool,
        action: Expr,
        subscript: Expr,
    },
    /// `WeakFairness`, or `StrongFairness` when `is_strong`. An instance's copy holds the
    /// `ENABLED` of its action with the instance's substitutions in `enabled`.
    Fairness {
        is_strong: bool,
        subscript: Expr,
        action: Expr,
        enabled: Option<Expr>,
    },
    Label {
        name: Name,
        params: Vec<Name>,
        param_ranges: Vec<Range>,
        body: Expr,
    },
    Subexpression {
        selectors: Vec<Selector>,
        selector_ranges: Vec<Range>,
        argument_ranges: Vec<Option<Range>>,
    },
}

/// A parameter the front end makes, such as an instance copy's, has no `location`.
#[derive(Clone, Debug)]
pub struct OperatorParam {
    pub name: Name,
    pub arity: usize,
    pub location: Option<Location>,
}

#[derive(Clone, Debug)]
pub enum DefinitionKind {
    Operator {
        params: Vec<OperatorParam>,
        body_range: Option<SourceRange>,
    },
    Function {
        bounds: Vec<Bound>,
    },
}

/// `is_self_referential` is a function definition's `isSelfReferential`, which resolution sets.
#[derive(Clone, Debug)]
pub struct Definition {
    pub name: Name,
    pub kind: DefinitionKind,
    pub body: Expr,
    pub is_local: bool,
    pub is_recursive: bool,
    pub location: Location,
    pub is_self_referential: Cell<Option<bool>>,
}

#[derive(Clone, Debug)]
pub struct Declaration {
    pub name: Name,
    pub arity: usize,
    pub location: Location,
}

#[derive(Clone, Debug)]
pub struct Assumption {
    pub name: Option<Name>,
    pub expression: Expr,
    pub is_axiom: bool,
    pub location: Location,
}

#[derive(Clone, Debug)]
pub struct InstanceSubstitution {
    pub name: Name,
    pub name_range: Range,
    pub expression: Expr,
}

#[derive(Clone, Debug)]
pub struct Instance {
    pub name: Option<Name>,
    pub params: Vec<OperatorParam>,
    pub module: Name,
    pub substitutions: Vec<InstanceSubstitution>,
    pub is_local: bool,
    pub location: Location,
    pub instance_range: Range,
    pub definition_range: Option<Range>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SymbolLevel {
    Constant,
    Variable,
    State,
    Action,
    Temporal,
}

impl SymbolLevel {
    pub fn name(self) -> &'static str {
        match self {
            SymbolLevel::Constant => "Constant",
            SymbolLevel::Variable => "Variable",
            SymbolLevel::State => "State",
            SymbolLevel::Action => "Action",
            SymbolLevel::Temporal => "Temporal",
        }
    }
}

#[derive(Clone, Debug)]
pub struct NewSymbol {
    pub name: Name,
    pub arity: usize,
    pub level: SymbolLevel,
    pub set: Option<Expr>,
    pub name_range: Option<Range>,
    pub location: Location,
}

#[derive(Clone, Debug)]
pub enum Assumed {
    Expression(Expr),
    NewSymbol(NewSymbol),
    AssumeProve(AssumeProve),
}

#[derive(Clone, Debug)]
pub struct AssumeProve {
    pub assumptions: Vec<Assumed>,
    pub conclusion: Expr,
    pub location: Location,
}

#[derive(Clone, Debug)]
pub enum Statement {
    Expression(Expr),
    AssumeProve(AssumeProve),
}

#[derive(Clone, Debug)]
pub enum Fact {
    Expression(Expr),
    Module { name: Name, location: Location },
}

/// A `USE`, or a `HIDE` when `is_hide`. `keyword` is the range of the keyword and any `ONLY`.
#[derive(Clone, Debug)]
pub struct UseOrHide {
    pub is_hide: bool,
    pub is_only: bool,
    pub facts: Vec<Fact>,
    pub defs: Vec<Fact>,
    pub keyword: Range,
    pub location: Location,
}

#[derive(Clone, Debug)]
pub enum ProofKind {
    Obvious {
        keyword: Range,
    },
    Omitted {
        keyword: Range,
    },
    By {
        is_only: bool,
        facts: Vec<Fact>,
        defs: Vec<Fact>,
        keyword: Range,
    },
    Steps {
        level: i64,
        steps: Vec<ProofStep>,
    },
}

#[derive(Clone, Debug)]
pub struct Proof {
    pub kind: ProofKind,
    pub location: Location,
}

#[derive(Clone, Debug)]
pub enum DefinitionUnit {
    Definition(Rc<Definition>),
    Instance(Rc<Instance>),
}

#[derive(Clone, Debug)]
pub enum StepBody {
    UseOrHide(UseOrHide),
    Instance(Rc<Instance>),
    Define {
        definitions: Vec<DefinitionUnit>,
        location: Location,
    },
    Have(Expr),
    Take {
        names: Vec<Name>,
        name_ranges: Vec<Range>,
        bounds: Vec<Bound>,
    },
    Witness(Vec<Expr>),
    Pick {
        names: Vec<Name>,
        name_ranges: Vec<Range>,
        bounds: Vec<Bound>,
        body: Expr,
    },
    Case(Expr),
    Assert {
        is_suffices: bool,
        statement: Statement,
    },
    Qed,
}

/// `head` is the range of the step number and its statement, without the proof, and `statement`
/// is the range of the statement alone.
#[derive(Clone, Debug)]
pub struct ProofStep {
    pub name: Option<Name>,
    pub token: Name,
    pub body: StepBody,
    pub head: Range,
    pub statement: Range,
    pub proof: Option<Box<Proof>>,
    pub location: Location,
}

#[derive(Clone, Debug)]
pub struct Theorem {
    pub name: Option<Name>,
    pub statement: Statement,
    pub proof: Option<Proof>,
    pub location: Location,
}

/// `Constants` and `Variables` keep the location of their keyword.
#[derive(Clone, Debug)]
pub enum ModuleUnit {
    Constants {
        declarations: Vec<Rc<Declaration>>,
        location: Location,
    },
    Variables {
        declarations: Vec<Rc<Declaration>>,
        location: Location,
    },
    Recursive(Vec<Rc<Declaration>>),
    Definition(Rc<Definition>),
    Instance(Rc<Instance>),
    Assumption(Rc<Assumption>),
    Theorem(Rc<Theorem>),
    Use(Rc<UseOrHide>),
    Module(Rc<Module>),
}

#[derive(Clone, Debug)]
pub struct Module {
    pub name: Name,
    pub modules: Vec<Rc<Module>>,
    pub extends: Vec<Name>,
    pub extends_ranges: Vec<Range>,
    pub constants: Vec<Rc<Declaration>>,
    pub variables: Vec<Rc<Declaration>>,
    pub definitions: Vec<Rc<Definition>>,
    pub instances: Vec<Rc<Instance>>,
    pub assumptions: Vec<Rc<Assumption>>,
    pub location: Location,
    pub theorems: Vec<Rc<Theorem>>,
    pub uses: Vec<Rc<UseOrHide>>,
    pub units: Vec<ModuleUnit>,
    /// Whether a LET of the module declares RECURSIVE an operator it doesn't define, whose errors
    /// SANY reports at the LET's level, which the front end doesn't follow.
    pub has_undefined_let_recursive: bool,
}

impl Expression {
    /// `getChildren`: the expressions a node holds, in the order `ast.ts` lists them.
    pub fn children(&self) -> Vec<Expr> {
        match &self.kind {
            ExpressionKind::Number { .. }
            | ExpressionKind::Decimal { .. }
            | ExpressionKind::String { .. }
            | ExpressionKind::Identifier { .. }
            | ExpressionKind::OperatorReference { .. }
            | ExpressionKind::ExceptAt => Vec::new(),
            ExpressionKind::Apply { args, .. } => args.clone(),
            ExpressionKind::Lambda { body, .. } => vec![body.clone()],
            ExpressionKind::Junction { operands, .. } => operands.clone(),
            ExpressionKind::Prime(inner)
            | ExpressionKind::Unchanged(inner)
            | ExpressionKind::Enabled(inner)
            | ExpressionKind::Always(inner)
            | ExpressionKind::Eventually(inner) => vec![inner.clone()],
            ExpressionKind::If {
                condition,
                consequent,
                alternative,
            } => vec![condition.clone(), consequent.clone(), alternative.clone()],
            ExpressionKind::Case { arms, other } => arms
                .iter()
                .flat_map(|arm| [arm.condition.clone(), arm.body.clone()])
                .chain(other.clone())
                .collect(),
            ExpressionKind::Let {
                definitions, body, ..
            } => definitions
                .iter()
                .flat_map(|definition| match &definition.kind {
                    DefinitionKind::Function { bounds } => bounds
                        .iter()
                        .map(|bound| bound.set.clone())
                        .chain([definition.body.clone()])
                        .collect(),
                    DefinitionKind::Operator { .. } => vec![definition.body.clone()],
                })
                .chain([body.clone()])
                .collect(),
            ExpressionKind::Quantified { bounds, body, .. }
            | ExpressionKind::FunctionConstruction { bounds, body } => bounds
                .iter()
                .map(|bound| bound.set.clone())
                .chain([body.clone()])
                .collect(),
            ExpressionKind::UnboundedQuantifier { body, .. } => vec![body.clone()],
            ExpressionKind::Choose { set, body, .. } => {
                set.iter().cloned().chain([body.clone()]).collect()
            }
            ExpressionKind::SetEnumeration(elements) | ExpressionKind::Tuple(elements) => {
                elements.clone()
            }
            ExpressionKind::SetFilter { bound, predicate } => {
                vec![bound.set.clone(), predicate.clone()]
            }
            ExpressionKind::SetMap { expression, bounds } => [expression.clone()]
                .into_iter()
                .chain(bounds.iter().map(|bound| bound.set.clone()))
                .collect(),
            ExpressionKind::FunctionSet { domain, range } => vec![domain.clone(), range.clone()],
            ExpressionKind::Record { fields, .. } => {
                fields.iter().map(|field| field.value.clone()).collect()
            }
            ExpressionKind::Except { function, updates } => [function.clone()]
                .into_iter()
                .chain(updates.iter().flat_map(|update| {
                    update
                        .path
                        .iter()
                        .flat_map(|step| match step {
                            ExceptPathStep::Index(args) => args.clone(),
                            ExceptPathStep::Field(_) => Vec::new(),
                        })
                        .chain([update.value.clone()])
                        .collect::<Vec<_>>()
                }))
                .collect(),
            ExpressionKind::FunctionApplication { function, args } => [function.clone()]
                .into_iter()
                .chain(args.iter().cloned())
                .collect(),
            ExpressionKind::Bracket(args) => args.clone(),
            ExpressionKind::FieldAccess { record, .. } => vec![record.clone()],
            ExpressionKind::Product(factors) => factors.clone(),
            ExpressionKind::Action {
                action, subscript, ..
            } => vec![action.clone(), subscript.clone()],
            ExpressionKind::Fairness {
                subscript, action, ..
            } => vec![subscript.clone(), action.clone()],
            ExpressionKind::Label { body, .. } => vec![body.clone()],
            ExpressionKind::Subexpression { selectors, .. } => selectors
                .iter()
                .flat_map(|selector| selector.args().to_vec())
                .collect(),
        }
    }
}
