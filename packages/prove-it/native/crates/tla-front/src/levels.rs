//! SANY's level checks on the AST, as `src/levels.ts` and `src/substitution-levels.ts` make them:
//! the levels, weights and Leibniz flags SANY computes for each operator, and the level errors it
//! reports for a module's units and for the substitutions of its instances.

use std::cell::RefCell;
use std::rc::Rc;

use crate::ast::*;
use crate::errors::{FrontError, SanyError, SyntaxError, format_range};
use crate::hash::{FastMap, FastSet};
use crate::instances::map_children;
use crate::ordered_map::OrderedMap;
use crate::resolve::{SemanticUnit, Tables, get_bound_names, get_pattern_names};

type Result<T> = std::result::Result<T, FrontError>;

// The levels of tla2sany.semantic.LevelConstants.
pub const CONSTANT_LEVEL: u8 = 0;
pub const VARIABLE_LEVEL: u8 = 1;
pub const ACTION_LEVEL: u8 = 2;
pub const TEMPORAL_LEVEL: u8 = 3;

/// An argument of an operator: the operator's name and the argument's index.
type ArgumentKey = (Name, usize);
/// A parameter that occurs in an argument of an operator.
type ArgumentParamKey = (Name, usize, Name);

/// A set that keeps the order of its insertions, as a JavaScript `Set` does.
type OrderedSet<T> = OrderedMap<T, ()>;

#[derive(Clone, Default, Debug)]
pub struct LevelData {
    pub level: u8,
    params: OrderedSet<Name>,
    constraints: OrderedMap<Name, u8>,
    arg_constraints: OrderedMap<ArgumentKey, u8>,
    arg_params: OrderedSet<ArgumentParamKey>,
}

impl LevelData {
    /// Whether the level depends on the parameters of an operator, `levelParams` in SANY.
    pub fn has_params(&self) -> bool {
        !self.params.is_empty()
    }

    fn new(level: u8) -> LevelData {
        LevelData {
            level,
            ..LevelData::default()
        }
    }
}

/// `SetOfLevelConstraints.put` keeps the lowest bound.
fn put_constraint(constraints: &mut OrderedMap<Name, u8>, name: &Name, level: u8) {
    let current = constraints.get(name).copied().unwrap_or(TEMPORAL_LEVEL);
    constraints.insert(name.clone(), level.min(current));
}

/// `SetOfArgLevelConstraints.put` keeps the highest bound.
fn put_arg_constraint(constraints: &mut OrderedMap<ArgumentKey, u8>, key: &ArgumentKey, level: u8) {
    let current = constraints.get(key).copied().unwrap_or(0);
    constraints.insert(key.clone(), level.max(current));
}

fn add<T: Clone + Eq + std::hash::Hash>(set: &mut OrderedSet<T>, item: &T) {
    if !set.contains_key(item) {
        set.insert(item.clone(), ());
    }
}

#[derive(Clone, Debug)]
pub struct Formal {
    name: Name,
    arity: usize,
}

/// What SANY computes for an operator besides the level data of its body.
#[derive(Clone, Debug)]
pub struct OperatorLevels {
    pub data: LevelData,
    name: Name,
    formals: Vec<Formal>,
    max_levels: Vec<u8>,
    weights: Vec<u8>,
    min_max_levels: Vec<Vec<u8>>,
    conditions: FastSet<(usize, usize, usize)>,
    non_leibniz: FastSet<usize>,
}

fn create_signature(name: &str, level: u8, max_levels: &[u8], weights: &[u8]) -> OperatorLevels {
    OperatorLevels {
        data: LevelData::new(level),
        name: Rc::from(name),
        formals: Vec::new(),
        max_levels: max_levels.to_vec(),
        weights: weights.to_vec(),
        min_max_levels: Vec::new(),
        conditions: FastSet::default(),
        non_leibniz: FastSet::default(),
    }
}

fn get_max_level(operator: &OperatorLevels, index: usize) -> u8 {
    if operator.formals.is_empty() && !operator.max_levels.is_empty() {
        operator.max_levels[index.min(operator.max_levels.len() - 1)]
    } else {
        operator
            .max_levels
            .get(index)
            .copied()
            .unwrap_or(TEMPORAL_LEVEL)
    }
}

fn get_weight(operator: &OperatorLevels, index: usize) -> u8 {
    if operator.formals.is_empty() && !operator.weights.is_empty() {
        operator.weights[index.min(operator.weights.len() - 1)]
    } else {
        operator.weights.get(index).copied().unwrap_or(1)
    }
}

/// `CORE_SIGNATURES`: name, level, maximum levels and weights of SANY's builtins.
const CORE_SIGNATURES: &[(&str, u8, &[u8], &[u8])] = &[
    ("=", 0, &[2, 2], &[1, 1]),
    ("#", 0, &[2, 2], &[1, 1]),
    ("\\in", 0, &[2, 2], &[1, 1]),
    ("\\notin", 0, &[2, 2], &[1, 1]),
    ("\\subseteq", 0, &[2, 2], &[1, 1]),
    ("\\cup", 0, &[2, 2], &[1, 1]),
    ("\\cap", 0, &[2, 2], &[1, 1]),
    ("\\", 0, &[2, 2], &[1, 1]),
    ("=>", 0, &[3, 3], &[1, 1]),
    ("<=>", 0, &[3, 3], &[1, 1]),
    ("/\\", 0, &[3, 3], &[1, 1]),
    ("\\/", 0, &[3, 3], &[1, 1]),
    ("~", 0, &[3], &[1]),
    ("SUBSET", 0, &[2], &[1]),
    ("UNION", 0, &[2], &[1]),
    ("DOMAIN", 0, &[2], &[1]),
    ("~>", 3, &[3, 3], &[0, 0]),
    ("-+->", 3, &[3, 3], &[0, 0]),
    ("\\cdot", 2, &[2, 2], &[0, 0]),
    ("TRUE", 0, &[], &[]),
    ("FALSE", 0, &[], &[]),
    ("BOOLEAN", 0, &[], &[]),
    ("STRING", 0, &[], &[]),
];

/// A signature of `STANDARD_LEVELS`: name, level, the arity of each parameter, maximum levels,
/// weights, the minimum maximum levels of each parameter's arguments, and the conditions.
type StandardSignature = (
    &'static str,
    u8,
    &'static [usize],
    &'static [u8],
    &'static [u8],
    &'static [(usize, usize, usize)],
);

/// `STANDARD_LEVELS`: SANY's view of the standard modules' dummy definitions of the operators
/// tla-ts implements natively.
const STANDARD_SIGNATURES: &[StandardSignature] = &[
    ("Nat", 0, &[], &[], &[], &[]),
    ("+", 0, &[0, 0], &[2, 2], &[1, 1], &[]),
    ("-", 0, &[0, 0], &[2, 2], &[1, 1], &[]),
    ("*", 0, &[0, 0], &[3, 3], &[0, 0], &[]),
    ("^", 0, &[0, 0], &[2, 2], &[1, 1], &[]),
    ("<", 0, &[0, 0], &[2, 2], &[1, 1], &[]),
    (">", 0, &[0, 0], &[2, 2], &[1, 1], &[]),
    ("<=", 0, &[0, 0], &[2, 2], &[1, 1], &[]),
    (">=", 0, &[0, 0], &[2, 2], &[1, 1], &[]),
    ("%", 0, &[0, 0], &[2, 2], &[1, 1], &[]),
    ("\\div", 0, &[0, 0], &[2, 2], &[1, 1], &[]),
    ("..", 0, &[0, 0], &[2, 2], &[1, 1], &[]),
    ("Int", 0, &[], &[], &[], &[]),
    ("-.", 0, &[0], &[2], &[1], &[]),
    ("Seq", 0, &[0], &[2], &[1], &[]),
    ("Len", 0, &[0], &[2], &[1], &[]),
    ("\\o", 0, &[0, 0], &[2, 2], &[1, 1], &[]),
    ("Append", 0, &[0, 0], &[2, 2], &[1, 1], &[]),
    ("Head", 0, &[0], &[2], &[1], &[]),
    ("Tail", 0, &[0], &[2], &[1], &[]),
    ("SubSeq", 0, &[0, 0, 0], &[2, 2, 2], &[1, 1, 1], &[]),
    ("SelectSeq", 0, &[0, 1], &[2, 2], &[1, 1], &[(1, 0, 0)]),
    ("IsFiniteSet", 0, &[0], &[2], &[1], &[]),
    ("Cardinality", 0, &[0], &[2], &[1], &[]),
    ("IsABag", 0, &[0], &[2], &[1], &[]),
    ("BagToSet", 0, &[0], &[2], &[1], &[]),
    ("SetToBag", 0, &[0], &[3], &[1], &[]),
    ("BagIn", 0, &[0, 0], &[2, 2], &[1, 1], &[]),
    ("EmptyBag", 0, &[], &[], &[], &[]),
    ("\\oplus", 0, &[0, 0], &[2, 2], &[1, 1], &[]),
    ("\\ominus", 0, &[0, 0], &[2, 2], &[1, 1], &[]),
    ("BagUnion", 0, &[0], &[2], &[1], &[]),
    ("\\sqsubseteq", 0, &[0, 0], &[2, 2], &[1, 1], &[]),
    ("SubBag", 0, &[0], &[2], &[1], &[]),
    ("BagOfAll", 0, &[1, 0], &[2, 2], &[1, 1], &[]),
    ("BagCardinality", 0, &[0], &[2], &[1], &[]),
    ("CopiesIn", 0, &[0, 0], &[2, 2], &[1, 1], &[]),
    ("Print", 0, &[0, 0], &[3, 3], &[0, 1], &[]),
    ("PrintT", 0, &[0], &[3], &[0], &[]),
    ("Assert", 0, &[0, 0], &[2, 3], &[1, 0], &[]),
    ("JavaTime", 0, &[], &[], &[], &[]),
    ("TLCGet", 0, &[0], &[3], &[0], &[]),
    ("TLCSet", 0, &[0, 0], &[3, 3], &[0, 0], &[]),
    (":>", 0, &[0, 0], &[2, 3], &[1, 1], &[]),
    ("@@", 0, &[0, 0], &[2, 2], &[1, 1], &[]),
    ("Permutations", 0, &[0], &[2], &[1], &[]),
    (
        "SortSeq",
        0,
        &[0, 2],
        &[2, 2],
        &[1, 1],
        &[(1, 0, 0), (1, 0, 1)],
    ),
    ("RandomElement", 0, &[0], &[3], &[1], &[]),
    ("Any", 0, &[], &[], &[], &[]),
    ("ToString", 0, &[0], &[2], &[1], &[]),
    ("TLCEval", 0, &[0], &[3], &[1], &[]),
    ("AssertEq", 0, &[0, 0], &[2, 2], &[1, 1], &[]),
    ("AssertError", 0, &[0, 0], &[2, 3], &[1, 0], &[]),
    ("TLCGetOrDefault", 0, &[0, 0], &[3, 3], &[0, 0], &[]),
    (
        "TLCGetAndSet",
        0,
        &[0, 2, 0, 0],
        &[3, 3, 3, 3],
        &[0, 0, 0, 0],
        &[(1, 2, 1)],
    ),
    ("Trace", 0, &[], &[], &[], &[]),
    ("CounterExample", 0, &[], &[], &[], &[]),
    ("ToTrace", 0, &[0], &[3], &[0], &[]),
    ("TLCModelValue", 0, &[0], &[2], &[1], &[]),
    ("TLCDefer", 0, &[0], &[3], &[0], &[]),
    ("TLCNoOp", 0, &[0], &[3], &[1], &[]),
    ("PickSuccessor", 0, &[0], &[3], &[1], &[]),
    ("TLCCache", 0, &[0, 0], &[3, 3], &[1, 0], &[]),
    ("TLCFP", 0, &[0], &[3], &[0], &[]),
    ("TLCEvalDefinition", 0, &[0], &[3], &[0], &[]),
    ("ToJson", 0, &[0], &[2], &[1], &[]),
    ("ToJsonArray", 0, &[0], &[2], &[1], &[]),
    ("ToJsonObject", 0, &[0], &[2], &[1], &[]),
    ("JsonSerialize", 0, &[0, 0], &[3, 3], &[0, 0], &[]),
    ("JsonDeserialize", 0, &[0], &[3], &[0], &[]),
    ("ndJsonSerialize", 0, &[0, 0], &[3, 3], &[0, 0], &[]),
    ("ndJsonDeserialize", 0, &[0], &[3], &[0], &[]),
    ("RandomSubset", 0, &[0, 0], &[2, 2], &[1, 1], &[]),
    (
        "RandomSetOfSubsets",
        0,
        &[0, 0, 0],
        &[2, 3, 2],
        &[1, 0, 1],
        &[],
    ),
    (
        "TestRandomSetOfSubsets",
        0,
        &[0, 0, 0],
        &[2, 3, 2],
        &[1, 0, 1],
        &[],
    ),
];

thread_local! {
    static SIGNATURES: FastMap<Name, Rc<OperatorLevels>> = {
        let core = CORE_SIGNATURES.iter().map(|(name, level, max_levels, weights)| {
            let mut signature = create_signature(name, *level, max_levels, weights);
            if *level > 1 {
                signature.non_leibniz = [0, 1].into_iter().collect();
            }
            signature
        });
        let standard = STANDARD_SIGNATURES.iter().map(
            |(name, level, arities, max_levels, weights, conditions)| OperatorLevels {
                data: LevelData::new(*level),
                name: Rc::from(*name),
                formals: arities
                    .iter()
                    .enumerate()
                    .map(|(index, arity)| Formal {
                        name: Rc::from(format!("${index}")),
                        arity: *arity,
                    })
                    .collect(),
                max_levels: max_levels.to_vec(),
                weights: weights.to_vec(),
                min_max_levels: Vec::new(),
                conditions: conditions.iter().copied().collect(),
                non_leibniz: FastSet::default(),
            },
        );
        // `CORE_SIGNATURES` wins over `STANDARD_LEVELS`.
        let mut signatures: FastMap<Name, Rc<OperatorLevels>> = FastMap::default();
        for signature in standard.chain(core) {
            signatures.insert(signature.name.clone(), Rc::new(signature));
        }
        signatures
    };
    static SET_LEVELS: Rc<OperatorLevels> = Rc::new(create_signature("$Set", 0, &[2], &[1]));
    static JUNCTION_LEVELS: Rc<OperatorLevels> =
        Rc::new(create_signature("$Junction", 0, &[3], &[1]));
    static CHOOSE_LEVELS: Rc<OperatorLevels> = Rc::new(create_signature("$Choose", 0, &[2], &[1]));
    static FUNCTION_LEVELS: Rc<OperatorLevels> =
        Rc::new(create_signature("$Function", 0, &[3], &[1]));
    static APPLY_LEVELS: Rc<OperatorLevels> =
        Rc::new(create_signature("$FcnApply", 0, &[2, 2], &[1, 1]));
    static SELECT_LEVELS: Rc<OperatorLevels> =
        Rc::new(create_signature("$RcdSelect", 0, &[2, 0], &[1, 1]));
    static PRIME_LEVELS: Rc<OperatorLevels> = Rc::new(create_signature("'", 2, &[1], &[0]));
    static ENABLED_LEVELS: Rc<OperatorLevels> = Rc::new(create_signature("ENABLED", 1, &[2], &[0]));
    static TEMPORAL_LEVELS: Rc<OperatorLevels> = Rc::new(create_signature("[]", 3, &[3], &[0]));
    static ACTION_LEVELS: Rc<OperatorLevels> =
        Rc::new(create_signature("$SquareAct", 2, &[2, 1], &[0, 0]));
    static FAIRNESS_LEVELS: Rc<OperatorLevels> =
        Rc::new(create_signature("$WF", 3, &[1, 2], &[0, 0]));
    static TEMPORAL_QUANTIFIER_LEVELS: Rc<OperatorLevels> =
        Rc::new(create_signature("$TemporalExists", 3, &[3], &[0]));
}

fn signature(key: &'static std::thread::LocalKey<Rc<OperatorLevels>>) -> Rc<OperatorLevels> {
    key.with(Rc::clone)
}

/// A name a scope binds: a formal parameter, or a LET definition, whose scope is the frame that
/// binds it.
#[derive(Clone)]
enum Entry {
    Formal(usize),
    Let(Rc<Definition>),
}

/// `Scope`: the names bound around an expression, nearest last.
#[derive(Clone, Default)]
pub struct Scope(Option<Rc<Frame>>);

struct Frame {
    entries: Vec<(Name, Entry)>,
    parent: Scope,
}

impl Scope {
    fn bind(&self, entries: Vec<(Name, Entry)>) -> Scope {
        if entries.is_empty() {
            return self.clone();
        }
        Scope(Some(Rc::new(Frame {
            entries,
            parent: self.clone(),
        })))
    }

    fn bind_formals(&self, formals: &[Formal]) -> Scope {
        self.bind(
            formals
                .iter()
                .map(|formal| (formal.name.clone(), Entry::Formal(formal.arity)))
                .collect(),
        )
    }

    fn bind_names(&self, names: &[Name]) -> Scope {
        self.bind(
            names
                .iter()
                .map(|name| (name.clone(), Entry::Formal(0)))
                .collect(),
        )
    }

    /// The entry of a name and the scope a LET definition is analyzed in.
    fn lookup(&self, name: &str) -> Option<(Entry, Scope)> {
        let mut current = self.clone();
        while let Some(frame) = current.0.clone() {
            if let Some((_, entry)) = frame
                .entries
                .iter()
                .rev()
                .find(|(bound, _)| &**bound == name)
            {
                return Some((entry.clone(), current));
            }
            current = frame.parent.clone();
        }
        None
    }
}

enum Resolved {
    Declared { name: Name, level: u8, arity: usize },
    Defined(Rc<OperatorLevels>),
}

struct Operand {
    own: LevelData,
    operator: Option<Rc<OperatorLevels>>,
    declared: Option<(Name, usize)>,
}

impl Operand {
    fn data(&self) -> &LevelData {
        self.operator
            .as_ref()
            .map_or(&self.own, |operator| &operator.data)
    }

    fn of(data: LevelData) -> Operand {
        Operand {
            own: data,
            operator: None,
            declared: None,
        }
    }
}

/// A level error before SANY places it at an expression, or an error SANY placed.
fn plain_error(message: String) -> FrontError {
    FrontError::Syntax(SyntaxError {
        message,
        failure: None,
        sany: None,
    })
}

/// `createLevelError`: SANY reports a level error at the range of the expression it rejects.
fn create_level_error(message: &str, expression: &Expression) -> FrontError {
    match &expression.location.range {
        Some(range) => FrontError::Syntax(SyntaxError::sany(vec![SanyError {
            location: format_range(range),
            message: format!("{message}."),
        }])),
        None => plain_error(format!(
            "{message} at line {}, column {}",
            expression.location.line, expression.location.column
        )),
    }
}

const LOGICAL_OPERATORS: &[&str] = &["/\\", "\\/", "=>", "<=>"];

/// SANY's OpApplNode.levelCheck rejects raw actions inside temporal formulas, but not inside a
/// LET or a label.
fn is_operator_application(expression: &Expression) -> bool {
    !matches!(
        expression.kind,
        ExpressionKind::Let { .. } | ExpressionKind::Label { .. }
    )
}

/// The definition a module names by a name or key.
pub type GetDefinition<'a> = Box<dyn Fn(&str) -> Option<Rc<Definition>> + 'a>;
/// The qualified name, such as I!Foo, of an instance's copy of a definition.
pub type GetQualifiedName<'a> = Box<dyn Fn(&str) -> Option<Name> + 'a>;

/// What the analyzer reads of the module whose expressions it analyzes.
pub struct LevelContext<'a> {
    pub constants: FastSet<Name>,
    pub variables: FastSet<Name>,
    pub get_definition: GetDefinition<'a>,
    pub get_qualified_name: GetQualifiedName<'a>,
}

/// `createLevelAnalyzer`.
pub struct LevelAnalyzer<'a> {
    context: LevelContext<'a>,
    tables: &'a Tables,
    definition_levels: RefCell<FastMap<usize, Rc<OperatorLevels>>>,
}

fn get_name(expression: &Expression) -> Name {
    expression.reference().unwrap_or_default()
}

impl<'a> LevelAnalyzer<'a> {
    pub fn new(context: LevelContext<'a>, tables: &'a Tables) -> LevelAnalyzer<'a> {
        LevelAnalyzer {
            context,
            tables,
            definition_levels: RefCell::default(),
        }
    }

    fn resolve(&self, name: &Name, scope: &Scope) -> Result<Resolved> {
        match scope.lookup(name) {
            Some((Entry::Formal(arity), _)) => {
                return Ok(Resolved::Declared {
                    name: name.clone(),
                    level: 0,
                    arity,
                });
            }
            Some((Entry::Let(definition), frame)) => {
                return Ok(Resolved::Defined(
                    self.analyze_definition(&definition, &frame)?,
                ));
            }
            None => {}
        }
        if self.context.constants.contains(name) {
            return Ok(Resolved::Declared {
                name: name.clone(),
                level: 0,
                arity: 0,
            });
        }
        if self.context.variables.contains(name) {
            return Ok(Resolved::Declared {
                name: name.clone(),
                level: 1,
                arity: 0,
            });
        }
        if let Some(definition) = (self.context.get_definition)(name) {
            let levels = self.analyze_definition(&definition, &Scope::default())?;
            // SANY names a definition of an instance by its qualified name, as in I!Foo.
            return Ok(Resolved::Defined(
                match (self.context.get_qualified_name)(name) {
                    Some(qualified) => Rc::new(OperatorLevels {
                        name: qualified,
                        ..(*levels).clone()
                    }),
                    None => levels,
                },
            ));
        }
        if let Some(signature) = SIGNATURES.with(|signatures| signatures.get(name).cloned()) {
            return Ok(Resolved::Defined(signature));
        }
        Ok(Resolved::Declared {
            name: name.clone(),
            level: 0,
            arity: 0,
        })
    }

    fn apply_declared(&self, name: &Name, level: u8, operands: &[Operand]) -> LevelData {
        let mut data = LevelData::new(
            operands
                .iter()
                .map(|operand| operand.data().level)
                .fold(level, u8::max),
        );
        add(&mut data.params, name);
        for (index, operand) in operands.iter().enumerate() {
            let operand_data = operand.data();
            for param in operand_data.params.keys() {
                add(&mut data.params, param);
                add(&mut data.arg_params, &(name.clone(), index, param.clone()));
            }
            for (key, value) in operand_data.constraints.iter() {
                put_constraint(&mut data.constraints, key, *value);
            }
            put_arg_constraint(
                &mut data.arg_constraints,
                &(name.clone(), index),
                operand_data.level,
            );
            for (key, value) in operand_data.arg_constraints.iter() {
                put_arg_constraint(&mut data.arg_constraints, key, *value);
            }
            for key in operand_data.arg_params.keys() {
                add(&mut data.arg_params, key);
            }
        }
        data
    }

    fn apply_defined(
        &self,
        operator: &OperatorLevels,
        operands: &[Operand],
        ranges: &[LevelData],
        bound: &[Name],
    ) -> Result<LevelData> {
        let is_bound = |name: &Name| bound.contains(name);
        for (index, operand) in operands.iter().enumerate() {
            if operand.operator.is_some() || operand.declared.is_some() {
                continue;
            }
            if operand.data().level > get_max_level(operator, index) {
                return Err(plain_error(format!(
                    "Level error in applying operator {}:\nThe level of argument {} exceeds the maximum level allowed by the operator",
                    operator.name,
                    index + 1
                )));
            }
        }
        if ranges.iter().any(|range| range.level > ACTION_LEVEL) {
            return Err(plain_error(format!(
                "Level error in applying operator {}:\nThe level of the range for a bounded variable exceeds the maximum level allowed by the operator",
                operator.name
            )));
        }
        let get_operand = |formal: &Name| {
            operator
                .formals
                .iter()
                .position(|param| param.name == *formal)
                .and_then(|index| operands.get(index))
        };
        let has_condition = |operand: usize, other: usize, argument: usize| {
            operator.conditions.contains(&(operand, other, argument))
        };
        let level = operands
            .iter()
            .enumerate()
            .filter(|(index, _)| get_weight(operator, *index) == 1)
            .map(|(_, operand)| operand.data().level)
            .chain(ranges.iter().map(|range| range.level))
            .fold(operator.data.level, u8::max);
        let mut data = LevelData::new(level);
        for param in operator.data.params.keys() {
            add(&mut data.params, param);
        }
        for (index, operand) in operands.iter().enumerate() {
            if get_weight(operator, index) == 1 {
                for param in operand.data().params.keys() {
                    add(&mut data.params, param);
                }
            }
        }
        for range in ranges {
            for param in range.params.keys() {
                add(&mut data.params, param);
            }
        }
        for name in bound {
            data.params.remove(name);
        }

        for (key, value) in operator.data.constraints.iter() {
            put_constraint(&mut data.constraints, key, *value);
        }
        for operand in operands {
            for (key, value) in operand.data().constraints.iter() {
                if !is_bound(key) {
                    put_constraint(&mut data.constraints, key, *value);
                }
            }
        }
        for range in ranges {
            for (key, value) in range.constraints.iter() {
                put_constraint(&mut data.constraints, key, *value);
            }
        }
        for (index, operand) in operands.iter().enumerate() {
            for param in operand.data().params.keys() {
                if !is_bound(param) {
                    put_constraint(&mut data.constraints, param, get_max_level(operator, index));
                }
            }
        }
        for (operand_index, operand) in operands.iter().enumerate() {
            let Some(argument) = &operand.operator else {
                continue;
            };
            for (other_index, other) in operands.iter().enumerate() {
                for argument_index in 0..argument.formals.len() {
                    if !has_condition(operand_index, other_index, argument_index) {
                        continue;
                    }
                    for param in other.data().params.keys() {
                        put_constraint(
                            &mut data.constraints,
                            param,
                            get_max_level(argument, argument_index),
                        );
                    }
                }
            }
        }
        for (formal, index, param) in operator.data.arg_params.keys() {
            if let Some(argument) =
                get_operand(formal).and_then(|operand| operand.operator.as_ref())
            {
                put_constraint(
                    &mut data.constraints,
                    param,
                    get_max_level(argument, *index),
                );
            }
        }

        let arg_constraints = std::iter::once(&operator.data.arg_constraints)
            .chain(
                operands
                    .iter()
                    .map(|operand| &operand.data().arg_constraints),
            )
            .chain(ranges.iter().map(|range| &range.arg_constraints));
        for constraints in arg_constraints {
            for (key, value) in constraints.iter() {
                put_arg_constraint(&mut data.arg_constraints, key, *value);
            }
        }
        for (operand_index, operand) in operands.iter().enumerate() {
            let Some((name, arity)) = &operand.declared else {
                continue;
            };
            for argument_index in 0..*arity {
                put_arg_constraint(
                    &mut data.arg_constraints,
                    &(name.clone(), argument_index),
                    operator
                        .min_max_levels
                        .get(operand_index)
                        .and_then(|levels| levels.get(argument_index))
                        .copied()
                        .unwrap_or(0),
                );
            }
            for (other_index, other) in operands.iter().enumerate() {
                for argument_index in 0..*arity {
                    if has_condition(operand_index, other_index, argument_index) {
                        put_arg_constraint(
                            &mut data.arg_constraints,
                            &(name.clone(), argument_index),
                            other.data().level,
                        );
                    }
                }
            }
        }
        for (formal, index, _) in operator.data.arg_params.keys() {
            if let Some(argument) = get_operand(formal) {
                put_arg_constraint(
                    &mut data.arg_constraints,
                    &(formal.clone(), *index),
                    argument.data().level,
                );
            }
        }

        for operand in operands {
            for key in operand.data().arg_params.keys() {
                if !is_bound(&key.2) {
                    add(&mut data.arg_params, key);
                }
            }
        }
        for range in ranges {
            for key in range.arg_params.keys() {
                add(&mut data.arg_params, key);
            }
        }
        for key in operator.data.arg_params.keys() {
            let (formal, index, param) = key;
            match get_operand(formal) {
                None => match get_operand(param) {
                    None => add(&mut data.arg_params, key),
                    Some(value) => {
                        for value_param in value.data().params.keys() {
                            add(
                                &mut data.arg_params,
                                &(formal.clone(), *index, value_param.clone()),
                            );
                        }
                    }
                },
                Some(argument) => {
                    if let Some((name, _)) = &argument.declared {
                        add(&mut data.arg_params, &(name.clone(), *index, param.clone()));
                    }
                }
            }
        }
        for (operand_index, operand) in operands.iter().enumerate() {
            let Some((name, arity)) = &operand.declared else {
                continue;
            };
            for (other_index, other) in operands.iter().enumerate() {
                for argument_index in 0..*arity {
                    if !has_condition(operand_index, other_index, argument_index) {
                        continue;
                    }
                    for param in other.data().params.keys() {
                        add(
                            &mut data.arg_params,
                            &(name.clone(), argument_index, param.clone()),
                        );
                    }
                }
            }
        }
        Ok(data)
    }

    fn to_operand(&self, expression: &Expr, scope: &Scope) -> Result<Operand> {
        if let ExpressionKind::Lambda { params, body, .. } = &expression.kind {
            let formals: Vec<Formal> = params
                .iter()
                .map(|name| Formal {
                    name: name.clone(),
                    arity: 0,
                })
                .collect();
            let operator =
                Rc::new(self.analyze_operator(&Rc::from("LAMBDA"), formals, body, scope)?);
            return Ok(Operand {
                own: LevelData::default(),
                operator: Some(operator),
                declared: None,
            });
        }
        let is_reference = matches!(expression.kind, ExpressionKind::OperatorReference { .. });
        if is_reference || matches!(expression.kind, ExpressionKind::Identifier { .. }) {
            let name = get_name(expression);
            match self.resolve(&name, scope)? {
                Resolved::Defined(levels) if !levels.formals.is_empty() || is_reference => {
                    return Ok(Operand {
                        own: LevelData::default(),
                        operator: Some(levels),
                        declared: None,
                    });
                }
                Resolved::Declared { arity, .. } if arity > 0 => {
                    let mut data = LevelData::default();
                    add(&mut data.params, &name);
                    return Ok(Operand {
                        own: data,
                        operator: None,
                        declared: Some((name, arity)),
                    });
                }
                _ => {}
            }
        }
        Ok(Operand::of(self.analyze(expression, scope)?))
    }

    fn to_operands(&self, expressions: &[Expr], scope: &Scope) -> Result<Vec<Operand>> {
        expressions
            .iter()
            .map(|expression| self.to_operand(expression, scope))
            .collect()
    }

    fn apply_builtin(
        &self,
        operator: &OperatorLevels,
        expressions: &[Expr],
        scope: &Scope,
        ranges: &[Expr],
        bound: &[Name],
    ) -> Result<LevelData> {
        let inner = scope.bind_names(bound);
        let operands = self.to_operands(expressions, &inner)?;
        let ranges = ranges
            .iter()
            .map(|range| self.analyze(range, scope))
            .collect::<Result<Vec<_>>>()?;
        self.apply_defined(operator, &operands, &ranges, bound)
    }

    fn apply_resolved(&self, resolved: Resolved, operands: &[Operand]) -> Result<LevelData> {
        match resolved {
            Resolved::Declared { name, level, .. } => {
                Ok(self.apply_declared(&name, level, operands))
            }
            Resolved::Defined(levels) => self.apply_defined(&levels, operands, &[], &[]),
        }
    }

    fn check_junction(operands: &[Operand], expression: &Expression) -> Result<()> {
        let levels: Vec<u8> = operands
            .iter()
            .map(|operand| operand.data().level)
            .collect();
        if levels.contains(&ACTION_LEVEL) && levels.contains(&TEMPORAL_LEVEL) {
            return Err(create_level_error(
                "Formula has both temporal formula and action as arguments",
                expression,
            ));
        }
        Ok(())
    }

    fn analyze_let(
        &self,
        definitions: &[Rc<Definition>],
        body: &Expr,
        scope: &Scope,
    ) -> Result<LevelData> {
        let inner = scope.bind(
            definitions
                .iter()
                .map(|definition| (definition.name.clone(), Entry::Let(definition.clone())))
                .collect(),
        );
        let mut data = self.analyze(body, &inner)?;
        for definition in definitions {
            let levels = self.analyze_definition(definition, &inner)?;
            for (key, value) in levels.data.constraints.iter() {
                put_constraint(&mut data.constraints, key, *value);
            }
            for (key, value) in levels.data.arg_constraints.iter() {
                put_arg_constraint(&mut data.arg_constraints, key, *value);
            }
            for key in levels.data.arg_params.keys() {
                add(&mut data.arg_params, key);
            }
        }
        Ok(data)
    }

    /// SANY reports a level error of an operator's arguments at the application.
    pub fn analyze(&self, expression: &Expr, scope: &Scope) -> Result<LevelData> {
        match self.analyze_node(expression, scope) {
            Err(FrontError::Syntax(error)) if error.sany.is_none() => {
                Err(create_level_error(&error.message, expression))
            }
            result => result,
        }
    }

    fn analyze_node(&self, expression: &Expr, scope: &Scope) -> Result<LevelData> {
        let empty: &[Name] = &[];
        match &expression.kind {
            ExpressionKind::Number { .. }
            | ExpressionKind::Decimal { .. }
            | ExpressionKind::String { .. }
            | ExpressionKind::ExceptAt
            | ExpressionKind::Bracket(_)
            | ExpressionKind::Subexpression { .. } => Ok(LevelData::default()),
            ExpressionKind::Identifier { .. } => {
                self.apply_resolved(self.resolve(&get_name(expression), scope)?, &[])
            }
            ExpressionKind::Apply { args, .. } => {
                let operands = self.to_operands(args, scope)?;
                let operator = get_name(expression);
                let is_leads_to = &*operator == "~>" || &*operator == "-+->";
                if is_leads_to
                    && operands
                        .iter()
                        .any(|operand| operand.data().level == ACTION_LEVEL)
                {
                    return Err(create_level_error(
                        "Action used where only temporal formula or state predicate allowed",
                        expression,
                    ));
                }
                if LOGICAL_OPERATORS.contains(&&*operator) {
                    Self::check_junction(&operands, expression)?;
                }
                self.apply_resolved(self.resolve(&operator, scope)?, &operands)
            }
            ExpressionKind::OperatorReference { .. } | ExpressionKind::Lambda { .. } => {
                Ok(self.to_operand(expression, scope)?.data().clone())
            }
            ExpressionKind::Junction { operands, .. } => {
                let operands = self.to_operands(operands, scope)?;
                Self::check_junction(&operands, expression)?;
                self.apply_defined(&signature(&JUNCTION_LEVELS), &operands, &[], &[])
            }
            ExpressionKind::Prime(inner) | ExpressionKind::Unchanged(inner) => self.apply_builtin(
                &signature(&PRIME_LEVELS),
                std::slice::from_ref(inner),
                scope,
                &[],
                empty,
            ),
            ExpressionKind::Enabled(inner) => self.apply_builtin(
                &signature(&ENABLED_LEVELS),
                std::slice::from_ref(inner),
                scope,
                &[],
                empty,
            ),
            ExpressionKind::Always(inner) | ExpressionKind::Eventually(inner) => {
                let operand = self.to_operand(inner, scope)?;
                let is_always = matches!(expression.kind, ExpressionKind::Always(_));
                let is_form = matches!(
                    inner.kind,
                    ExpressionKind::Action { is_box, .. } if is_box == is_always
                );
                if operand.data().level == ACTION_LEVEL
                    && is_operator_application(inner)
                    && !is_form
                {
                    return Err(create_level_error(
                        if is_always {
                            "[] followed by action not of form [A]_v"
                        } else {
                            "<> followed by action not of form <<A>>_v"
                        },
                        expression,
                    ));
                }
                self.apply_defined(&signature(&TEMPORAL_LEVELS), &[operand], &[], &[])
            }
            ExpressionKind::If {
                condition,
                consequent,
                alternative,
            } => self.apply_builtin(
                &signature(&JUNCTION_LEVELS),
                &[condition.clone(), consequent.clone(), alternative.clone()],
                scope,
                &[],
                empty,
            ),
            ExpressionKind::Case { arms, other } => {
                let parts: Vec<Expr> = arms
                    .iter()
                    .flat_map(|arm| [arm.condition.clone(), arm.body.clone()])
                    .chain(other.clone())
                    .collect();
                self.apply_builtin(&signature(&JUNCTION_LEVELS), &parts, scope, &[], empty)
            }
            ExpressionKind::Let {
                definitions, body, ..
            } => self.analyze_let(definitions, body, scope),
            ExpressionKind::Quantified { bounds, body, .. } => {
                let sets: Vec<Expr> = bounds.iter().map(|bound| bound.set.clone()).collect();
                let data = self.apply_builtin(
                    &signature(&JUNCTION_LEVELS),
                    std::slice::from_ref(body),
                    scope,
                    &sets,
                    &get_bound_names(bounds),
                )?;
                if data.level == TEMPORAL_LEVEL {
                    for bound in bounds {
                        if self.analyze(&bound.set, scope)?.level == ACTION_LEVEL {
                            return Err(create_level_error(
                                "Action-level bound of quantified temporal formula",
                                &bound.set,
                            ));
                        }
                    }
                }
                Ok(data)
            }
            ExpressionKind::UnboundedQuantifier {
                names,
                is_temporal,
                body,
                ..
            } => self.apply_builtin(
                &signature(if *is_temporal {
                    &TEMPORAL_QUANTIFIER_LEVELS
                } else {
                    &JUNCTION_LEVELS
                }),
                std::slice::from_ref(body),
                scope,
                &[],
                names,
            ),
            ExpressionKind::Choose { pattern, set, body } => self.apply_builtin(
                &signature(&CHOOSE_LEVELS),
                std::slice::from_ref(body),
                scope,
                &set.iter().cloned().collect::<Vec<_>>(),
                &get_pattern_names(pattern),
            ),
            ExpressionKind::SetEnumeration(elements)
            | ExpressionKind::Tuple(elements)
            | ExpressionKind::Product(elements) => {
                self.apply_builtin(&signature(&SET_LEVELS), elements, scope, &[], empty)
            }
            ExpressionKind::FunctionSet { domain, range } => self.apply_builtin(
                &signature(&SET_LEVELS),
                &[domain.clone(), range.clone()],
                scope,
                &[],
                empty,
            ),
            ExpressionKind::SetFilter { bound, predicate } => self.apply_builtin(
                &signature(&SET_LEVELS),
                std::slice::from_ref(predicate),
                scope,
                std::slice::from_ref(&bound.set),
                &get_pattern_names(&bound.pattern),
            ),
            ExpressionKind::SetMap {
                expression: mapped,
                bounds,
            } => self.apply_builtin(
                &signature(&SET_LEVELS),
                std::slice::from_ref(mapped),
                scope,
                &bounds
                    .iter()
                    .map(|bound| bound.set.clone())
                    .collect::<Vec<_>>(),
                &get_bound_names(bounds),
            ),
            ExpressionKind::FunctionConstruction { bounds, body } => self.apply_builtin(
                &signature(&FUNCTION_LEVELS),
                std::slice::from_ref(body),
                scope,
                &bounds
                    .iter()
                    .map(|bound| bound.set.clone())
                    .collect::<Vec<_>>(),
                &get_bound_names(bounds),
            ),
            ExpressionKind::Record { is_set, fields } => self.apply_builtin(
                &signature(if *is_set {
                    &SET_LEVELS
                } else {
                    &FUNCTION_LEVELS
                }),
                &fields
                    .iter()
                    .map(|field| field.value.clone())
                    .collect::<Vec<_>>(),
                scope,
                &[],
                empty,
            ),
            ExpressionKind::Except { function, updates } => {
                let parts: Vec<Expr> = std::iter::once(function.clone())
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
                    .collect();
                self.apply_builtin(&signature(&SET_LEVELS), &parts, scope, &[], empty)
            }
            ExpressionKind::FunctionApplication { function, args } => {
                let argument = if args.len() == 1 {
                    self.to_operand(&args[0], scope)?
                } else {
                    Operand::of(self.apply_builtin(
                        &signature(&SET_LEVELS),
                        args,
                        scope,
                        &[],
                        empty,
                    )?)
                };
                self.apply_defined(
                    &signature(&APPLY_LEVELS),
                    &[self.to_operand(function, scope)?, argument],
                    &[],
                    &[],
                )
            }
            ExpressionKind::FieldAccess { record, .. } => self.apply_defined(
                &signature(&SELECT_LEVELS),
                &[
                    self.to_operand(record, scope)?,
                    Operand::of(LevelData::default()),
                ],
                &[],
                &[],
            ),
            ExpressionKind::Action {
                action, subscript, ..
            } => self.apply_builtin(
                &signature(&ACTION_LEVELS),
                &[action.clone(), subscript.clone()],
                scope,
                &[],
                empty,
            ),
            ExpressionKind::Fairness {
                subscript, action, ..
            } => self.apply_builtin(
                &signature(&FAIRNESS_LEVELS),
                &[subscript.clone(), action.clone()],
                scope,
                &[],
                empty,
            ),
            ExpressionKind::Label { body, .. } => self.analyze(body, scope),
        }
    }

    fn collect_non_leibniz_names(
        &self,
        expression: &Expr,
        scope: &Scope,
        is_non_leibniz: bool,
        names: &mut FastSet<Name>,
    ) -> Result<()> {
        let visit_operator =
            |name: &Name, args: &[Expr], names: &mut FastSet<Name>| -> Result<()> {
                match self.resolve(name, scope)? {
                    Resolved::Declared { .. } => {
                        if is_non_leibniz {
                            names.insert(name.clone());
                        }
                        for arg in args {
                            self.collect_non_leibniz_names(arg, scope, is_non_leibniz, names)?;
                        }
                    }
                    Resolved::Defined(levels) => {
                        for (index, arg) in args.iter().enumerate() {
                            self.collect_non_leibniz_names(
                                arg,
                                scope,
                                is_non_leibniz || levels.non_leibniz.contains(&index),
                                names,
                            )?;
                        }
                    }
                }
                Ok(())
            };
        match &expression.kind {
            ExpressionKind::Identifier { .. } => visit_operator(&get_name(expression), &[], names),
            ExpressionKind::Apply { args, .. } => {
                visit_operator(&get_name(expression), args, names)
            }
            // SANY's LetInNode and OpArgNode don't carry the non-Leibniz parameters of their
            // bodies.
            ExpressionKind::Lambda { .. } | ExpressionKind::Let { .. } => Ok(()),
            ExpressionKind::Prime(_)
            | ExpressionKind::Unchanged(_)
            | ExpressionKind::Enabled(_)
            | ExpressionKind::Always(_)
            | ExpressionKind::Eventually(_)
            | ExpressionKind::Action { .. }
            | ExpressionKind::Fairness { .. } => {
                for child in expression.children() {
                    self.collect_non_leibniz_names(&child, scope, true, names)?;
                }
                Ok(())
            }
            ExpressionKind::UnboundedQuantifier {
                names: bound,
                is_temporal,
                body,
                ..
            } => self.collect_non_leibniz_names(
                body,
                &scope.bind_names(bound),
                is_non_leibniz || *is_temporal,
                names,
            ),
            _ => {
                let mut result = Ok(());
                map_children(expression, self.tables, &mut |child, bound| {
                    if result.is_ok() {
                        result = self.collect_non_leibniz_names(
                            child,
                            &scope.bind_names(bound),
                            is_non_leibniz,
                            names,
                        );
                    }
                    Ok(child.clone())
                })?;
                result
            }
        }
    }

    fn analyze_operator(
        &self,
        name: &Name,
        formals: Vec<Formal>,
        body: &Expr,
        scope: &Scope,
    ) -> Result<OperatorLevels> {
        let inner = scope.bind_formals(&formals);
        let data = self.analyze(body, &inner)?;
        let is_formal = |param: &Name| formals.iter().any(|formal| formal.name == *param);
        let mut non_leibniz_names = FastSet::default();
        self.collect_non_leibniz_names(body, &inner, false, &mut non_leibniz_names)?;
        let mut conditions = FastSet::default();
        for (operator_index, operator) in formals.iter().enumerate() {
            for (param_index, param) in formals.iter().enumerate() {
                for argument_index in 0..operator.arity {
                    let key = (operator.name.clone(), argument_index, param.name.clone());
                    if data.arg_params.contains_key(&key) {
                        conditions.insert((operator_index, param_index, argument_index));
                    }
                }
            }
        }
        let mut levels = OperatorLevels {
            data: LevelData::new(data.level),
            name: name.clone(),
            non_leibniz: formals
                .iter()
                .enumerate()
                .filter(|(_, formal)| non_leibniz_names.contains(&formal.name))
                .map(|(index, _)| index)
                .collect(),
            max_levels: formals
                .iter()
                .map(|formal| {
                    data.constraints
                        .get(&formal.name)
                        .copied()
                        .unwrap_or(TEMPORAL_LEVEL)
                        .min(TEMPORAL_LEVEL)
                })
                .collect(),
            weights: formals
                .iter()
                .map(|formal| u8::from(data.params.contains_key(&formal.name)))
                .collect(),
            min_max_levels: formals
                .iter()
                .map(|formal| {
                    (0..formal.arity)
                        .map(|index| {
                            data.arg_constraints
                                .get(&(formal.name.clone(), index))
                                .copied()
                                .unwrap_or(0)
                        })
                        .collect()
                })
                .collect(),
            conditions,
            formals: Vec::new(),
        };
        for param in data.params.keys() {
            if !is_formal(param) {
                add(&mut levels.data.params, param);
            }
        }
        for (key, value) in data.constraints.iter() {
            if !is_formal(key) {
                levels.data.constraints.insert(key.clone(), *value);
            }
        }
        for (key, value) in data.arg_constraints.iter() {
            if !is_formal(&key.0) {
                levels.data.arg_constraints.insert(key.clone(), *value);
            }
        }
        for key in data.arg_params.keys() {
            if !is_formal(&key.0) || !is_formal(&key.2) {
                add(&mut levels.data.arg_params, key);
            }
        }
        levels.formals = formals;
        Ok(levels)
    }

    pub fn analyze_definition(
        &self,
        definition: &Rc<Definition>,
        scope: &Scope,
    ) -> Result<Rc<OperatorLevels>> {
        let address = Rc::as_ptr(definition) as usize;
        if let Some(cached) = self.definition_levels.borrow().get(&address) {
            return Ok(cached.clone());
        }
        let formals: Vec<Formal> = match &definition.kind {
            DefinitionKind::Operator { params, .. } => params
                .iter()
                .map(|param| Formal {
                    name: param.name.clone(),
                    arity: param.arity,
                })
                .collect(),
            DefinitionKind::Function { .. } => Vec::new(),
        };
        // A recursive reference reads the levels of a definition being analyzed as these.
        self.definition_levels.borrow_mut().insert(
            address,
            Rc::new(OperatorLevels {
                data: LevelData::default(),
                name: definition.name.clone(),
                max_levels: vec![TEMPORAL_LEVEL; formals.len()],
                weights: vec![0; formals.len()],
                min_max_levels: vec![Vec::new(); formals.len()],
                conditions: FastSet::default(),
                non_leibniz: FastSet::default(),
                formals: formals.clone(),
            }),
        );
        let body = match &definition.kind {
            DefinitionKind::Function { bounds } => Rc::new(Expression::new(
                ExpressionKind::FunctionConstruction {
                    bounds: bounds.clone(),
                    body: definition.body.clone(),
                },
                definition.location.clone(),
            )),
            DefinitionKind::Operator { .. } => definition.body.clone(),
        };
        let levels = Rc::new(self.analyze_operator(&definition.name, formals, &body, scope)?);
        self.definition_levels
            .borrow_mut()
            .insert(address, levels.clone());
        Ok(levels)
    }

    /// `analyzeAssumeProve`.
    pub fn analyze_assume_prove(
        &self,
        assume_prove: &AssumeProve,
        scope: &Scope,
    ) -> Result<LevelData> {
        let mut inner = scope.clone();
        let mut parts = Vec::new();
        for assumption in &assume_prove.assumptions {
            match assumption {
                Assumed::NewSymbol(symbol) => {
                    if let Some(set) = &symbol.set {
                        parts.push(self.analyze(set, &inner)?);
                    }
                    inner = inner.bind(vec![(symbol.name.clone(), Entry::Formal(symbol.arity))]);
                }
                Assumed::AssumeProve(nested) => {
                    parts.push(self.analyze_assume_prove(nested, &inner)?)
                }
                Assumed::Expression(expression) => parts.push(self.analyze(expression, &inner)?),
            }
        }
        parts.push(self.analyze(&assume_prove.conclusion, &inner)?);
        let mut data = LevelData::new(parts.iter().map(|part| part.level).max().unwrap_or(0));
        for part in &parts {
            for param in part.params.keys() {
                add(&mut data.params, param);
            }
            for (key, value) in part.constraints.iter() {
                put_constraint(&mut data.constraints, key, *value);
            }
            for (key, value) in part.arg_constraints.iter() {
                put_arg_constraint(&mut data.arg_constraints, key, *value);
            }
            for key in part.arg_params.keys() {
                add(&mut data.arg_params, key);
            }
        }
        Ok(data)
    }

    fn get_statement_level(&self, statement: &Statement) -> Result<LevelData> {
        match statement {
            Statement::AssumeProve(assume_prove) => {
                self.analyze_assume_prove(assume_prove, &Scope::default())
            }
            Statement::Expression(expression) => self.analyze(expression, &Scope::default()),
        }
    }
}

fn get_level(analyzer: &LevelAnalyzer, expressions: &[Expr]) -> Result<u8> {
    let mut level = 0;
    for expression in expressions {
        level = level.max(analyzer.analyze(expression, &Scope::default())?.level);
    }
    Ok(level)
}

fn get_step_level(analyzer: &LevelAnalyzer, step: &ProofStep) -> Result<u8> {
    match &step.body {
        StepBody::Have(expression) | StepBody::Case(expression) => {
            get_level(analyzer, std::slice::from_ref(expression))
        }
        StepBody::Witness(expressions) => get_level(analyzer, expressions),
        StepBody::Take { bounds, .. } => get_level(
            analyzer,
            &bounds
                .iter()
                .map(|bound| bound.set.clone())
                .collect::<Vec<_>>(),
        ),
        StepBody::Pick { bounds, body, .. } => get_level(
            analyzer,
            &std::iter::once(body.clone())
                .chain(bounds.iter().map(|bound| bound.set.clone()))
                .collect::<Vec<_>>(),
        ),
        StepBody::Assert { statement, .. } => Ok(analyzer.get_statement_level(statement)?.level),
        _ => Ok(0),
    }
}

/// SANY's TheoremNode.LevelCheckTemporal: the proof of a temporal goal may only assume constants.
fn get_steps(proof: Option<&Proof>) -> &[ProofStep] {
    match proof.map(|proof| &proof.kind) {
        Some(ProofKind::Steps { steps, .. }) => steps,
        _ => &[],
    }
}

fn check_temporal_goal(analyzer: &LevelAnalyzer, proof: Option<&Proof>) -> Result<Vec<SanyError>> {
    let steps = get_steps(proof);
    if steps.is_empty() {
        return Ok(Vec::new());
    }
    let mut errors = Vec::new();
    for step in steps {
        let location = format_range(&step.statement);
        let is_constant = || -> Result<bool> { Ok(get_step_level(analyzer, step)? == 0) };
        match &step.body {
            StepBody::Have(_) | StepBody::Take { .. } | StepBody::Witness(_) => {
                if !is_constant()? {
                    errors.push(SanyError {
                        location,
                        message: "Non-constant TAKE, WITNESS, or HAVE for temporal goal."
                            .to_owned(),
                    });
                }
            }
            StepBody::Case(_) => {
                if !is_constant()? {
                    errors.push(SanyError {
                        location,
                        message: "Non-constant CASE for temporal goal.".to_owned(),
                    });
                }
                errors.extend(check_temporal_goal(analyzer, step.proof.as_deref())?);
            }
            StepBody::Qed => errors.extend(check_temporal_goal(analyzer, step.proof.as_deref())?),
            _ => {}
        }
    }
    Ok(errors)
}

/// SANY checks each step as a theorem of its own after the steps of its proof.
fn check_proof(analyzer: &LevelAnalyzer, proof: Option<&Proof>) -> Result<Vec<SanyError>> {
    let steps = get_steps(proof);
    if steps.is_empty() {
        return Ok(Vec::new());
    }
    let mut errors = Vec::new();
    for step in steps {
        errors.extend(check_proof(analyzer, step.proof.as_deref())?);
        let is_temporal =
            || -> Result<bool> { Ok(get_step_level(analyzer, step)? == TEMPORAL_LEVEL) };
        if let StepBody::Pick { bounds, .. } = &step.body
            && !bounds.is_empty()
            && is_temporal()?
        {
            for bound in bounds {
                if get_level(analyzer, std::slice::from_ref(&bound.set))? != 0
                    && let Some(range) = &bound.set.location.range
                {
                    errors.push(SanyError {
                        location: format_range(range),
                        message: "Non-constant bound of temporal PICK.".to_owned(),
                    });
                }
            }
        }
        let has_steps = !get_steps(step.proof.as_deref()).is_empty()
            || matches!(
                step.proof.as_deref().map(|proof| &proof.kind),
                Some(ProofKind::Steps { .. })
            );
        if has_steps && is_temporal()? {
            errors.extend(check_temporal_goal(analyzer, step.proof.as_deref())?);
        }
    }
    Ok(errors)
}

/// `checkModuleLevels`: the units SANY level-checks in a module, the definitions, assumptions and
/// theorems, with the checks of its instances.
pub fn get_level_units<'b>(
    module: &'b Module,
    analyzer: &'b LevelAnalyzer<'b>,
    mut units: Vec<SemanticUnit<'b>>,
) -> Vec<SemanticUnit<'b>> {
    // `ModuleNode.levelCheck` checks the recursive sections before the rest of the module.
    units.push(SemanticUnit {
        location: module.location.position(),
        check: Box::new(move |_, _| check_recursive_arguments(module, analyzer)),
    });
    for definition in &module.definitions {
        if definition.name.contains('!') {
            continue;
        }
        units.push(SemanticUnit {
            location: definition.location.position(),
            check: Box::new(move |_, _| {
                analyzer.analyze_definition(definition, &Scope::default())?;
                Ok(())
            }),
        });
    }
    for assumption in &module.assumptions {
        units.push(SemanticUnit {
            location: assumption.location.position(),
            check: Box::new(move |_, _| {
                let data = analyzer.analyze(&assumption.expression, &Scope::default())?;
                if data.level == CONSTANT_LEVEL {
                    return Ok(());
                }
                // `AssumeNode.levelCheck`, at the assumption.
                let Some(range) = &assumption.location.range else {
                    return Err(FrontError::NotYet(
                        "an assumption without a range".to_owned(),
                    ));
                };
                Err(FrontError::Syntax(SyntaxError::sany(vec![SanyError {
                    location: format_range(range),
                    message: format!(
                        "Level error: assumptions must be level 0 (Constant), \nbut this one has level {}.",
                        data.level
                    ),
                }])))
            }),
        });
    }
    for theorem in &module.theorems {
        units.push(SemanticUnit {
            location: theorem.location.position(),
            check: Box::new(move |_, _| {
                let data = analyzer.get_statement_level(&theorem.statement)?;
                let mut errors = check_proof(analyzer, theorem.proof.as_ref())?;
                if data.level == TEMPORAL_LEVEL {
                    errors.extend(check_temporal_goal(analyzer, theorem.proof.as_ref())?);
                }
                if errors.is_empty() {
                    return Ok(());
                }
                Err(FrontError::Syntax(SyntaxError::sany(errors)))
            }),
        });
    }
    units
}

// The names of the operators an expression applies or names.
fn collect_names(expression: &Expr, names: &mut FastSet<Name>) {
    match &expression.kind {
        ExpressionKind::Identifier { name, .. } => {
            names.insert(name.clone());
        }
        ExpressionKind::Apply { operator, .. }
        | ExpressionKind::OperatorReference { operator, .. } => {
            names.insert(operator.clone());
        }
        _ => {}
    }
    for child in expression.children() {
        collect_names(&child, names);
    }
}

// The definitions of the LETs in an expression, outermost first.
fn collect_let_definitions(expression: &Expr, definitions: &mut Vec<Rc<Definition>>) {
    if let ExpressionKind::Let {
        definitions: defined,
        ..
    } = &expression.kind
    {
        definitions.extend(defined.iter().cloned());
    }
    for child in expression.children() {
        collect_let_definitions(&child, definitions);
    }
}

/// `ModuleNode.levelCheck`'s check of the recursive operators: SANY rejects one whose argument
/// its body takes at a level below an action's, as a primed parameter. SANY reads each recursive
/// operator a recursive section applies with arguments of action level; the analyzer reads the
/// operator it is analyzing so, but another of the section with its levels, so a recursive
/// operator that applies another stays `NotYet` where it would be rejected, as do errors of both a
/// module's and a LET's recursive operators, whose order isn't checked.
fn check_recursive_arguments(module: &Module, analyzer: &LevelAnalyzer) -> Result<()> {
    // Each recursive operator with the levels of its arguments, or none where it or its LET's
    // definition fails to analyze, which its own unit reports.
    let mut recursive: Vec<(Rc<Definition>, Option<Rc<OperatorLevels>>, bool)> = Vec::new();
    for definition in &module.definitions {
        if definition.is_recursive {
            // A level error is its own unit's to report.
            let levels = analyzer
                .analyze_definition(definition, &Scope::default())
                .ok();
            recursive.push((definition.clone(), levels, false));
        }
    }
    for definition in &module.definitions {
        let mut lets = Vec::new();
        collect_let_definitions(&definition.body, &mut lets);
        lets.retain(|defined| defined.is_recursive);
        if lets.is_empty() {
            continue;
        }
        let is_analyzed = analyzer
            .analyze_definition(definition, &Scope::default())
            .is_ok();
        for defined in lets {
            let levels = is_analyzed
                .then(|| {
                    analyzer
                        .definition_levels
                        .borrow()
                        .get(&(Rc::as_ptr(&defined) as usize))
                        .cloned()
                })
                .flatten();
            recursive.push((defined, levels, true));
        }
    }
    let names: FastSet<Name> = recursive
        .iter()
        .map(|(definition, _, _)| definition.name.clone())
        .collect();
    let mut errors = Vec::new();
    let mut kinds = FastSet::default();
    for (definition, levels, is_in_let) in &recursive {
        let Some(levels) = levels else {
            return Err(FrontError::NotYet(
                "a recursive operator whose levels fail to analyze".to_owned(),
            ));
        };
        let primed: Vec<usize> = (0..levels.max_levels.len())
            .filter(|&index| levels.max_levels[index] < ACTION_LEVEL)
            .collect();
        if primed.is_empty() {
            continue;
        }
        let mut applied = FastSet::default();
        collect_names(&definition.body, &mut applied);
        if applied
            .iter()
            .any(|name| *name != definition.name && names.contains(name))
        {
            return Err(FrontError::NotYet(
                "a primed argument of a recursive operator that applies another".to_owned(),
            ));
        }
        let Some(range) = &definition.location.range else {
            return Err(FrontError::NotYet(
                "a recursive operator without a range".to_owned(),
            ));
        };
        kinds.insert(*is_in_let);
        for index in primed {
            errors.push(SanyError {
                location: format_range(range),
                message: format!(
                    "Argument {} of recursive operator {} is primed",
                    index + 1,
                    definition.name
                ),
            });
        }
    }
    if kinds.len() > 1 {
        return Err(FrontError::NotYet(
            "primed arguments of both a module's and a LET's recursive operators".to_owned(),
        ));
    }
    if errors.is_empty() {
        return Ok(());
    }
    Err(FrontError::Syntax(SyntaxError::sany(errors)))
}

/// What the instance checker reads of a module: its declarations, definitions and facts.
pub struct ModuleLevelContext<'a> {
    pub constants: Vec<Rc<Declaration>>,
    pub variables: Vec<Name>,
    pub definitions: Vec<Rc<Definition>>,
    pub assumptions: Vec<Expr>,
    pub theorems: Vec<Rc<Theorem>>,
    pub analyzer: LevelAnalyzer<'a>,
}

/// An instance SANY checks the substitutions of.
pub struct InstanceCheck {
    pub module: Name,
    pub instancer: Name,
    pub lets: Vec<Rc<Definition>>,
    pub substitutions: OrderedMap<Name, Expr>,
    pub location: Location,
}

struct ModuleLevels {
    is_constant: bool,
    constraints: OrderedMap<Name, u8>,
    arg_constraints: OrderedMap<ArgumentKey, u8>,
    arg_params: OrderedSet<ArgumentParamKey>,
}

fn get_module_levels(module: &ModuleLevelContext) -> Result<ModuleLevels> {
    let analyzer = &module.analyzer;
    let definitions = module
        .definitions
        .iter()
        .map(|definition| analyzer.analyze_definition(definition, &Scope::default()))
        .collect::<Result<Vec<_>>>()?;
    let mut levels = ModuleLevels {
        is_constant: module.variables.is_empty()
            && definitions
                .iter()
                .all(|definition| definition.data.level == 0),
        constraints: OrderedMap::new(),
        arg_constraints: OrderedMap::new(),
        arg_params: OrderedMap::new(),
    };
    if !levels.is_constant {
        for constant in &module.constants {
            put_constraint(&mut levels.constraints, &constant.name, 0);
        }
    }
    fn add_levels(
        levels: &mut ModuleLevels,
        data: &LevelData,
        is_kept: &dyn Fn(&Name, &Name) -> bool,
    ) {
        for (key, value) in data.constraints.iter() {
            put_constraint(&mut levels.constraints, key, *value);
        }
        for (key, value) in data.arg_constraints.iter() {
            put_arg_constraint(&mut levels.arg_constraints, key, *value);
        }
        for key in data.arg_params.keys() {
            if is_kept(&key.0, &key.2) {
                add(&mut levels.arg_params, key);
            }
        }
    }
    for definition in &definitions {
        add_levels(&mut levels, &definition.data, &|operator, param| {
            definition
                .formals
                .iter()
                .all(|formal| formal.name != *operator && formal.name != *param)
        });
    }
    let add_assumed_levels = |levels: &mut ModuleLevels, data: &LevelData| {
        add_levels(levels, data, &|_, _| true);
        for constant in &module.constants {
            if data.params.contains_key(&constant.name) {
                put_constraint(&mut levels.constraints, &constant.name, ACTION_LEVEL);
            }
        }
    };
    for assumption in &module.assumptions {
        add_assumed_levels(
            &mut levels,
            &analyzer.analyze(assumption, &Scope::default())?,
        );
    }
    for theorem in &module.theorems {
        match &theorem.statement {
            Statement::AssumeProve(assume_prove) => add_assumed_levels(
                &mut levels,
                &analyzer.analyze_assume_prove(assume_prove, &Scope::default())?,
            ),
            Statement::Expression(expression) => add_levels(
                &mut levels,
                &analyzer.analyze(expression, &Scope::default())?,
                &|_, _| true,
            ),
        }
    }
    Ok(levels)
}

struct Substituted {
    name: Name,
    maximum_level: u8,
    arity: usize,
    level: u8,
    operator: Option<Rc<OperatorLevels>>,
    is_leibniz: bool,
}

/// `createInstanceChecker`: checks the substitutions of an instance of `instancee` in the module
/// `instancer` analyzes.
pub fn check_instance(
    check: &InstanceCheck,
    instancee: &ModuleLevelContext,
    instancer: &LevelAnalyzer,
) -> Result<()> {
    let mut errors: OrderedMap<String, SanyError> = OrderedMap::new();
    // SANY reports each error at the whole instance.
    let location = match &check.location.range {
        Some(range) => format_range(range),
        None => format_range(&SourceRange {
            module: check.instancer.clone(),
            start: check.location.position(),
            end: check.location.position(),
        }),
    };
    let mut add_message = |message: String| {
        errors.insert(
            format!("{location}\n{message}"),
            SanyError {
                location: location.clone(),
                message,
            },
        );
    };
    let levels = get_module_levels(instancee)?;
    let scope = Scope::default().bind(
        check
            .lets
            .iter()
            .map(|definition| (definition.name.clone(), Entry::Let(definition.clone())))
            .collect(),
    );
    let declarations = instancee
        .constants
        .iter()
        .map(|constant| (constant.name.clone(), constant.arity, CONSTANT_LEVEL))
        .chain(
            instancee
                .variables
                .iter()
                .map(|variable| (variable.clone(), 0, VARIABLE_LEVEL)),
        );
    let mut substituted = Vec::new();
    for (name, arity, maximum_level) in declarations {
        let Some(expression) = check.substitutions.get(&name) else {
            continue;
        };
        if arity == 0 {
            let data = instancer.analyze(expression, &scope)?;
            substituted.push(Substituted {
                name,
                maximum_level,
                arity,
                level: data.level,
                operator: None,
                is_leibniz: true,
            });
            continue;
        }
        let operand = instancer.to_operand(expression, &scope)?;
        substituted.push(Substituted {
            name,
            maximum_level,
            arity,
            level: operand.data().level,
            is_leibniz: operand
                .operator
                .as_ref()
                .is_none_or(|operator| operator.non_leibniz.is_empty()),
            operator: operand.operator,
        });
    }
    let get_level_message = |name: &Name, level: u8| {
        format!(
            "Level error in instantiating module '{}':\nThe level of the expression or operator substituted for '{name}' \nmust be at most {level}.",
            check.module
        )
    };
    for item in &substituted {
        if !levels.is_constant && item.level > item.maximum_level {
            add_message(get_level_message(&item.name, item.maximum_level));
        }
        if !item.is_leibniz {
            add_message(format!(
                "Error in instantiating module '{}':\n A non-Leibniz operator substituted for '{}'.",
                check.module, item.name
            ));
        }
    }
    for item in &substituted {
        if let Some(maximum) = levels.constraints.get(&item.name)
            && item.level > *maximum
        {
            add_message(get_level_message(&item.name, *maximum));
        }
        let Some(operator) = &item.operator else {
            continue;
        };
        for index in 0..item.arity {
            if let Some(minimum) = levels.arg_constraints.get(&(item.name.clone(), index))
                && operator
                    .max_levels
                    .get(index)
                    .copied()
                    .unwrap_or(TEMPORAL_LEVEL)
                    < *minimum
            {
                add_message(format!(
                    "Level error in instantiating module '{}':\nThe level of the argument {} of the operator {} \nmust be at least {minimum}.",
                    check.module,
                    index + 1,
                    operator.name
                ));
            }
        }
    }
    for (operator_name, index, param) in levels.arg_params.keys() {
        let operator = substituted
            .iter()
            .find(|item| item.name == *operator_name)
            .and_then(|item| item.operator.as_ref());
        let argument = substituted.iter().find(|item| item.name == *param);
        let (Some(operator), Some(argument)) = (operator, argument) else {
            continue;
        };
        let maximum = operator
            .max_levels
            .get(*index)
            .copied()
            .unwrap_or(TEMPORAL_LEVEL);
        if argument.level > maximum {
            add_message(format!(
                "Level error when instantiating module '{}':\nThe level of the argument {index} of the operator {operator_name}' \nmust be at most {maximum}.",
                check.module
            ));
        }
    }
    if errors.is_empty() {
        return Ok(());
    }
    Err(FrontError::Syntax(SyntaxError::sany(
        errors.values().cloned().collect(),
    )))
}
