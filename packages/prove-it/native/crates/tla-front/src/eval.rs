//! A small evaluator of the constant expressions the front end needs values of before the
//! search, as `evaluate` in `src/evaluate.ts` computes them: the sets TLC unrolls a property's or
//! a temporal formula's quantifier over, the constant parts of a temporal formula, and the
//! substitutes for constants TLC evaluates at startup, whose failures it reports. It knows
//! booleans, integers, strings, model values, records and finite sets of them, and returns `NotYet`
//! for anything else, which TLC's own evaluation at startup handles.

use std::cell::{Cell, RefCell};
use std::cmp::Ordering;
use std::collections::HashMap;
use std::rc::Rc;

use crate::TlcVersion;
use crate::ast::*;
use crate::config::ConfigValue;
use crate::environment::Environment;
use crate::errors::{FrontError, describe_range};
use crate::resolve::Result;
use crate::spec::{Binding, Scope, ScopeOf, bind_definitions, get_definition, lookup_scope};
use crate::tlc_data::SANY_OPERATOR_SYNONYMS;
use crate::values::{ValueOrder, get_model_value_type};

/// The most elements the evaluator lists of a set, past which TLC's run is the engine's.
const MAXIMUM_ELEMENTS: i64 = 100_000;

/// The deepest the evaluator nests, past which a recursion is the engine's.
const MAXIMUM_DEPTH: usize = 400;

/// The keys of TLCGet that TLC's model checker holds.
const CHECKER_KEYS: [&str; 6] = [
    "diameter",
    "generated",
    "distinct",
    "queue",
    "stats",
    "config",
];

const TLC_GET_EVAL: &str = "public static tlc2.value.impl.Value tlc2.module.TLCGetSet.TLCGetEval(tlc2.tool.impl.Tool,tla2sany.semantic.ExprOrOpArgNode[],tlc2.util.Context,tlc2.tool.TLCState,tlc2.tool.TLCState,int,tlc2.tool.coverage.CostModel)";

fn not_yet(reason: &str) -> FrontError {
    FrontError::NotYet(format!(
        "{reason}, which the constant evaluator doesn't compute"
    ))
}

const TOO_DEEP: &str = "a recursion too deep";

// Whether the evaluation stopped at a recursion too deep, which evaluating the same expression
// again only repeats: a recursive definition whose evaluation asks itself through each of these
// retries would double its work at each level, and never finish.
fn is_too_deep(reason: &str) -> bool {
    reason.starts_with(TOO_DEEP)
}

thread_local! {
    /// Whether a membership or a bound inside a filter's predicate stopped at a recursion too
    /// deep, as `1 \in A(1500)` with
    /// `A(n) == IF n = 0 THEN {1} ELSE {x \in {1, 2} : 1 \in A(n - 1)}`: TLC filters the set
    /// enumeration at once at each level, so it evaluates `A(n - 1)` twice there, and either
    /// overflows its stack or doesn't finish, where the engine, which keeps a recursive
    /// operator's values, would answer (`take_membership_too_deep`).
    static MEMBERSHIP_TOO_DEEP: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Whether a membership or a bound inside a filter's predicate stopped at a recursion too deep
/// since the last call.
pub(crate) fn take_membership_too_deep() -> bool {
    MEMBERSHIP_TOO_DEEP.with(|flag| flag.replace(false))
}

// Whether `reason` is a recursion too deep, noting one met inside a filter's predicate.
fn note_too_deep(reason: &str, filtering: usize) -> bool {
    let is_too_deep = is_too_deep(reason);
    if is_too_deep && filtering > 0 {
        MEMBERSHIP_TOO_DEEP.with(|flag| flag.set(true));
    }
    is_too_deep
}

/// The name an operator's synonyms share, as `SANY_OPERATOR_SYNONYMS` lists them first.
fn get_canonical_name(name: &str) -> &str {
    SANY_OPERATOR_SYNONYMS
        .iter()
        .find(|synonyms| synonyms.contains(&name))
        .map_or(name, |synonyms| synonyms[0])
}

/// TLC's integers, which a value past 32 bits overflows.
fn to_integer(value: i64) -> Result<ConfigValue> {
    i32::try_from(value)
        .map(|value| ConfigValue::Number(f64::from(value)))
        .map_err(|_| not_yet("an integer TLC overflows"))
}

fn get_integer(value: &ConfigValue) -> Result<i64> {
    match value {
        ConfigValue::Number(number) if number.fract() == 0.0 => Ok(*number as i64),
        _ => Err(not_yet("arithmetic on a value that isn't an integer")),
    }
}

fn get_boolean(value: &ConfigValue) -> Result<bool> {
    match value {
        ConfigValue::Boolean(value) => Ok(*value),
        _ => Err(not_yet("a value that isn't a boolean where TLC wants one")),
    }
}

fn get_elements(value: ConfigValue) -> Result<Vec<ConfigValue>> {
    match value {
        ConfigValue::Set(elements) => Ok(elements),
        _ => Err(not_yet("a value that isn't a set where TLC wants one")),
    }
}

/// The most elements of a set whose subsets the evaluator draws from, one at a time.
const MAXIMUM_DRAWN_BASE: usize = 12;

/// The longest text of a value the evaluator prints, which TLC's pretty-printer, 80 columns wide,
/// leaves on one line.
const MAXIMUM_PLAIN_TEXT: usize = 60;

/// The text TLC prints of a natural number, a string of letters, digits and spaces, or a boolean.
fn format_scalar(value: &ConfigValue) -> Option<String> {
    match value {
        ConfigValue::Number(number) if *number >= 0.0 => Some(format!("{number}")),
        ConfigValue::String(text)
            if text
                .chars()
                .all(|character| character.is_ascii_alphanumeric() || character == ' ') =>
        {
            Some(format!("\"{text}\""))
        }
        ConfigValue::Boolean(value) => Some(if *value { "TRUE" } else { "FALSE" }.to_owned()),
        _ => None,
    }
}

/// The sets of numbers and strings TLC knows by name, which have no elements to list.
enum Infinite {
    Nat,
    Int,
    String,
}

/// The elements an evaluator takes for the draws of RandomElement it makes, in order, to compute
/// an expression for each element TLC may draw.
#[derive(Default)]
pub struct Draws {
    /// The position in its set of the element each draw takes; 0 past these.
    pub choices: Vec<usize>,
    /// How many elements the set each draw it made drew from has.
    pub sizes: Vec<usize>,
}

/// Whether a name is the builtin that draws, of the standard module that defines it: the draws
/// an evaluator given `Draws` follows.
pub(crate) fn is_builtin_draw(environment: &Environment, name: &str, module: &str) -> bool {
    environment
        .builtins
        .get(name)
        .is_some_and(|builtin| &*builtin.name == name && builtin.intrinsic.is_none())
        && environment.definitions.get(name).is_none_or(|definition| {
            definition
                .location
                .range
                .as_ref()
                .is_some_and(|range| &*range.module == module)
        })
}

/// How many combinations of the elements its draws may take `for_every_draw` evaluates an
/// expression for, at most.
const DRAW_COMBINATIONS: usize = 4096;

/// Whether `accepts` takes what an expression gives for each combination of the elements its
/// draws may take, in turn, up to `DRAW_COMBINATIONS`, with the sizes of the sets it drew from:
/// a probe evaluator in `environment`, of `evaluator`'s order and version, computes it once for
/// each.
pub(crate) fn for_every_draw(
    environment: &Environment,
    evaluator: &Evaluator,
    expression: &Expr,
    mut accepts: impl FnMut(Result<ConfigValue>, &[usize]) -> bool,
) -> bool {
    let mut choices = Vec::new();
    for _ in 0..DRAW_COMBINATIONS {
        let probe = Evaluator::new(
            environment,
            ValueOrder {
                ranks: evaluator.order.ranks,
            },
            evaluator.version,
            false,
        );
        *probe.draws.borrow_mut() = Some(Draws {
            choices: choices.clone(),
            sizes: Vec::new(),
        });
        let value = probe.evaluate(expression, None);
        let sizes = probe
            .draws
            .take()
            .map(|draws| draws.sizes)
            .unwrap_or_default();
        if !accepts(value, &sizes) {
            return false;
        }
        choices.resize(sizes.len(), 0);
        let Some(last) = (0..sizes.len())
            .rev()
            .find(|&at| choices[at] + 1 < sizes[at])
        else {
            return true;
        };
        choices.truncate(last + 1);
        choices[last] += 1;
    }
    false
}

pub struct Evaluator<'a> {
    pub environment: &'a Environment,
    pub order: ValueOrder<'a>,
    pub version: TlcVersion,
    /// Whether TLC has created its model checker, before which TLCGet reads none of its keys.
    pub is_started: bool,
    /// Whether it computes TLCSet as TLC does as it processes the spec, before it has made its
    /// checker or simulator (`TLCGetSet.TLCSet`), where it otherwise leaves TLCSet uncomputed.
    pub computes_tlc_set: bool,
    /// How many TLCSets it computed, where it computes them.
    pub tlc_sets: Cell<usize>,
    /// Where it computes RandomElement, the element of the set it draws each from, by the
    /// position of the draw (`Draws`); otherwise it leaves RandomElement uncomputed.
    pub draws: RefCell<Option<Draws>>,
    depth: Cell<usize>,
    /// How many filters' predicates it is evaluating, one inside another.
    filtering: Cell<usize>,
    /// Whether a value it couldn't compute was left to the engine's startup.
    is_deferring: Cell<bool>,
    /// The constant conjuncts of the specification, by name, whose values it left to the
    /// engine's startup.
    deferred_conjuncts: RefCell<Vec<Name>>,
    /// The value of each thunk it computed, by the node that binds it, which it keeps alive: TLC
    /// computes an operator's argument where the body first uses it, and keeps the value
    /// (`LazyValue`).
    thunks: RefCell<HashMap<usize, (Rc<Scope>, ConfigValue)>>,
    /// The value of each definition without parameters it computed without effect, by the
    /// definition, which it keeps alive, with how much deeper than the definition the computation
    /// nested and whether it computed TLCSet: TLC computes a constant definition once as it starts
    /// (`processConstantDefns`), so a chain of definitions that each name the one before twice
    /// takes a step a definition, not one for each path to it.
    definitions: RefCell<HashMap<usize, KeptDefinition>>,
    /// The value of each application of a definition with parameters it computed without effect,
    /// by the definition and the values of its arguments, which it knew without computing anything:
    /// as `definitions`, for a chain of operators that each apply the one before twice.
    applications: RefCell<HashMap<(usize, String), KeptDefinition>>,
    /// The deepest it nested since the definition it is computing began.
    deepest: Cell<usize>,
}

/// A definition's value as `Evaluator::definitions` keeps it.
struct KeptDefinition {
    _definition: Rc<Definition>,
    value: ConfigValue,
    span: usize,
    computes_tlc_set: bool,
}

impl<'a> Evaluator<'a> {
    pub fn new(
        environment: &'a Environment,
        order: ValueOrder<'a>,
        version: TlcVersion,
        is_started: bool,
    ) -> Evaluator<'a> {
        Evaluator {
            environment,
            order,
            version,
            is_started,
            computes_tlc_set: false,
            tlc_sets: Cell::new(0),
            draws: RefCell::new(None),
            depth: Cell::new(0),
            filtering: Cell::new(0),
            is_deferring: Cell::new(false),
            deferred_conjuncts: RefCell::new(Vec::new()),
            thunks: RefCell::new(HashMap::new()),
            definitions: RefCell::new(HashMap::new()),
            applications: RefCell::new(HashMap::new()),
            deepest: Cell::new(0),
        }
    }

    /// Leaves a value it couldn't compute to the engine's startup, which checks it.
    pub fn defer(&self) {
        self.is_deferring.set(true);
    }

    pub fn is_deferring(&self) -> bool {
        self.is_deferring.get()
    }

    /// Leaves the value of a constant conjunct of the specification to the engine's startup.
    pub fn defer_conjunct(&self, name: Name) {
        self.defer();
        self.deferred_conjuncts.borrow_mut().push(name);
    }

    pub fn deferred_conjuncts(&self) -> Vec<Name> {
        self.deferred_conjuncts.borrow().clone()
    }
}

impl Evaluator<'_> {
    /// `valuesEqual`: TLC compares a model value with any value, and values of other kinds only
    /// with values of their own kind.
    fn equals(&self, left: &ConfigValue, right: &ConfigValue) -> Result<bool> {
        match (left, right) {
            (ConfigValue::ModelValue(name), other) | (other, ConfigValue::ModelValue(name))
                if !matches!(other, ConfigValue::ModelValue(_)) =>
            {
                if get_model_value_type(name).is_some() {
                    return Err(not_yet("a typed model value compared"));
                }
                Ok(false)
            }
            (ConfigValue::Number(_), ConfigValue::Number(_))
            | (ConfigValue::String(_), ConfigValue::String(_))
            | (ConfigValue::Boolean(_), ConfigValue::Boolean(_))
            | (ConfigValue::ModelValue(_), ConfigValue::ModelValue(_))
            | (ConfigValue::Set(_), ConfigValue::Set(_))
            | (ConfigValue::Record(_), ConfigValue::Record(_)) => {
                Ok(self.order.compare(left, right)? == Ordering::Equal)
            }
            _ => Err(not_yet("values TLC can't compare")),
        }
    }

    /// `=` of two operands, `Value#equals` of the left one's value: an integer, a string or a
    /// boolean fails for a value of another kind but a model value, with both values' texts.
    fn equals_operands(&self, args: &[Expr], scope: Option<&Rc<Scope>>) -> Result<bool> {
        // Where it computes the draws, two tuples written out of integers, strings or booleans,
        // which TLC builds in turn, element by element, and compares element by element
        // (`TupleValue.equals`), a pair of different lengths being unequal.
        if self.draws.borrow().is_some()
            && let (ExpressionKind::Tuple(left), ExpressionKind::Tuple(right)) =
                (&args[0].kind, &args[1].kind)
        {
            let left = left
                .iter()
                .map(|element| self.evaluate(element, scope))
                .collect::<Result<Vec<_>>>()?;
            let right = right
                .iter()
                .map(|element| self.evaluate(element, scope))
                .collect::<Result<Vec<_>>>()?;
            if left.len() != right.len() {
                return Ok(false);
            }
            for (left, right) in left.iter().zip(&right) {
                match (left, right) {
                    (ConfigValue::Number(_), ConfigValue::Number(_))
                    | (ConfigValue::String(_), ConfigValue::String(_))
                    | (ConfigValue::Boolean(_), ConfigValue::Boolean(_)) => {
                        if left != right {
                            return Ok(false);
                        }
                    }
                    _ => return Err(not_yet("a tuple's elements TLC may not compare")),
                }
            }
            return Ok(true);
        }
        let left = self.evaluate(&args[0], scope)?;
        let right = self.evaluate(&args[1], scope)?;
        let failure = match (&left, &right) {
            (ConfigValue::Number(_), ConfigValue::Number(_))
            | (ConfigValue::String(_), ConfigValue::String(_))
            | (ConfigValue::Boolean(_), ConfigValue::Boolean(_))
            | (_, ConfigValue::ModelValue(_)) => None,
            (ConfigValue::Number(_), _) => Some(("check equality of integer", "non-integer")),
            (ConfigValue::String(_), _) => Some(("check equality of string", "non-string")),
            (ConfigValue::Boolean(_), _) => Some(("compare equality of boolean", "non-boolean")),
            _ => None,
        };
        let Some((check, other)) = failure else {
            return self.equals(&left, &right);
        };
        // The values' texts, which TLC pretty-prints, the right one's as its class prints it.
        let left_text = format_scalar(&left).ok_or_else(|| not_yet("values TLC can't compare"))?;
        let right_text = match (&right, &args[1].kind) {
            (ConfigValue::Set(elements), ExpressionKind::SetEnumeration(_)) => elements
                .iter()
                .map(format_scalar)
                .collect::<Option<Vec<_>>>()
                .map(|elements| format!("{{{}}}", elements.join(", "))),
            _ => format_scalar(&right),
        }
        .filter(|text| text.len() <= MAXIMUM_PLAIN_TEXT)
        .ok_or_else(|| not_yet("values TLC can't compare"))?;
        Err(FrontError::Evaluation(format!(
            "Attempted to {check} {left_text} with {other}:\n{right_text}"
        )))
    }

    /// The element of `elements` the next draw takes (`Draws`), counting how many it drew from.
    fn take_draw(&self, elements: Vec<ConfigValue>) -> Result<ConfigValue> {
        let mut draws = self.draws.borrow_mut();
        let draws = draws.as_mut().expect("draws");
        let choice = draws.choices.get(draws.sizes.len()).copied().unwrap_or(0);
        draws.sizes.push(elements.len());
        elements
            .get(choice)
            .cloned()
            .ok_or_else(|| not_yet("RandomElement of a set without the element drawn"))
    }

    /// The subsets of a set's elements, or those of `size` elements.
    fn get_subsets(&self, base: &[ConfigValue], size: Option<usize>) -> Result<Vec<ConfigValue>> {
        let mut subsets = Vec::new();
        for mask in 0..(1usize << base.len()) {
            if size.is_some_and(|size| mask.count_ones() as usize != size) {
                continue;
            }
            let elements = (0..base.len())
                .filter(|at| mask & (1 << at) != 0)
                .map(|at| base[at].clone())
                .collect();
            subsets.push(self.create_set(elements)?);
        }
        Ok(subsets)
    }

    fn create_set(&self, elements: Vec<ConfigValue>) -> Result<ConfigValue> {
        self.order.normalize(&ConfigValue::Set(elements))
    }

    /// A record's or a set of records' fields in TLC's order of their names, as `getSortedFields`
    /// sorts them.
    fn get_sorted_fields<'b>(&self, fields: &'b [RecordField]) -> Result<Vec<&'b RecordField>> {
        let mut sorted: Vec<&RecordField> = fields.iter().collect();
        crate::values::try_sort_by(&mut sorted, &mut |left, right| {
            self.order.compare_strings(&left.name, &right.name)
        })?;
        if sorted.windows(2).any(|pair| pair[0].name == pair[1].name) {
            return Err(not_yet("a record with a repeated field"));
        }
        Ok(sorted)
    }

    /// The records of `[f1 : S1, ..., fn : Sn]`, the last field varying fastest, as
    /// `getCartesianProduct` lists them, sorted into a set.
    fn get_records(
        &self,
        fields: &[RecordField],
        scope: Option<&Rc<Scope>>,
    ) -> Result<ConfigValue> {
        if self.version == TlcVersion::V1_7_4 {
            return Err(not_yet("TLC 1.7.4's sets of records"));
        }
        let fields = self.get_sorted_fields(fields)?;
        let mut sets = Vec::new();
        for field in &fields {
            sets.push(get_elements(self.evaluate(&field.value, scope)?)?);
        }
        let total = sets
            .iter()
            .try_fold(1_i64, |product, set| product.checked_mul(set.len() as i64))
            .filter(|total| *total <= MAXIMUM_ELEMENTS)
            .ok_or_else(|| not_yet("a set of records too large to list"))?;
        let mut records = Vec::with_capacity(total as usize);
        for mut count in 0..total as usize {
            let mut values = vec![ConfigValue::Boolean(false); sets.len()];
            for (index, set) in sets.iter().enumerate().rev() {
                values[index] = set[count % set.len()].clone();
                count /= set.len();
            }
            records.push(ConfigValue::Record(
                fields
                    .iter()
                    .map(|field| field.name.to_string())
                    .zip(values)
                    .collect(),
            ));
        }
        self.create_set(records)
    }

    /// The elements of a set in the order TLC's quantifiers visit them: the normalized set's,
    /// as `getQuantifierElements` gives them after TLC 1.7.4.
    pub fn get_set_elements(
        &self,
        expression: &Expr,
        scope: Option<&Rc<Scope>>,
    ) -> Result<Vec<ConfigValue>> {
        if self.version == TlcVersion::V1_7_4 {
            return Err(not_yet("TLC 1.7.4's streamed sets"));
        }
        // `enumerateSet`: TLC can't list the functions of a domain it knows only by name.
        if let ExpressionKind::FunctionSet { domain, range } = &expression.kind
            && let Some(infinite) = self.get_infinite(domain)
        {
            let is_empty = self.get_infinite(range).is_none()
                && get_elements(self.evaluate(range, scope)?)?.is_empty();
            if is_empty {
                return Ok(Vec::new());
            }
            let name = match infinite {
                Infinite::Nat => "Nat",
                Infinite::Int => "Int",
                Infinite::String => "STRING",
            };
            return Err(FrontError::Evaluation(format!(
                "Attempted to enumerate a set of the form [D -> R],but the domain D:\n{name}\ncannot be enumerated."
            )));
        }
        get_elements(self.evaluate(expression, scope)?)
    }

    /// Whether a constant formula holds.
    pub fn is_true(&self, expression: &Expr, scope: Option<&Rc<Scope>>) -> Result<bool> {
        get_boolean(&self.evaluate(expression, scope)?)
    }

    /// The value a name has where nothing binds it locally: a configuration's value, a
    /// definition's, or a builtin's.
    fn evaluate_global(&self, name: &str) -> Result<ConfigValue> {
        let environment = self.environment;
        if environment.variable_index.contains_key(name) {
            return Err(not_yet("a variable"));
        }
        if let Some(value) = environment.constants.get(name) {
            return Ok(value.clone());
        }
        if let Some(definition) = get_definition(name, environment) {
            return match &definition.kind {
                DefinitionKind::Operator { params, .. } if params.is_empty() => {
                    self.evaluate_definition(definition)
                }
                _ => Err(not_yet("an operator or a function definition as a value")),
            };
        }
        match self.get_builtin_name(name) {
            "TRUE" => Ok(ConfigValue::Boolean(true)),
            "FALSE" => Ok(ConfigValue::Boolean(false)),
            "BOOLEAN" => self.create_set(vec![
                ConfigValue::Boolean(false),
                ConfigValue::Boolean(true),
            ]),
            _ => Err(not_yet("a builtin's value")),
        }
    }

    /// The value of a definition without parameters, computed once where its computation has no
    /// effect the evaluator counts or notes: a value it computed (never a failure), without
    /// TLCSet, and without meeting a recursion too deep in a filter. Computing it again would
    /// nest as deep below the use as it did, which counts that depth as reached, so a use gets
    /// the kept value only where that stays short of `MAXIMUM_DEPTH`, as it did where it was
    /// computed, and computes it again elsewhere, as without it.
    fn evaluate_definition(&self, definition: &Rc<Definition>) -> Result<ConfigValue> {
        let key = Rc::as_ptr(definition) as usize;
        self.evaluate_kept(&self.definitions, key, definition, || {
            self.evaluate(&definition.body, None)
        })
    }

    /// `evaluate_definition`'s keeping, of the values `kept` holds by `key`, which `compute`
    /// computes.
    fn evaluate_kept<K: std::hash::Hash + Eq>(
        &self,
        kept: &RefCell<HashMap<K, KeptDefinition>>,
        key: K,
        definition: &Rc<Definition>,
        compute: impl FnOnce() -> Result<ConfigValue>,
    ) -> Result<ConfigValue> {
        let depth = self.depth.get();
        let is_short = |span: usize| depth + span + 1 < MAXIMUM_DEPTH;
        if let Some(kept) = kept.borrow().get(&key)
            && kept.computes_tlc_set == self.computes_tlc_set
            && is_short(kept.span)
        {
            self.deepest.set(self.deepest.get().max(depth + kept.span));
            return Ok(kept.value.clone());
        }
        let tlc_sets = self.tlc_sets.get();
        let was_too_deep = MEMBERSHIP_TOO_DEEP.with(Cell::get);
        let deepest = self.deepest.replace(depth);
        let value = compute();
        let span = self.deepest.get() - depth;
        self.deepest.set(deepest.max(self.deepest.get()));
        if let Ok(value) = &value
            && is_short(span)
            && self.tlc_sets.get() == tlc_sets
            && !was_too_deep
            && !MEMBERSHIP_TOO_DEEP.with(Cell::get)
        {
            kept.borrow_mut().insert(
                key,
                KeptDefinition {
                    _definition: definition.clone(),
                    value: value.clone(),
                    span,
                    computes_tlc_set: self.computes_tlc_set,
                },
            );
        }
        value
    }

    /// An operator's body, with each parameter bound to its argument, which it computes where the
    /// body first uses it (`LazyValue`).
    fn apply_closure(
        &self,
        params: &[OperatorParam],
        body: &Expr,
        closure_scope: Option<Rc<Scope>>,
        args: &[Expr],
        scope: Option<&Rc<Scope>>,
    ) -> Result<ConfigValue> {
        let mut bound = closure_scope;
        for (param, argument) in params.iter().zip(args) {
            if param.arity > 0 {
                return Err(not_yet("an operator argument"));
            }
            bound = Some(Rc::new(Scope {
                name: param.name.clone(),
                binding: Binding::Thunk {
                    expression: argument.clone(),
                    scope: ScopeOf::Other(scope.cloned()),
                },
                parent: bound,
            }));
        }
        self.evaluate(body, bound.as_ref())
    }

    /// The value of an argument known without computing anything: a literal, or a name bound to
    /// a value, to a thunk computed already or to a thunk of an argument so known.
    fn get_known_argument(
        &self,
        expression: &Expr,
        scope: Option<&Rc<Scope>>,
        steps: usize,
    ) -> Option<ConfigValue> {
        match &expression.kind {
            ExpressionKind::Number { value, .. } if value.fract() == 0.0 => {
                to_integer(*value as i64).ok()
            }
            ExpressionKind::String { value } => Some(ConfigValue::String(value.to_string())),
            ExpressionKind::Identifier { .. } if expression.is_locally_resolved() && steps > 0 => {
                let name = expression.reference()?;
                match lookup_scope(scope, &name)? {
                    (_, Binding::Value(value) | Binding::Literal { value, .. }) => {
                        Some(value.clone())
                    }
                    (node, Binding::Thunk { expression, scope }) => {
                        let key = Rc::as_ptr(node) as usize;
                        if let Some((_, value)) = self.thunks.borrow().get(&key) {
                            return Some(value.clone());
                        }
                        self.get_known_argument(expression, scope.resolve(node).as_ref(), steps - 1)
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// A named set TLC can't list, which `\in` still tests.
    fn get_infinite(&self, expression: &Expr) -> Option<Infinite> {
        let ExpressionKind::Identifier { .. } = &expression.kind else {
            return None;
        };
        if expression.is_locally_resolved() {
            return None;
        }
        let name = expression.reference()?;
        if get_definition(&name, self.environment).is_some()
            || self.environment.constants.contains_key(&*name)
        {
            return None;
        }
        match self.get_builtin_name(&name) {
            "Nat" => Some(Infinite::Nat),
            "Int" => Some(Infinite::Int),
            "STRING" => Some(Infinite::String),
            _ => None,
        }
    }

    /// The builtin a name stands for, which the configuration may replace with another.
    fn get_builtin_name<'b>(&'b self, name: &'b str) -> &'b str {
        if self.environment.operator_objects.is_admitted
            && let Some(method) = self.environment.operator_objects.method_aliases.get(name)
        {
            return &method.builtin.name;
        }
        let target = self
            .environment
            .substitutions
            .get(name)
            .map_or(name, |target| &**target);
        self.environment
            .builtins
            .get(target)
            .map_or(target, |builtin| {
                if builtin.intrinsic == Some(crate::environment::Intrinsic::StandardMethod) {
                    return &builtin.name;
                }
                if builtin.intrinsic == Some(crate::environment::Intrinsic::DefnsBuiltin)
                    && builtin.flags
                        & (tla_ir::Builtin::EXTERNAL_CLASS | tla_ir::Builtin::DECLINED) as u32
                        == 0
                {
                    &builtin.name
                } else {
                    target
                }
            })
    }

    /// `S.member(e)` of `e \in S`, which an integer, a string or a boolean S fails with both
    /// values' texts.
    fn is_element(
        &self,
        element: &ConfigValue,
        set: &Expr,
        scope: Option<&Rc<Scope>>,
    ) -> Result<bool> {
        let reason = match self.is_member(element, set, scope) {
            Err(FrontError::NotYet(reason))
                if self.get_infinite(set).is_none()
                    && !note_too_deep(&reason, self.filtering.get()) =>
            {
                reason
            }
            is_member => return is_member,
        };
        let value = self.evaluate(set, scope)?;
        let kind = match &value {
            ConfigValue::Number(_) => "integer",
            ConfigValue::String(_) => "string",
            ConfigValue::Boolean(_) => "boolean",
            _ => return Err(FrontError::NotYet(reason)),
        };
        match (format_scalar(element), format_scalar(&value)) {
            (Some(element), Some(value))
                if element.len() <= MAXIMUM_PLAIN_TEXT && value.len() <= MAXIMUM_PLAIN_TEXT =>
            {
                Err(FrontError::Evaluation(format!(
                    "Attempted to check if the value:\n{element}\nis an element of the {kind} {value}"
                )))
            }
            _ => Err(FrontError::NotYet(reason)),
        }
    }

    fn is_member(
        &self,
        element: &ConfigValue,
        set: &Expr,
        scope: Option<&Rc<Scope>>,
    ) -> Result<bool> {
        match self.get_infinite(set) {
            Some(Infinite::Nat) => Ok(get_integer(element)? >= 0),
            Some(Infinite::Int) => get_integer(element).map(|_| true),
            Some(Infinite::String) => match element {
                ConfigValue::String(_) => Ok(true),
                _ => Err(not_yet("a value tested against STRING")),
            },
            None => {
                for member in get_elements(self.evaluate(set, scope)?)? {
                    if self.equals(element, &member)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
        }
    }

    /// Each binding of the bounds to their sets' elements, the last bound outermost, as
    /// `forEachBoundElement` visits them, and as `Tool.contexts` enumerates them for a quantifier
    /// or a set of the form {e : x \in S}.
    /// `Tool.contexts` as `Liveness.astToLive` unrolls a temporal formula's quantifier over a
    /// constant set: a bound TLC knows only by name, such as Nat, isn't enumerable.
    pub fn get_temporal_bindings(
        &self,
        bounds: &[Bound],
        scope: Option<&Rc<Scope>>,
    ) -> Result<Vec<Option<Rc<Scope>>>> {
        if self.version == TlcVersion::Master
            && let Some(first) = bounds
                .iter()
                .position(|bound| self.get_infinite(&bound.set).is_some())
        {
            // `contexts` evaluates and tests each bound in turn.
            self.bind(&bounds[..first], scope, true)?;
            if let Some(bound) = bounds.get(first)
                && let Some(infinite) = self.get_infinite(&bound.set)
            {
                let range = describe_range(&bound.set);
                return Err(FrontError::Evaluation(match infinite {
                    Infinite::String => format!(
                        "TLC encountered a non-enumerable quantifier bound\nSTRING.\n{range}"
                    ),
                    Infinite::Nat | Infinite::Int => {
                        let text = if matches!(infinite, Infinite::Nat) {
                            "Nat"
                        } else {
                            "Int"
                        };
                        format!(
                            "TLC encountered the non-enumerable quantifier bound\n{text}\n{range}\nThe set {text} contains infinitely many elements. As a result, TLC cannot evaluate expressions that\nuniversally (\\A) or existentially (\\E) quantify over {text}, because this would require checking an\ninfinite number of cases. Note that TLC handles set membership like T \\subseteq {text} for any finite set T."
                        )
                    }
                }));
            }
        }
        self.get_bindings(bounds, scope)
    }

    pub fn get_bindings(
        &self,
        bounds: &[Bound],
        scope: Option<&Rc<Scope>>,
    ) -> Result<Vec<Option<Rc<Scope>>>> {
        self.bind(bounds, scope, true)
    }

    fn bind(
        &self,
        bounds: &[Bound],
        scope: Option<&Rc<Scope>>,
        is_contexts: bool,
    ) -> Result<Vec<Option<Rc<Scope>>>> {
        let mut names = Vec::new();
        let mut sets = Vec::new();
        for bound in bounds {
            names.push(match &bound.pattern {
                BoundPattern::Name { name, .. } => Some(name.clone()),
                _ if is_contexts => None,
                _ => return Err(not_yet("a tuple of bound names")),
            });
            sets.push(match self.get_set_elements(&bound.set, scope) {
                // `Tool.contexts` fails on a bound that isn't a set with the value's text and the
                // bound's, a numeral's as it is written.
                Err(FrontError::NotYet(reason))
                    if is_contexts && self.version == TlcVersion::Master && !note_too_deep(&reason, self.filtering.get()) =>
                {
                    let value = self.evaluate(&bound.set, scope)?;
                    let text = match &bound.set.kind {
                        ExpressionKind::Number { text, .. }
                            if text.chars().all(|character| character.is_ascii_digit()) =>
                        {
                            text.to_string()
                        }
                        _ => describe_range(&bound.set),
                    };
                    return Err(match format_scalar(&value) {
                        Some(value) if value.len() <= MAXIMUM_PLAIN_TEXT => {
                            FrontError::Evaluation(format!(
                                "TLC encountered a non-enumerable quantifier bound\n{value}.\n{text}"
                            ))
                        }
                        _ => FrontError::NotYet(reason),
                    });
                }
                elements => elements?,
            });
        }
        if sets.iter().any(Vec::is_empty) {
            return Ok(Vec::new());
        }
        let names = names
            .into_iter()
            .collect::<Option<Vec<_>>>()
            .ok_or_else(|| not_yet("a tuple of bound names"))?;
        let mut bindings = Vec::new();
        fn visit(
            index: usize,
            bound: Option<Rc<Scope>>,
            names: &[Name],
            sets: &[Vec<ConfigValue>],
            bindings: &mut Vec<Option<Rc<Scope>>>,
        ) {
            let Some(index) = index.checked_sub(1) else {
                bindings.push(bound);
                return;
            };
            for element in &sets[index] {
                let scope = Rc::new(Scope {
                    name: names[index].clone(),
                    binding: Binding::Value(element.clone()),
                    parent: bound.clone(),
                });
                visit(index, Some(scope), names, sets, bindings);
            }
        }
        visit(bounds.len(), scope.cloned(), &names, &sets, &mut bindings);
        Ok(bindings)
    }

    fn apply_operator(
        &self,
        name: &str,
        args: &[Expr],
        scope: Option<&Rc<Scope>>,
    ) -> Result<ConfigValue> {
        let value = |index: usize| self.evaluate(&args[index], scope);
        let integers =
            || -> Result<(i64, i64)> { Ok((get_integer(&value(0)?)?, get_integer(&value(1)?)?)) };
        let booleans =
            || -> Result<(bool, bool)> { Ok((get_boolean(&value(0)?)?, get_boolean(&value(1)?)?)) };
        let sets = || -> Result<(Vec<ConfigValue>, Vec<ConfigValue>)> {
            Ok((get_elements(value(0)?)?, get_elements(value(1)?)?))
        };
        let arity = args.len();
        Ok(match (get_canonical_name(name), arity) {
            // `TLCGetSet.TLCSet` with neither a checker nor a simulator: a number fails to set
            // the simulator's registers (a NullPointerException), "exit", "pause" and a named
            // register leave nothing to stop, prompt or set, a system property is set, and any
            // other key is TLC_MODULE_ARGUMENT_ERROR. Java computes both arguments first.
            ("TLCSet", 2) if self.computes_tlc_set => {
                let (key, _) = (value(0)?, value(1)?);
                self.tlc_sets.set(self.tlc_sets.get() + 1);
                return match key {
                    ConfigValue::String(key)
                        if key == "exit" || key == "pause" || key.starts_with("s:") =>
                    {
                        Ok(ConfigValue::Boolean(true))
                    }
                    ConfigValue::String(key) if key.starts_with("-D") => {
                        Err(not_yet("TLCSet of a system property"))
                    }
                    _ => Err(FrontError::Evaluation(
                        "TLCSet as TLC starts, which fails there".to_owned(),
                    )),
                };
            }
            // `TLC.Assert`, whose arguments Java computes first, as TLC computes it as it starts:
            // TRUE, or a failure.
            ("Assert", 2) if self.computes_tlc_set => {
                let (condition, _) = (value(0)?, value(1)?);
                return match condition {
                    ConfigValue::Boolean(true) => Ok(ConfigValue::Boolean(true)),
                    _ => Err(FrontError::Evaluation(
                        "Assert as TLC starts, which fails there".to_owned(),
                    )),
                };
            }
            // TLCGetSet.TLCGetEval fails on the keys and registers TLC's model checker holds
            // before it exists, and reads the level of TLCState.Empty, the initial level.
            ("TLCGet", 1) if !self.is_started && self.version == TlcVersion::Master => {
                let key = match value(0)? {
                    ConfigValue::String(key) if key == "level" => {
                        return Ok(ConfigValue::Number(1.0));
                    }
                    ConfigValue::String(key) if CHECKER_KEYS.contains(&key.as_str()) => key,
                    ConfigValue::Number(index) if index >= 0.0 => index.to_string(),
                    _ => return Err(not_yet("TLCGet")),
                };
                return Err(FrontError::Evaluation(format!(
                    "Attempted to apply the operator overridden by the Java method\n{TLC_GET_EVAL},\nbut it produced the following error:\nTLCGet({key}) was undefined."
                )));
            }
            ("+", 2) => {
                let (left, right) = integers()?;
                to_integer(left + right)?
            }
            ("-", 2) => {
                let (left, right) = integers()?;
                to_integer(left - right)?
            }
            ("*", 2) => {
                let (left, right) = integers()?;
                to_integer(left * right)?
            }
            ("-.", 1) => to_integer(-get_integer(&value(0)?)?)?,
            // The evaluator holds no functions, but TLC computes the argument first.
            ("DOMAIN", 1) => {
                value(0)?;
                return Err(not_yet("DOMAIN"));
            }
            ("^", 2) => {
                let (base, exponent) = integers()?;
                if exponent < 0 || (base == 0 && exponent == 0) {
                    return Err(not_yet("an exponent TLC rejects"));
                }
                let power = match base {
                    -1 => 1 - 2 * (exponent % 2),
                    0 | 1 => base,
                    _ => u32::try_from(exponent)
                        .ok()
                        .and_then(|exponent| base.checked_pow(exponent))
                        .ok_or_else(|| not_yet("an integer TLC overflows"))?,
                };
                to_integer(power)?
            }
            ("\\div", 2) => {
                let (left, right) = integers()?;
                if right == 0 {
                    // Naturals.Divide's EvalException.
                    return Err(FrontError::Evaluation(
                        "The second argument of \\div is 0.".to_owned(),
                    ));
                }
                to_integer(
                    left.div_euclid(right) - i64::from(right < 0 && left.rem_euclid(right) != 0),
                )?
            }
            ("%", 2) => {
                let (left, right) = integers()?;
                if right <= 0 {
                    return Err(not_yet("a modulus that isn't positive"));
                }
                to_integer(left.rem_euclid(right))?
            }
            ("..", 2) => {
                let (low, high) = integers()?;
                if high - low >= MAXIMUM_ELEMENTS {
                    return Err(not_yet("an interval too large to list"));
                }
                ConfigValue::Set(
                    (low..=high)
                        .map(|number| ConfigValue::Number(number as f64))
                        .collect(),
                )
            }
            ("<", 2) => {
                let (left, right) = integers()?;
                ConfigValue::Boolean(left < right)
            }
            (">", 2) => {
                let (left, right) = integers()?;
                ConfigValue::Boolean(left > right)
            }
            ("\\leq", 2) => {
                let (left, right) = integers()?;
                ConfigValue::Boolean(left <= right)
            }
            ("\\geq", 2) => {
                let (left, right) = integers()?;
                ConfigValue::Boolean(left >= right)
            }
            ("=", 2) => ConfigValue::Boolean(self.equals_operands(args, scope)?),
            ("/=", 2) => ConfigValue::Boolean(!self.equals_operands(args, scope)?),
            ("\\in", 2) => ConfigValue::Boolean(self.is_element(&value(0)?, &args[1], scope)?),
            ("\\notin", 2) => {
                ConfigValue::Boolean(!self.is_element(&value(0)?, &args[1], scope)?)
            }
            ("\\subseteq", 2) => {
                let left = get_elements(value(0)?)?;
                let mut is_subset = true;
                for element in &left {
                    if !self.is_member(element, &args[1], scope)? {
                        is_subset = false;
                        break;
                    }
                }
                ConfigValue::Boolean(is_subset)
            }
            ("\\union", 2) => {
                let (mut left, right) = sets()?;
                left.extend(right);
                self.create_set(left)?
            }
            ("\\intersect", 2) => {
                let (left, right) = sets()?;
                let mut both = Vec::new();
                for element in left {
                    let mut is_in = false;
                    for other in &right {
                        if self.equals(&element, other)? {
                            is_in = true;
                            break;
                        }
                    }
                    if is_in {
                        both.push(element);
                    }
                }
                self.create_set(both)?
            }
            ("\\", 2) => {
                let (left, right) = sets()?;
                let mut rest = Vec::new();
                for element in left {
                    let mut is_in = false;
                    for other in &right {
                        if self.equals(&element, other)? {
                            is_in = true;
                            break;
                        }
                    }
                    if !is_in {
                        rest.push(element);
                    }
                }
                self.create_set(rest)?
            }
            ("Cardinality", 1) => to_integer(get_elements(value(0)?)?.len() as i64)?,
            ("\\lnot", 1) => ConfigValue::Boolean(!get_boolean(&value(0)?)?),
            ("\\land", 2) => {
                ConfigValue::Boolean(get_boolean(&value(0)?)? && get_boolean(&value(1)?)?)
            }
            ("\\lor", 2) => {
                ConfigValue::Boolean(get_boolean(&value(0)?)? || get_boolean(&value(1)?)?)
            }
            ("=>", 2) => {
                ConfigValue::Boolean(!get_boolean(&value(0)?)? || get_boolean(&value(1)?)?)
            }
            ("\\equiv", 2) => {
                let (left, right) = booleans()?;
                ConfigValue::Boolean(left == right)
            }
            _ => return Err(not_yet("an operator")),
        })
    }

    /// `evaluate` of a constant expression read in a scope.
    /// The value of the thunk `node` binds, computed where it is first read and kept, as TLC's
    /// `LazyValue` keeps an operator's argument.
    pub fn evaluate_thunk(&self, node: &Rc<Scope>) -> Result<ConfigValue> {
        let Binding::Thunk { expression, scope } = &node.binding else {
            return Err(not_yet("an operator as a value"));
        };
        if let Some(value) = self.computed_thunk(node) {
            return Ok(value);
        }
        let value = self.evaluate(expression, scope.resolve(node).as_ref())?;
        self.thunks
            .borrow_mut()
            .insert(Rc::as_ptr(node) as usize, (node.clone(), value.clone()));
        Ok(value)
    }

    /// The value of the thunk `node` binds, where it has been read.
    pub fn computed_thunk(&self, node: &Rc<Scope>) -> Option<ConfigValue> {
        self.thunks
            .borrow()
            .get(&(Rc::as_ptr(node) as usize))
            .map(|(_, value)| value.clone())
    }

    pub fn evaluate(&self, expression: &Expr, scope: Option<&Rc<Scope>>) -> Result<ConfigValue> {
        // A definition that recurses without end overflows TLC's stack, which TLC words in ways
        // the front end doesn't follow.
        if self.depth.get() >= MAXIMUM_DEPTH {
            return Err(not_yet(TOO_DEEP));
        }
        self.depth.set(self.depth.get() + 1);
        self.deepest.set(self.deepest.get().max(self.depth.get()));
        let value = self.evaluate_expression(expression, scope);
        self.depth.set(self.depth.get() - 1);
        value
    }

    fn evaluate_expression(
        &self,
        expression: &Expr,
        scope: Option<&Rc<Scope>>,
    ) -> Result<ConfigValue> {
        match &expression.kind {
            ExpressionKind::Number { value, .. } if value.fract() == 0.0 => {
                to_integer(*value as i64)
            }
            ExpressionKind::String { value } => Ok(ConfigValue::String(value.to_string())),
            ExpressionKind::Identifier { .. } => {
                let name = expression.reference().unwrap_or_default();
                if expression.is_locally_resolved() {
                    return match lookup_scope(scope, &name) {
                        Some((_, Binding::Value(value) | Binding::Literal { value, .. })) => {
                            Ok(value.clone())
                        }
                        Some((node, Binding::Thunk { .. })) => self.evaluate_thunk(node),
                        _ => Err(not_yet("an operator as a value")),
                    };
                }
                if self.environment.variable_index.contains_key(&name) {
                    // TLC's Tool#evalAppl fails to look up a variable no state assigns.
                    return Err(FrontError::Evaluation(format!(
                        "In evaluation, the identifier {name} is either undefined or not an operator.\n{}",
                        describe_range(expression)
                    )));
                }
                self.evaluate_global(&name)
            }
            ExpressionKind::Apply { args, .. }
                if self.draws.borrow().is_some()
                    && args.len() == 1
                    && !expression.is_locally_resolved()
                    && expression.reference().as_deref() == Some("RandomElement")
                    && is_builtin_draw(self.environment, "RandomElement", "TLC") =>
            {
                // `TLC.RandomElement` of a finite set: the element the draw takes. Of `SUBSET S`,
                // `SubsetValue.randomElement` draws one of S's subsets, each of which the draws
                // take in turn.
                let elements = match &args[0].kind {
                    ExpressionKind::Apply {
                        operator,
                        args: bases,
                        ..
                    } if &**operator == "SUBSET"
                        && bases.len() == 1
                        && !args[0].is_locally_resolved() =>
                    {
                        let base = get_elements(self.evaluate(&bases[0], scope)?)?;
                        if base.len() > MAXIMUM_DRAWN_BASE {
                            return Err(not_yet("a power set too large to draw from"));
                        }
                        self.get_subsets(&base, None)?
                    }
                    _ => get_elements(self.evaluate(&args[0], scope)?)?,
                };
                self.take_draw(elements)
            }
            // `Randomization.RandomSubset(k, S)` of a natural k at most the size of a finite set S
            // (`EnumerableValue.getRandomSubset`): one of S's subsets of k elements, each of which
            // the draws take in turn.
            ExpressionKind::Apply { args, .. }
                if self.draws.borrow().is_some()
                    && args.len() == 2
                    && !expression.is_locally_resolved()
                    && expression.reference().as_deref() == Some("RandomSubset")
                    && is_builtin_draw(self.environment, "RandomSubset", "Randomization") =>
            {
                let ConfigValue::Number(count) = self.evaluate(&args[0], scope)? else {
                    return Err(not_yet("RandomSubset of a count that isn't a number"));
                };
                let base = get_elements(self.evaluate(&args[1], scope)?)?;
                if count.fract() != 0.0
                    || count < 0.0
                    || count > base.len() as f64
                    || base.len() > MAXIMUM_DRAWN_BASE
                {
                    return Err(not_yet("RandomSubset the evaluator doesn't draw"));
                }
                let elements = self.get_subsets(&base, Some(count as usize))?;
                self.take_draw(elements)
            }
            ExpressionKind::Apply { args, .. } => {
                let name = expression.reference().unwrap_or_default();
                let closure = if expression.is_locally_resolved() {
                    match lookup_scope(scope, &name) {
                        Some((
                            node,
                            Binding::Closure {
                                params,
                                body,
                                scope: closure_scope,
                                ..
                            },
                        )) => Some((params.clone(), body.clone(), closure_scope.resolve(node))),
                        _ => return Err(not_yet("an operator a scope doesn't bind")),
                    }
                } else {
                    match get_definition(&name, self.environment).map(|definition| &definition.kind)
                    {
                        Some(DefinitionKind::Operator { params, .. }) => Some((
                            params.clone(),
                            get_definition(&name, self.environment)
                                .map(|definition| definition.body.clone())
                                .expect("a definition"),
                            None,
                        )),
                        Some(DefinitionKind::Function { .. }) => {
                            return Err(not_yet("a function definition applied"));
                        }
                        None => None,
                    }
                };
                let Some((params, body, closure_scope)) = closure else {
                    return self.apply_operator(self.get_builtin_name(&name), args, scope);
                };
                // A definition applied to arguments whose values are known, again: its value
                // is the same, where computing it had no effect (`evaluate_kept`). The draws a
                // computation makes are its effects.
                if !expression.is_locally_resolved()
                    && self.draws.borrow().is_none()
                    && params.len() == args.len()
                    && params.iter().all(|param| param.arity == 0)
                    && let Some(definition) = get_definition(&name, self.environment)
                    && let Some(values) = args
                        .iter()
                        .map(|argument| self.get_known_argument(argument, scope, 64))
                        .collect::<Option<Vec<_>>>()
                {
                    let key = (Rc::as_ptr(definition) as usize, format!("{values:?}"));
                    return self.evaluate_kept(&self.applications, key, definition, || {
                        self.apply_closure(&params, &body, closure_scope, args, scope)
                    });
                }
                self.apply_closure(&params, &body, closure_scope, args, scope)
            }
            ExpressionKind::Junction {
                is_and, operands, ..
            } => {
                for operand in operands {
                    if get_boolean(&self.evaluate(operand, scope)?)? != *is_and {
                        return Ok(ConfigValue::Boolean(!is_and));
                    }
                }
                Ok(ConfigValue::Boolean(*is_and))
            }
            ExpressionKind::If {
                condition,
                consequent,
                alternative,
            } => {
                if self.is_true(condition, scope)? {
                    self.evaluate(consequent, scope)
                } else {
                    self.evaluate(alternative, scope)
                }
            }
            ExpressionKind::Let {
                definitions, body, ..
            } => {
                let bound = bind_definitions(definitions, scope)?;
                self.evaluate(body, bound.as_ref())
            }
            ExpressionKind::Record {
                is_set: false,
                fields,
            } => {
                let mut values = Vec::new();
                for field in self.get_sorted_fields(fields)? {
                    values.push((field.name.to_string(), self.evaluate(&field.value, scope)?));
                }
                Ok(ConfigValue::Record(values))
            }
            ExpressionKind::Record {
                is_set: true,
                fields,
            } => self.get_records(fields, scope),
            ExpressionKind::FieldAccess { record, field } => match self.evaluate(record, scope)? {
                ConfigValue::Record(fields) => fields
                    .into_iter()
                    .find(|(name, _)| **name == **field)
                    .map(|(_, value)| value)
                    .ok_or_else(|| not_yet("a record's missing field")),
                _ => Err(not_yet("a field of a value that isn't a record")),
            },
            ExpressionKind::Case { arms, other } => {
                for arm in arms {
                    if self.is_true(&arm.condition, scope)? {
                        return self.evaluate(&arm.body, scope);
                    }
                }
                match other {
                    Some(other) => self.evaluate(other, scope),
                    None => Err(not_yet("a CASE none of whose arms holds")),
                }
            }
            ExpressionKind::Choose {
                pattern: BoundPattern::Name { name, .. },
                set: Some(set),
                body,
            } => {
                for element in self.get_set_elements(set, scope)? {
                    let bound = Rc::new(Scope {
                        name: name.clone(),
                        binding: Binding::Value(element.clone()),
                        parent: scope.cloned(),
                    });
                    if self.is_true(body, Some(&bound))? {
                        return Ok(element);
                    }
                }
                Err(FrontError::Evaluation(format!(
                    "Attempted to compute the value of an expression of form\nCHOOSE x \\in S: P, but no element of S satisfied P.\n{}",
                    describe_range(expression)
                )))
            }
            ExpressionKind::SetEnumeration(elements) => {
                let elements = elements
                    .iter()
                    .map(|element| self.evaluate(element, scope))
                    .collect::<Result<Vec<_>>>()?;
                self.create_set(elements)
            }
            ExpressionKind::Quantified {
                quantifier,
                bounds,
                body,
            } => {
                let is_forall = *quantifier == Quantifier::Forall;
                for binding in self.get_bindings(bounds, scope)? {
                    if self.is_true(body, binding.as_ref())? != is_forall {
                        return Ok(ConfigValue::Boolean(!is_forall));
                    }
                }
                Ok(ConfigValue::Boolean(is_forall))
            }
            ExpressionKind::SetFilter { bound, predicate } => {
                let mut kept = Vec::new();
                // TLC keeps {x \in S : P} lazy where S isn't a set.
                for binding in self.bind(std::slice::from_ref(bound), scope, false)? {
                    self.filtering.set(self.filtering.get() + 1);
                    let is_kept = self.is_true(predicate, binding.as_ref());
                    self.filtering.set(self.filtering.get() - 1);
                    if is_kept? {
                        let Some(node) = &binding else {
                            continue;
                        };
                        let Binding::Value(element) = &node.binding else {
                            continue;
                        };
                        kept.push(element.clone());
                    }
                }
                self.create_set(kept)
            }
            ExpressionKind::SetMap {
                expression: mapped,
                bounds,
            } => {
                let mut elements = Vec::new();
                for binding in self.get_bindings(bounds, scope)? {
                    elements.push(self.evaluate(mapped, binding.as_ref())?);
                }
                self.create_set(elements)
            }
            ExpressionKind::Label { body, .. } => self.evaluate(body, scope),
            // `Tool#evalAppl` fails on a temporal operator before it evaluates its operands.
            ExpressionKind::Always(_)
            | ExpressionKind::Eventually(_)
            | ExpressionKind::Fairness { .. } => {
                let operator = match &expression.kind {
                    ExpressionKind::Always(_) => "[]A",
                    ExpressionKind::Eventually(_) => "<>A",
                    ExpressionKind::Fairness {
                        is_strong: false, ..
                    } => "WF",
                    _ => "SF",
                };
                Err(FrontError::Evaluation(format!(
                    "TLC encountered a temporal formula ({operator}) when evaluating a predicate or action.\n{}",
                    describe_range(expression)
                )))
            }
            // `Tool`'s OPCODE_fa computes the function first, whose failure is the application's.
            // The evaluator holds no functions.
            ExpressionKind::FunctionApplication { function, .. } => {
                self.evaluate(function, scope)?;
                Err(not_yet("a function's application"))
            }
            _ => Err(not_yet("an expression")),
        }
    }
}
