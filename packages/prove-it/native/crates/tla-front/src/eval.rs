//! A small evaluator of the constant expressions the front end needs values of before the
//! search, as `evaluate` in `src/evaluate.ts` computes them: the sets TLC unrolls a property's or
//! a temporal formula's quantifier over, and the constant parts of a temporal formula. It knows
//! booleans, integers, strings, model values and finite sets of them, and returns `NotYet` for
//! anything else, which TLC's own evaluation at startup handles.

use std::cmp::Ordering;
use std::rc::Rc;

use crate::TlcVersion;
use crate::ast::*;
use crate::config::ConfigValue;
use crate::environment::Environment;
use crate::errors::FrontError;
use crate::resolve::Result;
use crate::spec::{Binding, Scope, bind_definitions, get_definition, lookup_scope};
use crate::tlc_data::SANY_OPERATOR_SYNONYMS;
use crate::values::{ValueOrder, get_model_value_type};

/// The most elements the evaluator lists of a set, past which TLC's run is the engine's.
const MAXIMUM_ELEMENTS: i64 = 100_000;

fn not_yet(reason: &str) -> FrontError {
    FrontError::NotYet(format!(
        "{reason}, which the constant evaluator doesn't compute"
    ))
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

/// The sets of numbers and strings TLC knows by name, which have no elements to list.
enum Infinite {
    Nat,
    Int,
    String,
}

pub struct Evaluator<'a> {
    pub environment: &'a Environment,
    pub order: ValueOrder<'a>,
    pub version: TlcVersion,
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
            | (ConfigValue::Set(_), ConfigValue::Set(_)) => {
                Ok(self.order.compare(left, right)? == Ordering::Equal)
            }
            _ => Err(not_yet("values TLC can't compare")),
        }
    }

    fn create_set(&self, elements: Vec<ConfigValue>) -> Result<ConfigValue> {
        self.order.normalize(&ConfigValue::Set(elements))
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
                    self.evaluate(&definition.body, None)
                }
                _ => Err(not_yet("an operator or a function definition as a value")),
            };
        }
        match name {
            "TRUE" => Ok(ConfigValue::Boolean(true)),
            "FALSE" => Ok(ConfigValue::Boolean(false)),
            "BOOLEAN" => self.create_set(vec![
                ConfigValue::Boolean(false),
                ConfigValue::Boolean(true),
            ]),
            _ => Err(not_yet("a builtin's value")),
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
        match &*name {
            "Nat" => Some(Infinite::Nat),
            "Int" => Some(Infinite::Int),
            "STRING" => Some(Infinite::String),
            _ => None,
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
    /// `forEachBoundElement` visits them.
    pub fn get_bindings(
        &self,
        bounds: &[Bound],
        scope: Option<&Rc<Scope>>,
    ) -> Result<Vec<Option<Rc<Scope>>>> {
        let mut names = Vec::new();
        let mut sets = Vec::new();
        for bound in bounds {
            let BoundPattern::Name { name, .. } = &bound.pattern else {
                return Err(not_yet("a tuple of bound names"));
            };
            names.push(name.clone());
            sets.push(self.get_set_elements(&bound.set, scope)?);
        }
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
            ("\\div", 2) => {
                let (left, right) = integers()?;
                if right == 0 {
                    return Err(not_yet("a division by zero"));
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
            ("=", 2) => ConfigValue::Boolean(self.equals(&value(0)?, &value(1)?)?),
            ("/=", 2) => ConfigValue::Boolean(!self.equals(&value(0)?, &value(1)?)?),
            ("\\in", 2) => ConfigValue::Boolean(self.is_member(&value(0)?, &args[1], scope)?),
            ("\\notin", 2) => ConfigValue::Boolean(!self.is_member(&value(0)?, &args[1], scope)?),
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
    pub fn evaluate(&self, expression: &Expr, scope: Option<&Rc<Scope>>) -> Result<ConfigValue> {
        match &expression.kind {
            ExpressionKind::Number { value, .. } if value.fract() == 0.0 => {
                to_integer(*value as i64)
            }
            ExpressionKind::String { value } => Ok(ConfigValue::String(value.to_string())),
            ExpressionKind::Identifier { .. } => {
                let name = expression.reference().unwrap_or_default();
                if expression.is_locally_resolved() {
                    return match lookup_scope(scope, &name) {
                        Some((_, Binding::Value(value))) => Ok(value.clone()),
                        Some((node, Binding::Thunk { expression, scope })) => {
                            self.evaluate(expression, scope.resolve(node).as_ref())
                        }
                        _ => Err(not_yet("an operator as a value")),
                    };
                }
                self.evaluate_global(&name)
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
                    return self.apply_operator(&name, args, scope);
                };
                let mut bound = closure_scope;
                for (param, argument) in params.iter().zip(args) {
                    if param.arity > 0 {
                        return Err(not_yet("an operator argument"));
                    }
                    bound = Some(Rc::new(Scope {
                        name: param.name.clone(),
                        binding: Binding::Value(self.evaluate(argument, scope)?),
                        parent: bound,
                    }));
                }
                self.evaluate(&body, bound.as_ref())
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
                for binding in self.get_bindings(std::slice::from_ref(bound), scope)? {
                    if self.is_true(predicate, binding.as_ref())? {
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
            _ => Err(not_yet("an expression")),
        }
    }
}
