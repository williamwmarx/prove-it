//! The temporal formula the liveness checker solves (`toLiveExpression` in `liveness.ts`, joined
//! as `createLivenessChecker` joins it): the fairness and the negated properties, their state,
//! action and ENABLED parts as atoms, and the atoms in the order the checker asks about them.

use std::collections::HashMap;
use std::rc::Rc;

use crate::TlcVersion;
use crate::ast::*;
use crate::config::ConfigValue;
use crate::dependencies::{DefinitionFacts, Level};
use crate::environment::Environment;
use crate::errors::FrontError;
use crate::eval::Evaluator;
use crate::resolve::Result;
use crate::spec::{
    Binding, Expanded, Property, Scope, ScopeOf, bind_definitions, bind_operator_arguments,
    get_definition, get_level, lookup_scope, resolve_apply_operator,
};

const MAXIMUM_EXPANSION_DEPTH: usize = 100;

/// A part of the formula (`LiveExpression`). An atom is itself: two atoms are the same just when
/// they are the same `Rc`, as two objects are in `liveness.ts`.
pub enum Live {
    Boolean(bool),
    State {
        expression: Expr,
        scope: Option<Rc<Scope>>,
    },
    Enabled {
        step: Expr,
        scope: Option<Rc<Scope>>,
    },
    /// An action, false of a step that leaves `unchanged` unchanged, with the ENABLED of its
    /// fairness.
    Action {
        expression: Expr,
        unchanged: Option<Expr>,
        scope: Option<Rc<Scope>>,
        enabled: Option<Rc<Live>>,
    },
    Not(Rc<Live>),
    Always(Rc<Live>),
    Eventually(Rc<Live>),
    Junction {
        is_and: bool,
        operands: Vec<Rc<Live>>,
    },
}

/// What the liveness checker checks: the formula it solves, each property with the formula whose
/// violation a counterexample shows, and the atoms in the order it asks about them.
pub struct Liveness {
    pub formula: Rc<Live>,
    pub properties: Vec<(Name, Rc<Live>)>,
    pub atoms: Vec<Rc<Live>>,
}

fn not_yet(reason: &str) -> FrontError {
    FrontError::NotYet(reason.to_owned())
}

/// `createJunction`: the operands, those of the same junction in their place.
fn junction(is_and: bool, operands: Vec<Rc<Live>>) -> Rc<Live> {
    let mut flat = Vec::with_capacity(operands.len());
    for operand in operands {
        match &*operand {
            Live::Junction {
                is_and: inner,
                operands,
            } if *inner == is_and => flat.extend(operands.iter().cloned()),
            _ => flat.push(operand),
        }
    }
    Rc::new(Live::Junction {
        is_and,
        operands: flat,
    })
}

fn pair(is_and: bool, left: Rc<Live>, right: Rc<Live>) -> Rc<Live> {
    Rc::new(Live::Junction {
        is_and,
        operands: vec![left, right],
    })
}

/// `getLiveLevel`.
fn live_level(live: &Live) -> Level {
    match live {
        Live::Boolean(_) => Level::Constant,
        Live::State { .. } | Live::Enabled { .. } => Level::Variable,
        Live::Action { .. } => Level::Action,
        Live::Not(body) => live_level(body),
        Live::Always(_) | Live::Eventually(_) => Level::Temporal,
        Live::Junction { operands, .. } => operands
            .iter()
            .map(|operand| live_level(operand))
            .max()
            .unwrap_or(Level::Constant),
    }
}

/// `toLiveExpression`.
struct Converter<'a> {
    environment: &'a Environment,
    facts: &'a DefinitionFacts,
    evaluator: Option<&'a Evaluator<'a>>,
    depth: usize,
}

impl Converter<'_> {
    fn level(&self, expression: &Expr, scope: Option<&Rc<Scope>>) -> Level {
        get_level(expression, scope, self.environment, self.facts, &[])
    }

    /// The evaluator, whose failures TLC words in ways the front end doesn't follow yet.
    fn get_evaluator(&self, reason: &str) -> Result<&Evaluator<'_>> {
        self.evaluator.ok_or_else(|| not_yet(reason))
    }

    /// A constant formula's value, or `None` where it isn't a boolean.
    fn evaluate_boolean(
        &self,
        expression: &Expr,
        scope: Option<&Rc<Scope>>,
        reason: &str,
    ) -> Result<Option<bool>> {
        match self.get_evaluator(reason)?.evaluate(expression, scope) {
            Ok(ConfigValue::Boolean(value)) => Ok(Some(value)),
            Ok(_) => Ok(None),
            Err(FrontError::Evaluation(_)) => Err(not_yet(reason)),
            Err(error) => Err(error),
        }
    }

    /// `toAtom`: TLC bounds the level of a formula whose parts are constant by the formula's own.
    fn atom(&self, expression: &Expr, scope: Option<&Rc<Scope>>, level: Level) -> Result<Rc<Live>> {
        let level = if level == Level::Constant {
            self.level(expression, scope)
        } else {
            level
        };
        Ok(Rc::new(match level {
            Level::Constant => {
                let reason = "a constant part of a temporal formula";
                return match self.evaluate_boolean(expression, scope, reason)? {
                    Some(value) => Ok(Rc::new(Live::Boolean(value))),
                    None => Err(not_yet(
                        "a constant part of a temporal formula that isn't a boolean",
                    )),
                };
            }
            Level::Variable => Live::State {
                expression: expression.clone(),
                scope: scope.cloned(),
            },
            _ => Live::Action {
                expression: expression.clone(),
                unchanged: None,
                scope: scope.cloned(),
                enabled: None,
            },
        }))
    }

    /// `toWhole`: a formula whose translated parts are below temporal level is an atom whole.
    fn whole(
        &self,
        expression: &Expr,
        scope: Option<&Rc<Scope>>,
        parts: Rc<Live>,
    ) -> Result<Rc<Live>> {
        let level = live_level(&parts);
        if level > Level::Action {
            Ok(parts)
        } else {
            self.atom(expression, scope, level)
        }
    }

    /// `expand`: an operator's body, an atom of the application where it isn't temporal.
    fn expand(
        &mut self,
        body: &Expr,
        body_scope: Option<&Rc<Scope>>,
        expression: &Expr,
        scope: Option<&Rc<Scope>>,
    ) -> Result<Rc<Live>> {
        if self.depth >= MAXIMUM_EXPANSION_DEPTH {
            return Err(not_yet("a temporal formula expanded too deep"));
        }
        self.depth += 1;
        let result = self.convert(body, body_scope);
        self.depth -= 1;
        self.whole(expression, scope, result?)
    }

    /// `convertCall`: a definition of a LET or an operator, expanded.
    fn call(&mut self, expression: &Expr, scope: Option<&Rc<Scope>>) -> Result<Rc<Live>> {
        let name = expression.reference().unwrap_or_default();
        let is_local = expression.is_locally_resolved();
        let binding = if is_local || get_definition(&name, self.environment).is_none() {
            lookup_scope(scope, &name)
        } else {
            None
        };
        if let Some((
            node,
            Binding::Thunk {
                expression: body,
                scope: definition_scope @ ScopeOf::Own,
            },
        )) = binding
        {
            let body_scope = definition_scope.resolve(node);
            return self.expand(body, body_scope.as_ref(), expression, scope);
        }
        let cannot_handle = || not_yet("a temporal formula TLC can't handle");
        if binding.is_some_and(|(_, binding)| !matches!(binding, Binding::Closure { .. })) {
            return Err(cannot_handle());
        }
        let (params, body, closure_scope) =
            resolve_apply_operator(expression, scope, self.environment)
                .ok_or_else(cannot_handle)?;
        let args = match &expression.kind {
            ExpressionKind::Apply { args, .. } => &args[..],
            _ => &[],
        };
        let bound = bind_operator_arguments(&params, args, closure_scope, scope, self.environment)?;
        self.expand(&body, bound.as_ref(), expression, scope)
    }

    // The formulas below temporal level whose parts TLC's Liveness.astToLive translates, as one
    // that is constant, such as a quantifier over the empty set, can make the formula constant.
    fn is_translated_whole(expression: &Expr) -> bool {
        match &expression.kind {
            ExpressionKind::Label { .. }
            | ExpressionKind::Let { .. }
            | ExpressionKind::Junction { .. }
            | ExpressionKind::Quantified { .. }
            | ExpressionKind::If { .. } => true,
            ExpressionKind::Apply { operator, .. } => {
                (&**operator == "~" && !expression.is_locally_resolved()) || &**operator == "=>"
            }
            _ => false,
        }
    }

    fn convert(&mut self, expression: &Expr, scope: Option<&Rc<Scope>>) -> Result<Rc<Live>> {
        let level = self.level(expression, scope);
        if level <= Level::Action && !Self::is_translated_whole(expression) {
            return self.atom(expression, scope, level);
        }
        match &expression.kind {
            ExpressionKind::Label { body, .. } => self.convert(body, scope),
            ExpressionKind::Let {
                definitions, body, ..
            } => {
                let bound = bind_definitions(definitions, scope)?;
                self.convert(body, bound.as_ref())
            }
            ExpressionKind::Identifier { .. } => self.call(expression, scope),
            ExpressionKind::Apply { operator, args, .. } => match &**operator {
                "~>" => {
                    let premise = self.convert(&args[0], scope)?;
                    let consequence = self.convert(&args[1], scope)?;
                    Ok(Rc::new(Live::Always(pair(
                        false,
                        Rc::new(Live::Not(premise)),
                        Rc::new(Live::Eventually(consequence)),
                    ))))
                }
                "~" if !expression.is_locally_resolved() => {
                    let body = self.convert(&args[0], scope)?;
                    self.whole(expression, scope, Rc::new(Live::Not(body)))
                }
                "=>" => {
                    let premise = self.convert(&args[0], scope)?;
                    let consequence = self.convert(&args[1], scope)?;
                    let parts = pair(false, Rc::new(Live::Not(premise)), consequence);
                    self.whole(expression, scope, parts)
                }
                _ => self.call(expression, scope),
            },
            ExpressionKind::Junction {
                is_and, operands, ..
            } => {
                let parts = operands
                    .iter()
                    .map(|operand| self.convert(operand, scope))
                    .collect::<Result<Vec<_>>>()?;
                self.whole(expression, scope, junction(*is_and, parts))
            }
            ExpressionKind::Quantified {
                quantifier,
                bounds,
                body,
            } => {
                let is_forall = *quantifier == Quantifier::Forall;
                let is_constant = bounds
                    .iter()
                    .all(|bound| self.level(&bound.set, scope) == Level::Constant);
                if !is_constant {
                    return if level <= Level::Action {
                        self.atom(expression, scope, level)
                    } else {
                        Err(not_yet("a temporal formula TLC can't handle"))
                    };
                }
                let reason = "a temporal quantifier over a set TLC fails to list";
                let bindings = match self.get_evaluator(reason)?.get_bindings(bounds, scope) {
                    Err(FrontError::Evaluation(_)) => return Err(not_yet(reason)),
                    bindings => bindings?,
                };
                let operands = bindings
                    .iter()
                    .map(|bound| self.convert(body, bound.as_ref()))
                    .collect::<Result<Vec<_>>>()?;
                if operands.is_empty() {
                    return Ok(Rc::new(Live::Boolean(is_forall)));
                }
                self.whole(expression, scope, junction(is_forall, operands))
            }
            ExpressionKind::If {
                condition,
                consequent,
                alternative,
            } => {
                if self.level(condition, scope) == Level::Constant {
                    let reason = "a temporal IF whose condition TLC fails to evaluate";
                    if let Some(value) = self.evaluate_boolean(condition, scope, reason)? {
                        return self.convert(if value { consequent } else { alternative }, scope);
                    }
                }
                let condition = self.convert(condition, scope)?;
                let consequent = self.convert(consequent, scope)?;
                let alternative = self.convert(alternative, scope)?;
                let parts = pair(
                    false,
                    pair(true, condition.clone(), consequent),
                    pair(true, Rc::new(Live::Not(condition)), alternative),
                );
                self.whole(expression, scope, parts)
            }
            ExpressionKind::Always(body) => Ok(Rc::new(Live::Always(self.convert(body, scope)?))),
            ExpressionKind::Eventually(body) => {
                Ok(Rc::new(Live::Eventually(self.convert(body, scope)?)))
            }
            ExpressionKind::Fairness {
                is_strong,
                subscript,
                action,
                enabled,
            } => {
                let location = action.location.clone();
                let step = Rc::new(Expression::new(
                    ExpressionKind::Action {
                        is_box: false,
                        action: action.clone(),
                        subscript: subscript.clone(),
                    },
                    location.clone(),
                ));
                let enabled = Rc::new(Live::Enabled {
                    step: enabled.clone().unwrap_or(step),
                    scope: scope.cloned(),
                });
                let disabled = Rc::new(Live::Not(enabled.clone()));
                let taken = Rc::new(Live::Action {
                    expression: action.clone(),
                    unchanged: Some(Rc::new(Expression::new(
                        ExpressionKind::Unchanged(subscript.clone()),
                        location,
                    ))),
                    scope: scope.cloned(),
                    enabled: Some(enabled),
                });
                Ok(if *is_strong {
                    pair(
                        false,
                        Rc::new(Live::Eventually(Rc::new(Live::Always(disabled)))),
                        Rc::new(Live::Always(Rc::new(Live::Eventually(taken)))),
                    )
                } else {
                    Rc::new(Live::Always(Rc::new(Live::Eventually(pair(
                        false, disabled, taken,
                    )))))
                })
            }
            _ => Err(not_yet("a temporal formula TLC can't handle")),
        }
    }
}

/// `createLivenessChecker`'s formula, properties and atoms, or none without temporal properties.
pub fn get_liveness(
    temporals: &[Expanded],
    properties: &[Property],
    environment: &Environment,
    facts: &DefinitionFacts,
    evaluator: Option<&Evaluator>,
    version: TlcVersion,
) -> Result<Option<Liveness>> {
    if properties.is_empty() {
        return Ok(None);
    }
    if version == TlcVersion::V1_7_4 {
        return Err(not_yet("temporal properties in TLC 1.7.4"));
    }
    let mut converter = Converter {
        environment,
        facts,
        evaluator,
        depth: 0,
    };
    let fairness = temporals
        .iter()
        .map(|temporal| converter.convert(&temporal.expression, temporal.scope.as_ref()))
        .collect::<Result<Vec<_>>>()?;
    let mut negations = Vec::with_capacity(properties.len());
    let mut named = Vec::with_capacity(properties.len());
    for property in properties {
        let formula = converter.convert(&property.expression, property.scope.as_ref())?;
        negations.push(Rc::new(Live::Not(formula.clone())));
        named.push((property.name.clone(), formula));
    }
    let violation = if negations.len() == 1 {
        negations.remove(0)
    } else {
        junction(false, negations)
    };
    let formula = if fairness.is_empty() {
        violation
    } else {
        junction(true, [fairness, vec![violation]].concat())
    };
    let atoms = order_atoms(&formula)?;
    Ok(Some(Liveness {
        formula,
        properties: named,
        atoms,
    }))
}

/// The atoms in the order the checker asks about them, as `tla_live::atom_order` finds it from the
/// solutions of the formula, each atom by its position among those of the formula.
fn order_atoms(formula: &Rc<Live>) -> Result<Vec<Rc<Live>>> {
    let mut atoms: Vec<Rc<Live>> = Vec::new();
    let mut ids: HashMap<*const Live, u32> = HashMap::new();
    let mut terms = Vec::new();
    write_terms(formula, &mut atoms, &mut ids, &mut terms);
    let order = tla_live::atom_order(&terms).map_err(|declined| match &*declined.0 {
        "a tautology" => not_yet("a temporal property that is a tautology"),
        _ => not_yet("a temporal formula the tableau declines"),
    })?;
    Ok(order
        .into_iter()
        .map(|id| atoms[id as usize].clone())
        .collect())
}

fn write_terms(
    live: &Rc<Live>,
    atoms: &mut Vec<Rc<Live>>,
    ids: &mut HashMap<*const Live, u32>,
    terms: &mut Vec<tla_live::Term>,
) {
    let mut id = |atom: &Rc<Live>| {
        *ids.entry(Rc::as_ptr(atom)).or_insert_with(|| {
            atoms.push(atom.clone());
            atoms.len() as u32 - 1
        })
    };
    match &**live {
        Live::Boolean(value) => terms.push(tla_live::Term::Boolean(*value)),
        Live::State { .. } => terms.push(tla_live::Term::State(id(live))),
        Live::Enabled { .. } => terms.push(tla_live::Term::Enabled(id(live))),
        Live::Action { enabled, .. } => {
            let atom = id(live);
            let enabled = enabled.as_ref().map(&mut id);
            terms.push(tla_live::Term::Action { atom, enabled });
        }
        Live::Not(body) | Live::Always(body) | Live::Eventually(body) => {
            terms.push(match &**live {
                Live::Not(_) => tla_live::Term::Not,
                Live::Always(_) => tla_live::Term::Always,
                _ => tla_live::Term::Eventually,
            });
            write_terms(body, atoms, ids, terms);
        }
        Live::Junction { is_and, operands } => {
            let count = operands.len() as u32;
            terms.push(if *is_and {
                tla_live::Term::And(count)
            } else {
                tla_live::Term::Or(count)
            });
            for operand in operands {
                write_terms(operand, atoms, ids, terms);
            }
        }
    }
}
