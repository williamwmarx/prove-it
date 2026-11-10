//! Whether the hypotheses make a relation reflexive, symmetric or transitive, which Zenon's rules
//! for relations other than = rely on. The property holds when no way for the relation to hold
//! among three elements satisfies the ground instances of the hypotheses and breaks the property.

use std::collections::HashMap;
use std::rc::Rc;

use super::terms::{CheckContext, RelationProperty};
use crate::expr::{Expr, Kind, UNIVERSE};

#[derive(Clone, Copy, PartialEq, Eq)]
enum Polarity {
    Positive,
    Negative,
    Both,
}

const ELEMENTS: [usize; 3] = [0, 1, 2];

// A hypothesis as a test on how a relation holds among three elements: `values` gives the bound
// variables their elements and bit 3 * i + j of `holds` says whether the relation holds from
// element i to element j.
enum GroundTest {
    Constant(bool),
    Not(Box<GroundTest>),
    Binary(Kind, Box<GroundTest>, Box<GroundTest>),
    All(Box<GroundTest>),
    Ex(Box<GroundTest>),
    Holds(usize, usize),
}

impl GroundTest {
    fn test(&self, values: &[usize], holds: u32) -> bool {
        let extended = |element: usize| [values, &[element]].concat();
        match self {
            GroundTest::Constant(value) => *value,
            GroundTest::Not(operand) => !operand.test(values, holds),
            GroundTest::Binary(kind, left, right) => match kind {
                Kind::And => left.test(values, holds) && right.test(values, holds),
                Kind::Or => left.test(values, holds) || right.test(values, holds),
                Kind::Imply => !left.test(values, holds) || right.test(values, holds),
                _ => left.test(values, holds) == right.test(values, holds),
            },
            GroundTest::All(body) => ELEMENTS
                .iter()
                .all(|element| body.test(&extended(*element), holds)),
            GroundTest::Ex(body) => ELEMENTS
                .iter()
                .any(|element| body.test(&extended(*element), holds)),
            GroundTest::Holds(from, to) => (holds >> (3 * values[*from] + values[*to])) & 1 == 1,
        }
    }
}

// The ground instances of a hypothesis over three elements. A universal quantifier where the
// hypothesis asserts it, or an existential where it denies it, becomes a test over the three
// elements, which the hypothesis implies. None when the hypothesis says anything but how the
// relation holds between bound variables, so that it's left out.
fn get_ground_test(
    formula: &Expr,
    symbol: &str,
    bound: &[Rc<str>],
    polarity: Polarity,
) -> Option<GroundTest> {
    let flip = || match polarity {
        Polarity::Both => Polarity::Both,
        Polarity::Positive => Polarity::Negative,
        Polarity::Negative => Polarity::Positive,
    };
    match formula.kind {
        Kind::True => Some(GroundTest::Constant(true)),
        Kind::False => Some(GroundTest::Constant(false)),
        Kind::Not => get_ground_test(&formula.args[0], symbol, bound, flip())
            .map(|operand| GroundTest::Not(Box::new(operand))),
        Kind::And | Kind::Or | Kind::Imply | Kind::Equiv => {
            let left = get_ground_test(
                &formula.args[0],
                symbol,
                bound,
                match formula.kind {
                    Kind::Imply => flip(),
                    Kind::Equiv => Polarity::Both,
                    _ => polarity,
                },
            );
            let right = get_ground_test(
                &formula.args[1],
                symbol,
                bound,
                if formula.kind == Kind::Equiv {
                    Polarity::Both
                } else {
                    polarity
                },
            );
            Some(GroundTest::Binary(
                formula.kind,
                Box::new(left?),
                Box::new(right?),
            ))
        }
        Kind::All | Kind::Ex => {
            let is_universal = if formula.kind == Kind::All {
                polarity == Polarity::Positive
            } else {
                polarity == Polarity::Negative
            };
            if !is_universal || &*formula.symbol != UNIVERSE {
                return None;
            }
            let inner = [bound, &[formula.args[0].symbol.clone()]].concat();
            let body = Box::new(get_ground_test(&formula.args[1], symbol, &inner, polarity)?);
            Some(if formula.kind == Kind::All {
                GroundTest::All(body)
            } else {
                GroundTest::Ex(body)
            })
        }
        Kind::App => {
            if &*formula.symbol != symbol || formula.args.len() != 2 {
                return None;
            }
            let position = |inner: &Expr| {
                if inner.kind == Kind::Var {
                    bound.iter().rposition(|name| *name == inner.symbol)
                } else {
                    None
                }
            };
            Some(GroundTest::Holds(
                position(&formula.args[0])?,
                position(&formula.args[1])?,
            ))
        }
        _ => None,
    }
}

/// = has every property. Another relation has the ones the hypotheses give it:
/// `createRelationProperties`.
pub struct RelationProperties<'a> {
    context: &'a CheckContext,
    cache: HashMap<String, bool>,
}

impl<'a> RelationProperties<'a> {
    pub fn new(context: &'a CheckContext) -> RelationProperties<'a> {
        RelationProperties {
            context,
            cache: HashMap::new(),
        }
    }

    fn has_property(&mut self, symbol: &str, property: RelationProperty) -> bool {
        let key = format!("{}:{symbol}", property.name());
        if let Some(cached) = self.cache.get(&key) {
            return *cached;
        }
        let tests: Vec<GroundTest> = self
            .context
            .hypotheses
            .iter()
            .filter_map(|hypothesis| get_ground_test(hypothesis, symbol, &[], Polarity::Positive))
            .collect();
        let has = |holds: u32, from: u32, to: u32| (holds >> (3 * from + to)) & 1 == 1;
        let is_broken = |holds: u32| match property {
            RelationProperty::Reflexive => !has(holds, 0, 0),
            RelationProperty::Symmetric => has(holds, 0, 1) && !has(holds, 1, 0),
            RelationProperty::Transitive => {
                has(holds, 0, 1) && has(holds, 1, 2) && !has(holds, 0, 2)
            }
        };
        let result = (0..512u32)
            .all(|holds| !is_broken(holds) || !tests.iter().all(|test| test.test(&[], holds)));
        self.cache.insert(key, result);
        result
    }

    pub fn has(&mut self, symbol: &str, properties: &[RelationProperty]) -> bool {
        symbol == "="
            || properties
                .iter()
                .all(|property| self.has_property(symbol, *property))
    }
}
