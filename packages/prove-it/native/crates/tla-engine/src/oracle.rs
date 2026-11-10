//! The enumeration oracle's native side (DESIGN.md 6.8): answers the requests of
//! `native/oracle/ValueOracle.java` that build values, the sets TLC keeps lazy among them, and
//! enumerate a set, as the native engine builds and enumerates them, so `replay enumerate` can
//! answer each line as TLC does. A set's elements are answered as their TLC fingerprints.

use tla_values::fingerprint::{Fingerprints, Polynomial};
use tla_values::store::Outcome;
use tla_values::{Bail, Id, Store};

use crate::compile::lazy::{Lazy, Operator};
use crate::machine::{Machine, Program};

fn decode(hex: &str) -> Vec<u16> {
    (0..hex.len() / 4)
        .map(|index| u16::from_str_radix(&hex[index * 4..index * 4 + 4], 16).unwrap_or(0))
        .collect()
}

struct Reader<'a> {
    tokens: Vec<&'a str>,
    next: usize,
}

impl<'a> Reader<'a> {
    fn token(&mut self) -> Outcome<&'a str> {
        let token = self
            .tokens
            .get(self.next)
            .ok_or(Bail("a request too short"))?;
        self.next += 1;
        Ok(token)
    }

    fn count(text: &str) -> Outcome<usize> {
        text.parse()
            .map_err(|_| Bail("a count that isn't a number"))
    }

    fn value(&mut self, machine: &mut Machine<'_>) -> Outcome<Id> {
        match self.lazy(machine)? {
            Lazy::Set(id) => Ok(id),
            _ => Err(Bail("a lazy set inside a value")),
        }
    }

    fn values(&mut self, machine: &mut Machine<'_>, count: usize) -> Outcome<Vec<Id>> {
        (0..count).map(|_| self.value(machine)).collect()
    }

    // A value, or a lazy set as Tool builds it. A value that isn't a set stands as Lazy::Set,
    // which enumerating fails on, as TLC does.
    fn lazy(&mut self, machine: &mut Machine<'_>) -> Outcome<Lazy> {
        let token = self.token()?;
        let (kind, rest) = token.split_at(1);
        let store = &mut machine.store;
        let id = match kind {
            "T" => tla_values::store::TRUE,
            "F" => tla_values::store::FALSE,
            "i" => store.int(rest.parse().map_err(|_| Bail("an integer token"))?)?,
            "s" => store.str(&decode(rest)),
            "m" => store.model(&decode(rest)),
            "S" => {
                let elements = self.values(machine, Self::count(rest)?)?;
                machine.store.set_of(&elements)?
            }
            "U" => {
                let elements = self.values(machine, Self::count(rest)?)?;
                machine.store.tuple_of(&elements)
            }
            "R" | "f" => {
                let count = Self::count(rest)?;
                let mut keys = Vec::with_capacity(count);
                let mut values = Vec::with_capacity(count);
                for _ in 0..count {
                    keys.push(self.value(machine)?);
                    values.push(self.value(machine)?);
                }
                machine.store.function_of(&keys, &values)?
            }
            "L" => return self.lazy_set(machine, rest),
            _ => return Err(Bail("an unknown token")),
        };
        Ok(Lazy::Set(id))
    }

    fn lazy_set(&mut self, machine: &mut Machine<'_>, kind: &str) -> Outcome<Lazy> {
        let (letter, rest) = kind.split_at(1);
        Ok(match letter {
            "p" => Lazy::Subset(Box::new(self.lazy(machine)?)),
            "f" => {
                let domain = self.lazy(machine)?;
                Lazy::FunctionSet(Box::new(domain), Box::new(self.lazy(machine)?))
            }
            "r" => {
                let mut fields = Vec::new();
                for _ in 0..Self::count(rest)? {
                    let key = self.value(machine)?;
                    fields.push((key, self.lazy(machine)?));
                }
                // The engine orders the fields by TLC's order of their names.
                let mut failure = None;
                fields.sort_by(|left, right| match machine.store.compare(left.0, right.0) {
                    Ok(order) => order.cmp(&0),
                    Err(bail) => {
                        failure = Some(bail);
                        std::cmp::Ordering::Equal
                    }
                });
                if let Some(bail) = failure {
                    return Err(bail);
                }
                let (keys, sets) = fields.into_iter().unzip();
                Lazy::RecordSet(keys, sets)
            }
            "x" => Lazy::Product(
                (0..Self::count(rest)?)
                    .map(|_| self.lazy(machine))
                    .collect::<Outcome<_>>()?,
            ),
            "u" | "i" | "d" => {
                let left = self.lazy(machine)?;
                let right = self.lazy(machine)?;
                let operator = match letter {
                    "u" => Operator::Union,
                    "i" => Operator::Intersection,
                    _ => Operator::Difference,
                };
                Lazy::combine(machine, operator, left, right)?
            }
            _ => return Err(Bail("an unknown lazy set")),
        })
    }
}

/// Answers each request as `ValueOracle.java` answers it: `strings` with the tokens TLC gives
/// texts it interns first, `value` with ok, `enumerate` with "elements" and each element's TLC
/// fingerprint, and a request the engine stops on with "!" and the reason. Other requests are
/// the value oracle's, which this doesn't answer.
pub fn answer_requests<'a>(lines: impl IntoIterator<Item = &'a str>) -> Vec<String> {
    let program = Program::default();
    let mut machine = Machine::new(&program, Store::new());
    let mut fingerprints = Fingerprints::new(Polynomial::get(0));
    let mut values: Vec<Outcome<Lazy>> = Vec::new();
    let mut answers = Vec::new();
    for line in lines {
        let mut reader = Reader {
            tokens: line.split(' ').collect(),
            next: 1,
        };
        let answer = match reader.tokens[0] {
            "strings" => {
                let texts: Vec<Vec<u16>> = reader.tokens[1..]
                    .iter()
                    .map(|token| decode(&token[1..]))
                    .collect();
                machine.store.reset(texts.iter().map(Vec::as_slice));
                let tokens: Vec<String> =
                    (1..=texts.len()).map(|token| token.to_string()).collect();
                format!("tokens {}", tokens.join(" "))
            }
            "value" => {
                let value = reader.lazy(&mut machine);
                let answer = match &value {
                    Ok(_) => "ok".to_string(),
                    Err(bail) => format!("!{}", bail.0),
                };
                values.push(value);
                answer
            }
            "enumerate" => {
                let index: usize = reader
                    .tokens
                    .get(2)
                    .and_then(|text| text.parse().ok())
                    .unwrap_or(usize::MAX);
                let elements = match values.get(index) {
                    Some(Ok(set)) if reader.tokens[1] == "q" => set.enumerate(&mut machine),
                    Some(Ok(set)) => set.stream(&mut machine),
                    Some(Err(bail)) => Err(*bail),
                    None => Err(Bail("no such value")),
                };
                match elements {
                    Ok(elements) => elements
                        .into_iter()
                        .map(|element| fingerprints.get_state(&machine.store, &[element], &[0]))
                        .try_fold("elements".to_string(), |answer, fingerprint| {
                            Ok(format!("{answer} {}", fingerprint? as i64))
                        })
                        .unwrap_or_else(|bail: Bail| format!("!{}", bail.0)),
                    Err(bail) => format!("!{}", bail.0),
                }
            }
            _ => "!a request the enumeration oracle doesn't answer".to_string(),
        };
        answers.push(answer);
    }
    answers
}
