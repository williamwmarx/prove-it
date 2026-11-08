//! The store's operations by the names `PROVE_IT_STORE_TRACE` writes, with their arguments as the
//! trace records them, so one table serves the replay of a trace, the N-API test hooks and the
//! fuzzer. Arguments are checked before an operation runs: an id must name a value, and a
//! position must be inside its function, so a wrong argument is an error and never a panic.

use crate::store::{Bail, Id, Store, is_function_kind};

/// An argument as a trace records it.
#[derive(Clone, Debug, PartialEq)]
pub enum Argument {
    Number(f64),
    Text(Vec<u16>),
    Numbers(Vec<f64>),
    Texts(Vec<Vec<u16>>),
}

/// An operation's result as a trace records it: `null`, a boolean, or a number.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Answer {
    Null,
    Bool(bool),
    Number(i64),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Failure {
    /// The store stopped, with its reason.
    Bail(Bail),
    /// The operation is unknown or its arguments are wrong.
    Argument(String),
}

impl From<Bail> for Failure {
    fn from(bail: Bail) -> Failure {
        Failure::Bail(bail)
    }
}

/// Every operation `perform` knows, as the trace names them.
pub const OPERATIONS: [&str; 33] = [
    "resetStore",
    "rankStrings",
    "int",
    "str",
    "model",
    "compare",
    "equals",
    "setOf",
    "setOfRange",
    "setOfSorted",
    "setOfSortedRange",
    "isMember",
    "union",
    "intersection",
    "difference",
    "isSubset",
    "withElement",
    "tupleOf",
    "tupleOfRange",
    "recordOf",
    "functionOfSorted",
    "functionOverSet",
    "functionOf",
    "findKey",
    "apply",
    "except",
    "exceptAt",
    "applyField",
    "domainOf",
    "sliceTuple",
    "concatTuples",
    "appendTuple",
    "getValueCount",
];

struct Arguments<'a> {
    name: &'a str,
    values: &'a [Argument],
    value_count: usize,
}

impl Arguments<'_> {
    fn wrong(&self, what: &str) -> Failure {
        Failure::Argument(format!("{} takes {what}", self.name))
    }

    fn get(&self, index: usize) -> Result<&Argument, Failure> {
        self.values
            .get(index)
            .ok_or_else(|| self.wrong(&format!("an argument at {index}")))
    }

    fn number(&self, index: usize) -> Result<f64, Failure> {
        match self.get(index)? {
            Argument::Number(number) => Ok(*number),
            _ => Err(self.wrong(&format!("a number at {index}"))),
        }
    }

    fn to_id(&self, number: f64) -> Result<Id, Failure> {
        if number >= 0.0 && number < self.value_count as f64 && number.fract() == 0.0 {
            Ok(number as Id)
        } else {
            Err(self.wrong(&format!("ids of values, not {number}")))
        }
    }

    fn id(&self, index: usize) -> Result<Id, Failure> {
        self.to_id(self.number(index)?)
    }

    fn whole(&self, index: usize) -> Result<u32, Failure> {
        let number = self.number(index)?;
        if number >= 0.0 && number <= f64::from(u32::MAX) && number.fract() == 0.0 {
            Ok(number as u32)
        } else {
            Err(self.wrong(&format!("a whole number at {index}")))
        }
    }

    fn ids(&self, index: usize) -> Result<Vec<Id>, Failure> {
        match self.get(index)? {
            Argument::Numbers(numbers) => {
                numbers.iter().map(|&number| self.to_id(number)).collect()
            }
            Argument::Texts(texts) if texts.is_empty() => Ok(Vec::new()),
            _ => Err(self.wrong(&format!("ids at {index}"))),
        }
    }

    fn text(&self, index: usize) -> Result<&[u16], Failure> {
        match self.get(index)? {
            Argument::Text(text) => Ok(text),
            _ => Err(self.wrong(&format!("a string at {index}"))),
        }
    }

    fn texts(&self, index: usize) -> Result<&[Vec<u16>], Failure> {
        match self.values.get(index) {
            None => Ok(&[]),
            Some(Argument::Texts(texts)) => Ok(texts),
            Some(Argument::Numbers(numbers)) if numbers.is_empty() => Ok(&[]),
            _ => Err(self.wrong(&format!("strings at {index}"))),
        }
    }
}

fn id(id: Id) -> Answer {
    Answer::Number(i64::from(id))
}

/// Runs an operation of the store by its trace name, as `scripts/store-replay.ts` runs it on the
/// TypeScript store. `resetStore` takes TLC's order of strings, as the trace records it.
pub fn perform(store: &mut Store, name: &str, values: &[Argument]) -> Result<Answer, Failure> {
    let arguments = Arguments {
        name,
        values,
        value_count: store.value_count(),
    };
    let arguments = &arguments;
    let at_least = |ids: &[Id], length: usize| {
        if ids.len() >= length {
            Ok(())
        } else {
            Err(arguments.wrong(&format!("at least {length} values")))
        }
    };
    let function = |store: &Store, index: usize| {
        let function = arguments.id(index)?;
        if is_function_kind(store.kind_of(function)) {
            Ok(function)
        } else {
            Err(arguments.wrong(&format!("a function at {index}")))
        }
    };
    Ok(match name {
        "resetStore" => {
            store.reset(arguments.texts(0)?.iter().map(Vec::as_slice));
            Answer::Null
        }
        "rankStrings" => {
            store.rank_strings(arguments.texts(0)?.iter().map(Vec::as_slice));
            Answer::Null
        }
        "int" => {
            let number = arguments.number(0)?;
            // A number that isn't an integer overflows, as Number.isInteger decides in int().
            if number.fract() != 0.0 || !number.is_finite() {
                return Err(Failure::Bail(Bail("integer overflow")));
            }
            id(store.int(number as i64)?)
        }
        "str" => id(store.str(arguments.text(0)?)),
        "model" => id(store.model(arguments.text(0)?)),
        "compare" => Answer::Number(i64::from(
            store.compare(arguments.id(0)?, arguments.id(1)?)?,
        )),
        "equals" => Answer::Bool(store.equals(arguments.id(0)?, arguments.id(1)?)?),
        "setOf" => id(store.set_of(&arguments.ids(0)?)?),
        "setOfRange" => id(store.set_of_range(&arguments.ids(0)?)?),
        "setOfSorted" | "setOfSortedRange" => id(store.set_of_sorted(&arguments.ids(0)?)),
        "isMember" => Answer::Bool(store.is_member(arguments.id(0)?, arguments.id(1)?)?),
        "union" => id(store.union(arguments.id(0)?, arguments.id(1)?)?),
        "intersection" => id(store.intersection(arguments.id(0)?, arguments.id(1)?)?),
        "difference" => id(store.difference(arguments.id(0)?, arguments.id(1)?)?),
        "isSubset" => Answer::Bool(store.is_subset(arguments.id(0)?, arguments.id(1)?)?),
        "withElement" => id(store.with_element(arguments.id(0)?, arguments.id(1)?)?),
        "tupleOf" | "tupleOfRange" => id(store.tuple_of(&arguments.ids(0)?)),
        "recordOf" => {
            let (keys, values) = (arguments.ids(0)?, arguments.ids(1)?);
            at_least(&values, keys.len())?;
            let shape = store.create_record_shape(&keys);
            id(store.record_of(&shape, &values))
        }
        "functionOfSorted" | "functionOf" => {
            let (keys, values) = (arguments.ids(0)?, arguments.ids(1)?);
            at_least(&values, keys.len())?;
            if name == "functionOf" {
                id(store.function_of(&keys, &values)?)
            } else {
                id(store.function_of_sorted(&keys, &values))
            }
        }
        "functionOverSet" => {
            let (set, values) = (arguments.id(0)?, arguments.ids(1)?);
            at_least(&values, store.size_of(set) as usize)?;
            id(store.function_over_set(set, &values))
        }
        "findKey" => Answer::Number(i64::from(
            store.find_key(arguments.id(0)?, arguments.id(1)?)?,
        )),
        "apply" => id(store.apply(arguments.id(0)?, arguments.id(1)?)?),
        "except" => id(store.except(arguments.id(0)?, arguments.id(1)?, arguments.id(2)?)?),
        "exceptAt" => {
            let function = function(store, 0)?;
            let values = arguments.ids(2)?;
            let positions = match arguments.get(1)? {
                Argument::Numbers(numbers) => numbers
                    .iter()
                    .map(|&number| {
                        let size = store.size_of(function);
                        if number >= 0.0 && number < f64::from(size) && number.fract() == 0.0 {
                            Ok(number as u32)
                        } else {
                            Err(arguments.wrong("positions inside the function"))
                        }
                    })
                    .collect::<Result<Vec<u32>, Failure>>()?,
                _ => return Err(arguments.wrong("positions at 1")),
            };
            at_least(&values, positions.len())?;
            id(store.except_at(function, &positions, &values[..positions.len()]))
        }
        "applyField" => id(store.apply_field(arguments.id(0)?, arguments.id(1)?, &mut 0)?),
        "domainOf" => id(store.domain_of(arguments.id(0)?)),
        "sliceTuple" => {
            let tuple = arguments.id(0)?;
            let (from, to) = (arguments.whole(1)?, arguments.whole(2)?);
            if from < to && to > store.size_of(tuple) {
                return Err(arguments.wrong("a slice inside the tuple"));
            }
            id(store.slice_tuple(tuple, from, to))
        }
        "concatTuples" => id(store.concat_tuples(arguments.id(0)?, arguments.id(1)?)),
        "appendTuple" => id(store.append_tuple(arguments.id(0)?, arguments.id(1)?)),
        "getValueCount" => Answer::Number(store.value_count() as i64),
        _ => return Err(Failure::Argument(format!("no operation {name}"))),
    })
}
