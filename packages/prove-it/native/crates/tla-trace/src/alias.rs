//! A trace's states as TLC prints them through the configuration's ALIAS (`Tool.evalAlias`): the
//! alias evaluated at each state, with the state after it as the next state, and printed as the
//! record it gives (`RecordValue.toState`).

use crate::eval::TracePrefix;
use crate::failure::nested;
use crate::postcondition::{InitialAction, action_parameters, action_record, site_record};
use crate::print::{print_order, text_string};
use crate::rebuild::{Rebuilder, run};
use crate::value::{Class, EvalError, TlcMessage, Value};
use crate::{Trace, Unsupported};
use std::cell::{Cell, RefCell};
use std::rc::Rc;
use tla_ir::{Definition, DefinitionForm};

/// A state as TLC prints it through the ALIAS.
#[derive(Clone, Debug)]
pub enum Alias {
    /// The fields of the record the alias gives, in the order TLC prints them: as written until
    /// TLC sorts the record (`RecordValue.snapshot`).
    Record(Vec<(String, Value)>),
    /// The alias gives no record, so TLC prints the state itself (`Value.toState` is null).
    State,
}

// TLC's messages of a configuration naming a definition that takes arguments, what the spec
// doesn't define, and a definition TLC computed as it started (`EC.TLC_CONFIG_ID_REQUIRES_NO_ARG`,
// `EC.TLC_CONFIG_SPECIFIED_NOT_DEFINED`, `EC.TLC_CONFIG_ID_MUST_NOT_BE_CONSTANT`).
const REQUIRES_NO_ARGUMENT: u32 = 2228;
const SPECIFIED_NOT_DEFINED: u32 = 2229;
const MUST_NOT_BE_CONSTANT: u32 = 2233;

fn unsupported<T>(reason: &str) -> Result<T, Unsupported> {
    Err(Unsupported(format!("an ALIAS {reason}")))
}

impl Rebuilder<'_> {
    /// Each state of a rebuilt trace as TLC prints it through the ALIAS, or `None` without one.
    /// TLC evaluates the alias with TLCGet("level") at the state's position in the trace, and the
    /// state after it as the next state: for a lasso's last state, the state its cycle starts at
    /// (`cycle_start`), and otherwise the state itself.
    /// An alias that fails to evaluate gives the state with TLC's message of the failure as its
    /// `_ALIASEvalError` field, marked as TLC marks a coded message under `-tool`.
    /// TLC binds the builtin Trace at each position to the trace's first states, as many as
    /// `prefixes` says; with no `prefixes`, the alias isn't followed where it reads Trace. A
    /// simulation's records carry each state's action first, as an `_action` field
    /// (`TLCExt.getTrace`): for each step TLC's record of its action, and for the initial state
    /// the record of the initial predicate, `initial`.
    pub fn alias(
        &mut self,
        trace: &Trace,
        cycle_start: Option<usize>,
        prefixes: Option<&[usize]>,
        is_tool: bool,
        is_simulated: bool,
        initial: Option<&InitialAction>,
    ) -> Result<Option<Vec<Alias>>, Unsupported> {
        let evaluator = self.evaluator();
        let ir = evaluator.ir;
        let Some(alias) = &ir.model.alias else {
            return Ok(None);
        };
        let initial = match (is_simulated && prefixes.is_some(), initial) {
            (false, _) => None,
            (true, Some(initial)) => Some(initial),
            (true, None) => {
                return unsupported("of a simulation whose initial predicate has no location");
            }
        };
        let name = &ir.texts[alias.name as usize];
        let rejected = |text: String, code: u32| TlcMessage {
            text,
            code: Some(code),
            is_eval_exception: false,
        };
        // TLC finds the alias by its name as it evaluates it, and fails on a name it has no
        // definition of, on a definition that takes arguments and on one it computed as it
        // started (`Spec.getAliasSpec`).
        let defined = alias
            .definition
            .map(|index| (index, evaluator.definition(ir.definitions[index as usize])));
        let body = match defined {
            None => Err(rejected(
                format!(
                    "The alias {name} specified in the configuration file\nis not defined in the specification."
                ),
                SPECIFIED_NOT_DEFINED,
            )),
            Some((
                _,
                Definition {
                    form: DefinitionForm::Operator(params),
                    ..
                },
            )) if !params.is_empty() => Err(rejected(
                format!("TLC requires alias not to take any argument, but one was given: {name}"),
                REQUIRES_NO_ARGUMENT,
            )),
            Some((index, definition)) => {
                if Rebuilder::new(ir)?.is_computed_at_startup(index)? {
                    Err(rejected(
                        format!("The alias {name} cannot be a constant."),
                        MUST_NOT_BE_CONSTANT,
                    ))
                } else {
                    Ok(definition.body)
                }
            }
        };
        let context = run(evaluator.scope_context(ir.model.scope))?;
        let states = &trace.states;
        let state = |position: usize| states[position].values.iter().cloned().map(Some).collect();
        // Each state as the record of its variables TLC binds Trace to, in the order of the
        // state's variables (`RecordValue(TLCState)`).
        let mut records = Vec::new();
        // What kinds of values steps' actions bind parameters to that TLC holds otherwise: it
        // sorts a record, as it fingerprints it, at a point of its simulation the trace
        // evaluator doesn't follow, and may hold a set as an interval or lazily.
        let mut bound = Kinds::default();
        for (position, state) in states.iter().enumerate().filter(|_| prefixes.is_some()) {
            let action = match initial {
                None => None,
                Some(initial) if position == 0 => {
                    Some(site_record(evaluator, initial, &[], false)?)
                }
                Some(_) => {
                    let Some(action) = state
                        .action
                        .and_then(|index| ir.model.actions.get(index as usize))
                    else {
                        return unsupported("of a simulation's step whose action the trace lacks");
                    };
                    let parameters = action_parameters(evaluator, action)?;
                    for (_, value) in &parameters {
                        bound = bound.or(Kinds::of(value));
                    }
                    Some(action_record(evaluator, action, &parameters, false)?)
                }
            };
            let mut fields: Vec<_> = ir
                .tlc_order
                .iter()
                .map(|&variable| {
                    let name = &ir.texts[ir.variables[variable as usize] as usize];
                    (
                        evaluator.text_of(name.encode_utf16().collect()),
                        state.values[variable as usize].clone(),
                    )
                })
                .collect();
            if let Some(action) = action {
                fields.insert(
                    0,
                    (evaluator.counterexample_field("_action", false), action),
                );
            }
            records.push(run(Value::record(fields))?);
        }
        let records: Rc<[Value]> = records.into();
        let mut aliases = Vec::with_capacity(states.len());
        // TLC evaluates the alias of each state as it prints it, between its rebuilds of the
        // states, so an alias that uses the registers those rebuilds set reads them part way.
        let (reads, writes) = (evaluator.register_reads, evaluator.register_writes);
        for position in 0..states.len() {
            let next = match position + 1 {
                after if after < states.len() => after,
                _ => cycle_start.unwrap_or(position),
            };
            evaluator.current = state(position);
            evaluator.next = state(next);
            evaluator.level = position as i32 + 1;
            // The next state is at its own position's level, one past the state's but for the
            // last state's, which is the state itself or the one its cycle starts at.
            evaluator.next_level = Some(next as i32 + 1);
            evaluator.printed.clear();
            evaluator.trace = prefixes.map(|prefixes| TracePrefix {
                records: records.clone(),
                length: prefixes[position],
                built: RefCell::new(None),
                reads: Cell::new(0),
                stringified: RefCell::new(Vec::new()),
            });
            // TLC prints an alias that fails with its message as a field of the state
            // (`_ALIASEvalError`, `Tool.evalAlias`).
            let result = match &body {
                Ok(body) => evaluator.evaluate(*body, &context),
                Err(message) => Err(EvalError {
                    reason: "an ALIAS TLC rejects".into(),
                    message: Some(message.clone()),
                }),
            };
            evaluator.next_level = None;
            let prefix = evaluator.trace.take();
            let is_trace_read = prefix
                .as_ref()
                .is_some_and(|prefix| prefix.built.borrow().is_some());
            // TLC builds the records anew each time the alias reads Trace (`TLCExt.getTrace`):
            // one read that sorts them leaves the others' as built.
            // What kinds of values the alias's value holds, below its own fields, or that it
            // turned to text: a record or set it derived from Trace's may print otherwise, so
            // the alias declines where it holds any of the kind.
            let stringified = prefix
                .as_ref()
                .map(|prefix| prefix.stringified.take())
                .unwrap_or_default();
            let shown = match &result {
                Ok(Value::Function(function)) => function
                    .range
                    .iter()
                    .chain(&function.domain)
                    .fold(Kinds::default(), |kinds, value| kinds.or(Kinds::of(value))),
                Ok(value) => Kinds::of(value),
                Err(_) => Kinds::default(),
            };
            let shown = stringified
                .iter()
                .fold(shown, |kinds, value| kinds.or(Kinds::of(value)));
            if let Some(prefix) = &prefix
                && prefix.reads.get() > 1
                && let Some(Value::Function(built)) = &*prefix.built.borrow()
                && prefix
                    .records
                    .iter()
                    .zip(&built.range)
                    .any(|(record, copy)| is_sorted_since(record, copy))
                && shown.is_record
            {
                return unsupported("that reads Trace more than once and sorts its records");
            }
            if is_trace_read
                && ((bound.is_record && shown.is_record) || (bound.is_set && shown.is_set))
            {
                return unsupported(
                    "that reads a simulation's Trace whose actions bind a parameter to a record or a set",
                );
            }
            if !evaluator.printed.is_empty() {
                return unsupported("that prints");
            }
            // TLC evaluates the alias again as it checks the postconditions, and as it prints the
            // trace between its rebuilds: one that sets registers, or reads those the rebuilds
            // set, isn't followed.
            if (evaluator.register_reads, evaluator.register_writes) != (reads, writes)
                && (writes > 0 || evaluator.register_writes != writes)
            {
                return unsupported("that uses registers the rebuild of the trace sets");
            }
            let value = match result {
                Err(EvalError {
                    message: Some(message),
                    ..
                }) => {
                    let text = if is_tool {
                        nested(&message)
                    } else {
                        message.text
                    };
                    let mut fields: Vec<_> = ir
                        .tlc_order
                        .iter()
                        .map(|&variable| {
                            let name = &ir.texts[ir.variables[variable as usize] as usize];
                            let value = states[position].values[variable as usize].clone();
                            (name.to_string(), value)
                        })
                        .collect();
                    let units: Box<[u16]> = text.encode_utf16().collect();
                    fields.push((
                        "_ALIASEvalError".into(),
                        Value::Str(evaluator.text_of(units)),
                    ));
                    aliases.push(Alias::Record(fields));
                    continue;
                }
                value => run(value)?,
            };
            aliases.push(match &value {
                Value::Function(function) if function.class.get() == Class::Record => {
                    let fields: Vec<_> = print_order(function, false)
                        .into_iter()
                        .map(|position| match &function.domain[position] {
                            Value::Str(name) => {
                                Ok((text_string(&name.units), function.range[position].clone()))
                            }
                            _ => unsupported("record with a key that isn't a string"),
                        })
                        .collect::<Result<_, _>>()?;
                    // A `_format` field sets how TLC writes each field.
                    if fields.iter().any(|(name, _)| name == "_format") {
                        return unsupported("record with a _format field");
                    }
                    Alias::Record(fields)
                }
                // TLC prints the state itself for a function with a key that isn't a string,
                // which no record converts it to (`FcnRcdValue.toRcd`, `Value.toState`).
                Value::Function(function)
                    if function
                        .domain
                        .iter()
                        .any(|key| !matches!(key, Value::Str(_))) =>
                {
                    Alias::State
                }
                // TLC prints a function of strings as the record it converts it to
                // (`FcnRcdValue.toState`), but not one it keeps lazy.
                Value::Function(_) => return unsupported("function that isn't a record"),
                _ => Alias::State,
            });
        }
        Ok(Some(aliases))
    }
}

// Whether a value holds a record of more than one field, or a function of strings TLC prints as
// one, and whether it holds a set.
#[derive(Clone, Copy, Default)]
struct Kinds {
    is_record: bool,
    is_set: bool,
}

impl Kinds {
    fn or(self, other: Kinds) -> Kinds {
        Kinds {
            is_record: self.is_record || other.is_record,
            is_set: self.is_set || other.is_set,
        }
    }

    fn of(value: &Value) -> Kinds {
        match value {
            Value::Function(function) => {
                let is_record = function.domain.len() > 1
                    && function
                        .domain
                        .iter()
                        .all(|key| matches!(key, Value::Str(_)));
                function.domain.iter().chain(&function.range).fold(
                    Kinds {
                        is_record,
                        is_set: false,
                    },
                    |kinds, inner| kinds.or(Kinds::of(inner)),
                )
            }
            Value::Set(elements) => elements.iter().fold(
                Kinds {
                    is_record: false,
                    is_set: true,
                },
                |kinds, inner| kinds.or(Kinds::of(inner)),
            ),
            Value::Bool(_) | Value::Int(_) | Value::Model(_) | Value::Str(_) => Kinds::default(),
            _ => Kinds {
                is_record: true,
                is_set: true,
            },
        }
    }
}

// Whether an evaluation sorted a copy of Trace's records, or of the records they hold that TLC
// builds with them, which a read of Trace sees and another's copies don't.
fn is_sorted_since(record: &Value, copy: &Value) -> bool {
    match (record, copy) {
        (Value::Function(record), Value::Function(copy)) if !Rc::ptr_eq(record, copy) => {
            (record.written.borrow().is_some() && copy.written.borrow().is_none())
                || record
                    .range
                    .iter()
                    .zip(&copy.range)
                    .any(|(record, copy)| is_sorted_since(record, copy))
        }
        _ => false,
    }
}
