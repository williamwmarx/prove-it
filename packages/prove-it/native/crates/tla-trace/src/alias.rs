//! A trace's states as TLC prints them through the configuration's ALIAS (`Tool.evalAlias`): the
//! alias evaluated at each state, with the state after it as the next state, and printed as the
//! record it gives (`RecordValue.toState`).

use crate::eval::TracePrefix;
use crate::failure::nested;
use crate::print::{format_pretty, print_order, text_string};
use crate::rebuild::{Rebuilder, run};
use crate::value::{Class, EvalError, TlcMessage, Value};
use crate::{Trace, Unsupported};
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
    /// simulation's records carry each state's action as an `_action` field
    /// (`TLCExt.getTrace`), which the rebuild doesn't hold: the alias is evaluated with three
    /// stand-ins for it, one string for every state, a string for each and a number for each,
    /// and followed only where each state's value, or failure, is the same under all three.
    pub fn alias(
        &mut self,
        trace: &Trace,
        cycle_start: Option<usize>,
        prefixes: Option<&[usize]>,
        is_tool: bool,
        is_simulated: bool,
    ) -> Result<Option<Vec<Alias>>, Unsupported> {
        if !is_simulated || prefixes.is_none() {
            return Ok(self
                .alias_with(trace, cycle_start, prefixes, is_tool, None)?
                .map(|evaluated| evaluated.aliases));
        }
        let mut evaluated = Vec::new();
        for stand_in in [StandIn::Same, StandIn::Each, StandIn::Number] {
            evaluated.push(self.alias_with(
                trace,
                cycle_start,
                prefixes,
                is_tool,
                Some(stand_in),
            )?);
        }
        let texts = |position: usize| evaluated[position].as_ref().map(|each| &each.texts);
        if texts(0) != texts(1) || texts(0) != texts(2) {
            return unsupported("that reads the actions of a simulation's Trace");
        }
        Ok(evaluated.swap_remove(0).map(|each| each.aliases))
    }

    fn alias_with(
        &mut self,
        trace: &Trace,
        cycle_start: Option<usize>,
        prefixes: Option<&[usize]>,
        is_tool: bool,
        action: Option<StandIn>,
    ) -> Result<Option<Evaluated>, Unsupported> {
        let evaluator = self.evaluator();
        let ir = evaluator.ir;
        let Some(alias) = &ir.model.alias else {
            return Ok(None);
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
        for (position, state) in states.iter().enumerate().filter(|_| prefixes.is_some()) {
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
            if let Some(stand_in) = action {
                let value = match stand_in {
                    StandIn::Same => Value::Str(evaluator.text_of("a".encode_utf16().collect())),
                    StandIn::Each => Value::Str(
                        evaluator.text_of(format!("b{position}").encode_utf16().collect()),
                    ),
                    StandIn::Number => Value::Int(position as i32),
                };
                fields.push((evaluator.text_of("_action".encode_utf16().collect()), value));
            }
            records.push(run(Value::record(fields))?);
        }
        let records: std::rc::Rc<[Value]> = records.into();
        let mut aliases = Vec::with_capacity(states.len());
        // Each state's value of the alias, or its failure, as text.
        let mut texts = Vec::with_capacity(states.len());
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
            evaluator.trace = None;
            texts.push(match &result {
                Ok(value) => format_pretty(value),
                Err(error) => format!("{:?}", error.message.as_ref().map(|message| &message.text)),
            });
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
        Ok(Some(Evaluated { aliases, texts }))
    }
}

// What a simulation's Trace records hold as each state's action, which the rebuild doesn't know.
#[derive(Clone, Copy)]
enum StandIn {
    // The same string for every state.
    Same,
    // A string of each state's own.
    Each,
    // A number of each state's own.
    Number,
}

// Each state of a trace as the alias gives it, and its value of the alias, or its failure, as text.
struct Evaluated {
    aliases: Vec<Alias>,
    texts: Vec<String>,
}
