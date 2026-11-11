//! A trace's states as TLC prints them through the configuration's ALIAS (`Tool.evalAlias`): the
//! alias evaluated at each state, with the state after it as the next state, and printed as the
//! record it gives (`RecordValue.toState`).

use crate::failure::nested;
use crate::print::{print_order, text_string};
use crate::rebuild::{Rebuilder, run};
use crate::value::{Class, EvalError, Value};
use crate::{Trace, Unsupported};

/// A state as TLC prints it through the ALIAS.
#[derive(Clone, Debug)]
pub enum Alias {
    /// The fields of the record the alias gives, in the order TLC prints them: as written until
    /// TLC sorts the record (`RecordValue.snapshot`).
    Record(Vec<(String, Value)>),
    /// The alias gives no record, so TLC prints the state itself (`Value.toState` is null).
    State,
}

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
    pub fn alias(
        &mut self,
        trace: &Trace,
        cycle_start: Option<usize>,
        is_tool: bool,
    ) -> Result<Option<Vec<Alias>>, Unsupported> {
        let evaluator = self.evaluator();
        let ir = evaluator.ir;
        let Some(alias) = &ir.model.alias else {
            return Ok(None);
        };
        let Some(index) = alias.definition else {
            return unsupported("without a definition");
        };
        let body = evaluator.definition(ir.definitions[index as usize]).body;
        let context = run(evaluator.scope_context(ir.model.scope))?;
        let states = &trace.states;
        let state = |position: usize| states[position].values.iter().cloned().map(Some).collect();
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
            // TLC prints an alias that fails with its message as a field of the state
            // (`_ALIASEvalError`, `Tool.evalAlias`).
            let result = evaluator.evaluate(body, &context);
            evaluator.next_level = None;
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
                // TLC prints a function of strings as the record it converts it to
                // (`FcnRcdValue.toState`), but not one it keeps lazy.
                Value::Function(_) => return unsupported("function that isn't a record"),
                _ => Alias::State,
            });
        }
        Ok(Some(aliases))
    }
}
