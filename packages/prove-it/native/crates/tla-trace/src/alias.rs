//! A trace's states as TLC prints them through the configuration's ALIAS (`Tool.evalAlias`): the
//! alias evaluated at each state, with the state after it as the next state, and printed as the
//! record it gives (`RecordValue.toState`).

use crate::eval::{TraceContext, TracePrefix};
use crate::failure::nested;
use crate::print::{print_order, text_string};
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

/// ALIAS values and the output produced while evaluating each corresponding state.
#[derive(Clone, Debug)]
pub struct Aliases {
    pub values: Vec<Alias>,
    pub output: Vec<Vec<crate::OutputEvent>>,
}

impl std::ops::Deref for Aliases {
    type Target = [Alias];
    fn deref(&self) -> &Self::Target {
        &self.values
    }
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
    /// Worker.doPostCondition uses ordinary Java Trace, without the print-time supplier.
    pub fn worker_alias(
        &mut self,
        trace: &Trace,
        workers: Option<usize>,
        is_tool: bool,
    ) -> Result<Option<Aliases>, Unsupported> {
        let ir = self.evaluator().ir;
        let changes_context = ir.builtins.iter().any(|builtin| {
            matches!(
                &*ir.texts[builtin.name as usize],
                "RandomElement"
                    | "RandomSubset"
                    | "RandomSubsetSet"
                    | "RandomSetOfSubsets"
                    | "TestRandomSetOfSubsets"
                    | "TLCSet"
                    | "TLCGetAndSet"
                    | "_Track"
            )
        });
        let observed = trace
            .quiet_prefixes
            .as_ref()
            .filter(|prefixes| prefixes.len() == trace.states.len());
        let contexts: Vec<_> = (0..trace.states.len())
            .map(|position| {
                if observed.is_none() {
                    TraceContext::Unfollowed
                } else if position == 0 {
                    TraceContext::WorkerPrefix(1)
                } else if position + 1 == trace.states.len() {
                    // Tool.getState's last successor has no trace record: its worker id
                    // remains Short.MAX_VALUE (ConcurrentTLCTrace.Record.getRecord).
                    match workers.filter(|&count| count > 0 && count <= i16::MAX as usize) {
                        Some(workers) => TraceContext::WorkerUnrecorded { workers },
                        None => TraceContext::Unfollowed,
                    }
                } else if !changes_context && observed.is_some_and(|quiet| quiet[position]) {
                    TraceContext::WorkerPrefix(position + 1)
                } else {
                    TraceContext::Unfollowed
                }
            })
            .collect();
        self.alias_with_context(trace, None, Some(&contexts), is_tool)
    }

    /// Each state of a rebuilt trace as TLC prints it through the ALIAS, or `None` without one.
    /// TLC evaluates the alias with TLCGet("level") at the state's position in the trace, and the
    /// state after it as the next state: for a lasso's last state, the state its cycle starts at
    /// (`cycle_start`), and otherwise the state itself.
    /// An alias that fails to evaluate gives the state with TLC's message of the failure as its
    /// `_ALIASEvalError` field, marked as TLC marks a coded message under `-tool`.
    /// TLC binds the builtin Trace at each position to the trace's first states, as many as
    /// `prefixes` says; with no `prefixes`, the alias isn't followed where it reads Trace.
    pub fn alias(
        &mut self,
        trace: &Trace,
        cycle_start: Option<usize>,
        prefixes: Option<&[usize]>,
        is_tool: bool,
    ) -> Result<Option<Aliases>, Unsupported> {
        let contexts = prefixes.map(|prefixes| {
            prefixes
                .iter()
                .copied()
                .map(TraceContext::Printed)
                .collect::<Vec<_>>()
        });
        self.alias_with_context(trace, cycle_start, contexts.as_deref(), is_tool)
    }

    fn alias_with_context(
        &mut self,
        trace: &Trace,
        cycle_start: Option<usize>,
        contexts: Option<&[TraceContext]>,
        is_tool: bool,
    ) -> Result<Option<Aliases>, Unsupported> {
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
            inner: None,
        };
        // TLC finds the alias by its name as it evaluates it, and fails on a name it has no
        // definition of, on a definition that takes arguments and on one it computed as it
        // started (`Spec.getAliasSpec`).
        let defined = alias
            .definition
            .map(|index| (index, evaluator.definition(ir.definitions[index as usize])));
        // TLC holds a name the configuration assigns as its value (`SpecProcessor.processConstants`),
        // unless the configuration also substitutes a definition for it, which TLC applies after.
        let is_substituted = |definition: &Definition| ir.texts[definition.name as usize] != *name;
        let is_assigned = (ir.constants.iter())
            .any(|constant| ir.texts[constant.name as usize] == *name)
            && !defined
                .as_ref()
                .is_some_and(|(_, definition)| is_substituted(definition));
        let body = match defined {
            _ if is_assigned => Err(rejected(
                format!("The alias {name} cannot be a constant."),
                MUST_NOT_BE_CONSTANT,
            )),
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
                // TLC holds the definition a name the configuration substitutes for names, which
                // it computed as it started in its own name only (`SpecProcessor.processSpec`).
                if !is_substituted(definition)
                    && Rebuilder::new(ir)?.is_computed_at_startup(index)?
                {
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
        for state in states.iter().filter(|_| contexts.is_some()) {
            let fields = ir
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
            records.push(run(Value::record(fields))?);
        }
        let records: std::rc::Rc<[Value]> = records.into();
        let mut aliases = Vec::with_capacity(states.len());
        let mut output = Vec::with_capacity(states.len());
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
            evaluator.trace = contexts.map(|contexts| TracePrefix {
                records: records.clone(),
                context: contexts[position],
            });
            let lazy_body_effects = evaluator.lazy_body_effects();
            // TLC prints an alias that fails with its message as a field of the state
            // (`_ALIASEvalError`, `Tool.evalAlias`).
            let result = match &body {
                Ok(body) => evaluator.evaluate(*body, &context),
                Err(message) => Err(EvalError {
                    runtime_exception: crate::value::RuntimeException::Runtime,
                    is_set_normalization: false,
                    is_set_reduction: false,
                    is_followed_comparison: false,
                    is_named_normalization: false,
                    reason: "an ALIAS TLC rejects".into(),
                    message: Some(message.clone()),
                }),
            };
            evaluator.next_level = None;
            evaluator.trace = None;
            output.push(std::mem::take(&mut evaluator.printed));
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
            // TLC prints the alias as it holds it, unnormalized: a function `@@` built holds its
            // keys in the order of the arguments' (`CombineFcn`), which the evaluator doesn't
            // keep. Main printed it sorted too, but declined an alias that prints.
            if (evaluator.lazy_body_effects() != lazy_body_effects
                || output.last().is_some_and(|printed| {
                    printed
                        .iter()
                        .any(|event| matches!(event, crate::OutputEvent::Print(_)))
                }))
                && crate::eval::holds_unknown_function_order(&value)
            {
                return unsupported("that prints and holds a function of unknown key order");
            }
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
                    // TLC normalizes a set enumeration to print it, and reports the exception where
                    // its elements don't compare, in place of the states.
                    if fields.iter().any(|(_, value)| holds_unsorted(value)) {
                        return unsupported("of a set TLC fails to normalize as it prints it");
                    }
                    Alias::Record(fields)
                }
                // TLC prints a function of strings as the record it converts it to
                // (`FcnRcdValue.toState`, `toRcd`), and the state itself for any other function:
                // one of other keys, one over an interval, a tuple, or one it keeps lazy, which
                // has no state of its own (`Value.toState`).
                Value::Function(function)
                    if is_fcn_rcd(function)
                        && !function.domain.is_empty()
                        && function
                            .domain
                            .iter()
                            .all(|key| matches!(key, Value::Str(_))) =>
                {
                    let fields: Vec<_> = print_order(function, true)
                        .into_iter()
                        .map(|position| match &function.domain[position] {
                            Value::Str(name) => {
                                (text_string(&name.units), function.range[position].clone())
                            }
                            _ => unreachable!("a key that is a string"),
                        })
                        .collect();
                    if fields.iter().any(|(name, _)| name == "_format") {
                        return unsupported("record with a _format field");
                    }
                    if fields.iter().any(|(_, value)| holds_unsorted(value)) {
                        return unsupported("of a set TLC fails to normalize as it prints it");
                    }
                    Alias::Record(fields)
                }
                Value::Function(function) if function.domain.is_empty() => {
                    return unsupported("function of no keys");
                }
                Value::Function(function)
                    if function.class.get() != Class::Tuple
                        && function
                            .domain
                            .iter()
                            .any(|key| matches!(key, Value::Str(_))) =>
                {
                    return unsupported("function of strings TLC may keep lazy");
                }
                _ => Alias::State,
            });
            // TLC prints a state with the fingerprint of its alias (`TLCStateInfo.fingerPrint`),
            // which it computes where the state it rebuilt has none: each state after the first,
            // and the first of a trace of two, which TLC prints from the states it holds
            // (`TLCTrace.printTrace`). It fingerprints the state of the record's fields named as
            // the variables, where there is one for each (`RecordValue.toState`,
            // `PrintTLCState.allAssigned`): a function it keeps lazy over a domain it can't count
            // fails there (`FcnLambdaValue.fingerPrint`), as does a set it can't enumerate, and
            // TLC reports the exception in place of the rest of the trace, which the printing
            // doesn't follow.
            if (position > 0 || states.len() == 2)
                && let Some(Alias::Record(fields)) = aliases.last()
            {
                let variables: Vec<&Value> = ir
                    .variables
                    .iter()
                    .filter_map(|&name| {
                        let name = &ir.texts[name as usize];
                        fields
                            .iter()
                            .find(|(field, _)| **field == **name)
                            .map(|(_, value)| value)
                    })
                    .collect();
                if variables.len() == ir.variables.len()
                    && variables.into_iter().any(may_fail_fingerprint)
                {
                    return unsupported(
                        "whose state of the variables TLC may fail to fingerprint as it prints it",
                    );
                }
            }
        }
        Ok(Some(Aliases {
            values: aliases,
            output,
        }))
    }
}

// Whether TLC holds a function as a `FcnRcdValue`: one it built, rather than kept lazy.
fn is_fcn_rcd(function: &crate::value::Function) -> bool {
    function.class.get() == Class::Plain
        || function.class.get() == Class::Lambda && function.java_class.get() == Some(Class::Plain)
}

// Whether a value holds one whose fingerprint fails or may fail: a function TLC keeps lazy over a
// domain it can't count, a set TLC keeps lazy that the evaluator doesn't know to be finite, or
// one whose fingerprint fails (`fingerprint_failure`).
fn may_fail_fingerprint(value: &Value) -> bool {
    !is_countable(value) || matches!(crate::fingerprint::fingerprint_failure(value), Ok(Some(_)))
}

// Whether a value is built of finite sets and functions only, by the sets it is built from, and
// of no union TLC keeps lazy.
fn is_countable(value: &Value) -> bool {
    use crate::value::Lazy;
    match value {
        Value::Lambda(_) => false,
        Value::Lazy(lazy) => match &***lazy {
            Lazy::Subset(base) => is_countable(base),
            Lazy::FunctionSet(domain, range) => is_countable(domain) && is_countable(range),
            Lazy::RecordSet(fields, _) => fields.iter().all(|(_, set)| is_countable(set)),
            Lazy::Product(sets) => sets.iter().all(is_countable),
            Lazy::Cap(left, right) | Lazy::Cup(left, right) | Lazy::Diff(left, right) => {
                is_countable(left) && is_countable(right)
            }
            Lazy::Nat
            | Lazy::Int
            | Lazy::Real
            | Lazy::Strings
            | Lazy::Seq(_)
            | Lazy::Any
            | Lazy::Filter(..) => false,
            // TLC fingerprints a union by the set it enumerates of the elements of its sets
            // (`UnionValue.toSetEnum`), which fails where it can't sort them, as `fingerprint_failure`
            // doesn't follow.
            Lazy::Union(_) => false,
        },
        Value::Set(elements) | Value::Unsorted(elements) => elements.iter().all(is_countable),
        Value::Function(function) => function
            .domain
            .iter()
            .chain(&function.range)
            .all(is_countable),
        _ => true,
    }
}

// Whether a value holds a set enumeration whose elements TLC can't sort.
fn holds_unsorted(value: &Value) -> bool {
    match value {
        Value::Unsorted(_) => true,
        Value::Set(elements) => elements.iter().any(holds_unsorted),
        Value::Function(function) => function
            .domain
            .iter()
            .chain(&function.range)
            .any(holds_unsorted),
        _ => false,
    }
}
