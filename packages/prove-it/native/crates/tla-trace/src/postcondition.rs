//! TLC's check of a POSTCONDITION once the search is over (`findPostconditionViolation`): the
//! definition evaluated with no state, reading what TLCGet and TLCExt's CounterExample give then.

use std::collections::HashMap;

use tla_ir::{DefinitionForm, ScopeBinding};

use crate::alias::Alias;
use crate::eval::{Context, Evaluator, Runtime};
use crate::rebuild::{Rebuilder, run};
use crate::value::{Class, Value, set_of, sorted_function};
use crate::{Trace, Unsupported};

/// What TLC holds of the run when it checks a postcondition.
pub struct PostconditionInputs<'a> {
    /// Each `_POSSIBLE` predicate's name and how many states or steps satisfied it, in the
    /// model's order: -1 where TLC evaluated it on none.
    pub possible: &'a [(String, i64)],
    /// TLCGet("stats").
    pub stats: Stats,
    /// The trace TLC printed for a violation, which CounterExample records.
    pub counter_example: Option<CounterExample<'a>>,
}

/// The counts TLCGet("stats") gives, and the seconds the run took.
#[derive(Clone, Copy)]
pub struct Stats {
    pub queue: i64,
    pub distinct: i64,
    pub initial: i64,
    pub generated: i64,
    pub diameter: i64,
    pub duration: i64,
}

/// A violation's trace: its states with the actions of their steps, and for a lasso the state its
/// cycle starts at with the position in the model's actions of the step back to it, or none where
/// TLC holds no action for it, as for a lasso that stutters at its initial state.
pub struct CounterExample<'a> {
    pub trace: &'a Trace,
    pub cycle: Option<(usize, Option<u32>)>,
}

/// What TLC finds of a postcondition, and what it printed as TLC evaluated it.
#[derive(Debug, PartialEq, Eq)]
pub struct Checked {
    pub verdict: Verdict,
    pub printed: Vec<crate::OutputEvent>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Verdict {
    Holds,
    False,
    /// The message of the error TLC reports evaluating it, and as -tool nests it.
    Failed {
        text: String,
        tool_text: String,
    },
}

/// `EC.TLC_EXPECTED_VALUE`.
const EXPECTED_VALUE: u32 = 2215;

fn unsupported<T>(reason: &str) -> Result<T, Unsupported> {
    Err(Unsupported(format!("a postcondition {reason}")))
}

// `_Possible._Counts`: the count TLC took of each `_POSSIBLE` predicate it evaluated, by name,
// a function of the names TLC sorts as it prints it. Where `_Track` counted in the register
// "s:_possible" of TLC's one worker, the counts it holds, in the order `_Possible.counts`
// gives them: it merges each worker's normalized function into a `java.util.HashMap`, and
// builds the function from the map's entries as it iterates them, which it doesn't normalize.
fn possible_counts(
    evaluator: &Evaluator<'_>,
    possible: &[(String, i64)],
) -> Result<Value, Unsupported> {
    let register: Vec<u16> = "s:_possible".encode_utf16().collect();
    let tracked =
        evaluator.registers.named.iter().find(
            |(name, _)| matches!(name, Value::Str(text) if *text.units == *register.as_slice()),
        );
    if let Some((_, tracked)) = tracked {
        if possible.iter().any(|(_, count)| *count >= 0) {
            return unsupported("reading _POSSIBLE's counts and _Track's at once");
        }
        let Some(function) = tracked.as_function() else {
            return unsupported("reading a register _Track set that isn't a function");
        };
        let polynomial =
            tla_values::fingerprint::Polynomial::get(evaluator.ir.model.fingerprint_index);
        // `rec.normalize()`: the names in TLC's order of strings, the order it interned them in.
        let mut order = Vec::with_capacity(function.domain.len());
        for (position, name) in function.domain.iter().enumerate() {
            let Value::Str(text) = name else {
                return unsupported("reading a count _Track took of a name that isn't a string");
            };
            if text.rank < 0 {
                return unsupported(
                    "reading a count _Track took of a name TLC made as it searched",
                );
            }
            if !matches!(function.range[position], Value::Int(_)) {
                return unsupported("reading a count _Track took that isn't an integer");
            }
            order.push((text.rank, position));
        }
        order.sort_unstable();
        // `HashMap.merge` of each name, in that order, into a map of 16 buckets: before it adds
        // a name it doubles the map where it holds more than three quarters of its buckets, and
        // it puts the name at the head of its bucket (`newNode(hash, key, value, first)`).
        let mut buckets: Vec<Vec<(i32, usize)>> = vec![Vec::new(); 16];
        for &(_, position) in &order {
            let Value::Str(text) = &function.domain[position] else {
                return unsupported("reading a count _Track took of a name that isn't a string");
            };
            // `Value.hashCode`: the fingerprint's halves, xored.
            let fingerprint = polynomial.extend_int(
                polynomial.extend_byte(polynomial.value(), tla_values::fingerprint::STRING_VALUE),
                text.units.len() as i32,
            );
            let fingerprint = text.units.iter().fold(fingerprint, |fingerprint, &unit| {
                polynomial.extend_byte(fingerprint, unit as u8)
            });
            let hash = ((fingerprint >> 32) as i32) ^ (fingerprint as i32);
            let index = |hash: i32, capacity: usize| {
                let hash = hash as u32;
                ((hash ^ (hash >> 16)) as usize) & (capacity - 1)
            };
            let size: usize = buckets.iter().map(Vec::len).sum();
            if size > buckets.len() * 3 / 4 {
                // `HashMap.resize` keeps each bucket's order in the two it splits into.
                let capacity = buckets.len() * 2;
                let mut grown = vec![Vec::new(); capacity];
                for &(hash, position) in buckets.iter().flatten() {
                    grown[index(hash, capacity)].push((hash, position));
                }
                buckets = grown;
            }
            let at = index(hash, buckets.len());
            buckets[at].insert(0, (hash, position));
            // A bucket of eight names Java resizes or makes a tree of (`treeifyBin`).
            if buckets[at].len() >= 8 {
                return unsupported("reading counts _Track took in a crowded bucket");
            }
        }
        let (names, counts) = buckets
            .iter()
            .flatten()
            .map(|&(_, position)| {
                (
                    function.domain[position].clone(),
                    function.range[position].clone(),
                )
            })
            .unzip();
        return run(crate::value::written_function(names, counts, Class::Plain));
    }
    let mut names = Vec::new();
    let mut counts = Vec::new();
    for (name, count) in possible.iter().filter(|(_, count)| *count >= 0) {
        let Ok(count) = i32::try_from(*count) else {
            return unsupported("reading a count past an int");
        };
        names.push(Value::Str(evaluator.text_of(name.encode_utf16().collect())));
        counts.push(Value::Int(count));
    }
    run(sorted_function(names, counts, Class::Plain))
}

impl Rebuilder<'_> {
    /// What `_CheckName` prints as TLC finds a `_POSSIBLE` predicate the search didn't witness:
    /// `_Counts`, as PrintT prints it (`_Possible.tla`).
    pub fn possible_counts_printed(
        &mut self,
        possible: &[(String, i64)],
    ) -> Result<crate::OutputEvent, Unsupported> {
        let counts = possible_counts(self.evaluator(), possible)?;
        Ok(crate::OutputEvent::Print(vec![
            crate::print::format_printed(&counts),
        ]))
    }

    fn prepare_postconditions(
        &mut self,
        inputs: &PostconditionInputs<'_>,
    ) -> Result<(Option<Value>, Vec<crate::OutputEvent>), Unsupported> {
        let aliases = match &inputs.counter_example {
            Some(counter_example) if counter_example.cycle.is_none() => {
                self.alias(counter_example.trace, None, None, false)?
            }
            _ => None,
        };
        let counter_example = match &inputs.counter_example {
            Some(counter_example) => Some(self.counter_example_value(
                counter_example,
                aliases.as_deref(),
                false,
                false,
            )?),
            None => None,
        };
        let printed = aliases
            .as_ref()
            .into_iter()
            .flat_map(|aliases| aliases.output.iter().flatten())
            .cloned()
            .collect();
        Ok((counter_example, printed))
    }

    /// Evaluates one postcondition, preparing its counterexample once.
    pub fn postcondition(
        &mut self,
        index: usize,
        inputs: &PostconditionInputs<'_>,
    ) -> Result<Checked, Unsupported> {
        let (counter_example, printed) = self.prepare_postconditions(inputs)?;
        self.postcondition_prepared(index, inputs, counter_example, printed)
    }

    /// TLC evaluates ALIAS once before checking the postconditions against their shared counterexample.
    pub fn postconditions(
        &mut self,
        inputs: &PostconditionInputs<'_>,
    ) -> Result<Vec<Checked>, Unsupported> {
        let count = self.evaluator().ir.model.postconditions.len();
        if count == 0 {
            return Ok(Vec::new());
        }
        let (counter_example, mut printed) = self.prepare_postconditions(inputs)?;
        let mut results = Vec::new();
        for index in 0..count {
            let checked = self.postcondition_prepared(
                index,
                inputs,
                counter_example.clone(),
                std::mem::take(&mut printed),
            )?;
            let stops = checked.verdict != Verdict::Holds;
            results.push(checked);
            if stops {
                break;
            }
        }
        Ok(results)
    }

    /// Checks against the ALIAS values already evaluated for this worker counterexample.
    pub fn postconditions_using_aliases(
        &mut self,
        inputs: &PostconditionInputs<'_>,
        aliases: Option<&[Alias]>,
    ) -> Result<Vec<Checked>, Unsupported> {
        let count = self.evaluator().ir.model.postconditions.len();
        if count == 0 {
            return Ok(Vec::new());
        }
        let counter_example = match &inputs.counter_example {
            Some(counter_example) => {
                Some(self.counter_example_value(counter_example, aliases, false, false)?)
            }
            None => None,
        };
        let mut results = Vec::new();
        for index in 0..count {
            let checked =
                self.postcondition_prepared(index, inputs, counter_example.clone(), Vec::new())?;
            let stops = checked.verdict != Verdict::Holds;
            results.push(checked);
            if stops {
                break;
            }
        }
        Ok(results)
    }

    fn postcondition_prepared(
        &mut self,
        index: usize,
        inputs: &PostconditionInputs<'_>,
        counter_example: Option<Value>,
        mut prefix: Vec<crate::OutputEvent>,
    ) -> Result<Checked, Unsupported> {
        let evaluator = self.evaluator();
        let ir = evaluator.ir;
        let Some(definition) = ir
            .model
            .postconditions
            .get(index)
            .and_then(|postcondition| postcondition.definition)
        else {
            return unsupported("the IR doesn't define");
        };
        let text = |name: &str| Value::Str(evaluator.text_of(name.encode_utf16().collect()));
        let record = |fields: Vec<(&str, Value)>| {
            Value::record(
                fields
                    .into_iter()
                    .map(|(name, value)| (evaluator.counterexample_field(name, false), value))
                    .collect(),
            )
        };
        let int = |value: i64| i32::try_from(value).map(Value::Int);
        let Ok(stats) = [
            inputs.stats.queue,
            inputs.stats.distinct,
            inputs.stats.initial,
            inputs.stats.generated,
            inputs.stats.diameter,
            inputs.stats.duration,
        ]
        .map(int)
        .into_iter()
        .collect::<Result<Vec<_>, _>>() else {
            return unsupported("reading counts past an int");
        };
        let stats = run(record(
            [
                "queue",
                "distinct",
                "initial",
                "generated",
                "diameter",
                "duration",
            ]
            .into_iter()
            .zip(stats)
            .chain([("worker", Value::Int(0))])
            .collect(),
        ))?;
        // The named registers, each the tuple of one worker's value: those TLCSet set, and each
        // `_POSSIBLE` count TLC took, by name.
        let possible_counts = possible_counts(evaluator, inputs.possible)?;
        let (mut names, mut values): (Vec<_>, Vec<_>) = evaluator
            .registers
            .named
            .iter()
            .map(|(name, value)| (name.clone(), Value::tuple(vec![value.clone()])))
            .unzip();
        if inputs.possible.iter().any(|(_, count)| *count >= 0) {
            names.push(text("s:_possible"));
            values.push(Value::tuple(vec![possible_counts.clone()]));
        }
        let named = run(sorted_function(names, values, Class::Plain))?;
        let counter_example = match counter_example {
            Some(counter_example) => counter_example,
            None => run(Value::counter_example(
                vec![
                    ("action", Value::empty_set()),
                    ("state", Value::empty_set()),
                ]
                .into_iter()
                .map(|(name, value)| (evaluator.counterexample_field(name, false), value))
                .collect(),
            ))?,
        };
        let body = evaluator
            .definition(ir.definitions[definition as usize])
            .body;
        let width = ir.variables.len();
        evaluator.current = vec![None; width];
        evaluator.next = vec![None; width];
        evaluator.level = 0;
        evaluator.printed.clear();
        evaluator.runtime = Some(Runtime {
            named,
            stats,
            counter_example,
            possible_counts,
        });
        let result = evaluator.evaluate(body, &Context::default());
        evaluator.runtime = None;
        prefix.append(&mut evaluator.printed);
        let printed = prefix;
        // TLCGet("stats").duration counts the seconds since TLC started (`AbstractChecker`),
        // which the JVM's own start makes longer than the checker's; a postcondition that shows
        // the record words a time the checker can't give as TLC does.
        let is_timed = |text: &str| text.contains("duration |-> ");
        if printed.iter().any(|event| {
            matches!(event, crate::OutputEvent::Print(texts) if texts.iter().any(|text| is_timed(text)))
        })
            || matches!(&result, Err(error) if error.message.as_ref().is_some_and(|message| is_timed(&message.text)))
        {
            return unsupported("that shows how long TLC ran");
        }
        let verdict = match result {
            Ok(Value::Bool(true)) => Verdict::Holds,
            Ok(Value::Bool(false)) => Verdict::False,
            // `Tool.isValid` fails on a value that is no boolean, naming the body as SANY's
            // `toString` does: a numeral by its image, else by where it is written.
            Ok(_) => match evaluator.describe_node(body) {
                Some(written) => {
                    let message = crate::value::TlcMessage {
                        text: format!(
                            "TLC expected a boolean value, but did not find one. {written}"
                        ),
                        code: Some(EXPECTED_VALUE),
                        is_eval_exception: false,
                        inner: None,
                    };
                    Verdict::Failed {
                        tool_text: crate::failure::nested(&message),
                        text: message.text,
                    }
                }
                None => return unsupported("that isn't a boolean"),
            },
            Err(error) => match error.message {
                Some(message) => Verdict::Failed {
                    tool_text: crate::failure::nested(&message),
                    text: message.text,
                },
                None => return Err(Unsupported(format!("a postcondition: {}", error.reason))),
            },
        };
        Ok(Checked { verdict, printed })
    }

    /// CounterExample's record of a violation's trace (`tlc2.value.impl.CounterExample`): each
    /// state as the tuple of its number and its record, through the ALIAS where `aliases` has it,
    /// and each step as the tuple of its states with its action's record between them. A trace
    /// TLC dumps (`is_dumped`) ranks the field names as the trace modules intern them, and with
    /// `is_sharing_followed` declines a parameter TLC may share with a state.
    pub(crate) fn counter_example_value(
        &mut self,
        counter_example: &CounterExample<'_>,
        aliases: Option<&[Alias]>,
        is_dumped: bool,
        is_sharing_followed: bool,
    ) -> Result<Value, Unsupported> {
        let evaluator = self.evaluator();
        let ir = evaluator.ir;
        // The values TLC binds the parameters of each action of the trace's steps to.
        let mut parameters = HashMap::new();
        {
            let positions = counter_example
                .trace
                .states
                .iter()
                .skip(1)
                .map(|state| state.action)
                .chain(counter_example.cycle.map(|(_, closing)| closing));
            for position in positions.flatten() {
                if let (Some(action), None) = (
                    ir.model.actions.get(position as usize),
                    parameters.get(&position),
                ) {
                    let bound = action_parameters(evaluator, action)?;
                    parameters.insert(position, bound);
                }
            }
        }
        let text = |name: &str| Value::Str(evaluator.text_of(name.encode_utf16().collect()));
        let record = |fields: Vec<(&str, Value)>| {
            Value::record(
                fields
                    .into_iter()
                    .map(|(name, value)| (evaluator.counterexample_field(name, is_dumped), value))
                    .collect(),
            )
        };
        let states = counter_example
            .trace
            .states
            .iter()
            .enumerate()
            .map(|(position, state)| {
                if let Some(Alias::Record(fields)) =
                    aliases.as_ref().map(|aliases| &aliases[position])
                {
                    // Where the ALIAS fails, TLC adds the error's message to the state's record
                    // (`Tool.evalAlias`); the binary trace file holds it as the evaluator words it.
                    if fields.iter().any(|(name, _)| name == "_ALIASEvalError")
                        && (!is_dumped || is_sharing_followed)
                    {
                        return unsupported("of a model whose ALIAS fails");
                    }
                    let fields = fields
                        .iter()
                        .map(|(name, value)| {
                            (
                                evaluator.text_of(name.encode_utf16().collect()),
                                value.clone(),
                            )
                        })
                        .collect();
                    return Ok(Value::tuple(vec![
                        Value::Int(position as i32 + 1),
                        run(Value::record(fields))?,
                    ]));
                }
                let fields = ir
                    .tlc_order
                    .iter()
                    .map(|&variable| {
                        (
                            evaluator.text_of(
                                ir.texts[ir.variables[variable as usize] as usize]
                                    .encode_utf16()
                                    .collect(),
                            ),
                            state.values[variable as usize].clone(),
                        )
                    })
                    .collect();
                Ok(Value::tuple(vec![
                    Value::Int(position as i32 + 1),
                    run(Value::record(fields))?,
                ]))
            })
            .collect::<Result<Vec<_>, Unsupported>>()?;
        // TLC records each step with its action's name and location.
        let action = |position: Option<u32>| {
            let Some(action) =
                position.and_then(|position| ir.model.actions.get(position as usize))
            else {
                return unsupported("of a step whose action the trace lacks");
            };
            // TLC records the name and location its action holds (`TLCStateInfo`).
            let name = &ir.texts[action.name as usize];
            let Some(range) = action.location else {
                return unsupported("of an action without a location");
            };
            let location = run(record(vec![
                ("beginLine", Value::Int(range.start_line)),
                ("beginColumn", Value::Int(range.start_column)),
                ("endLine", Value::Int(range.end_line)),
                ("endColumn", Value::Int(range.end_column)),
                ("module", text(&ir.texts[range.module as usize])),
            ]))?;
            let mut fields = vec![("name", text(name)), ("location", location)];
            // TLC adds the parameters bound to values, by name and in order.
            let bound = position.and_then(|position| parameters.get(&position));
            if let Some(bound) = bound.filter(|bound| !bound.is_empty()) {
                // A dump writes a value TLC wrote before as a reference to it, and TLC binds a
                // parameter to the very value its set holds, which a state may hold too.
                let is_shareable = |value: &Value| {
                    !matches!(
                        value,
                        Value::Bool(_) | Value::Int(_) | Value::Model(_) | Value::Interval(..)
                    )
                };
                if is_sharing_followed && bound.iter().any(|(_, value)| is_shareable(value)) {
                    return unsupported("dumped with an action's parameter TLC may share");
                }
                let context = bound
                    .iter()
                    .map(|(name, value)| (*name, value.clone()))
                    .collect();
                let names = bound.iter().map(|(name, _)| text(name)).collect();
                fields.push(("context", run(record(context))?));
                fields.push(("parameters", Value::tuple(names)));
            }
            run(record(fields))
        };
        let mut steps = Vec::new();
        for position in 1..states.len() {
            steps.push(Value::tuple(vec![
                states[position - 1].clone(),
                action(counter_example.trace.states[position].action)?,
                states[position].clone(),
            ]));
        }
        if let Some((start, closing)) = counter_example.cycle {
            let (Some(last), Some(first)) = (states.last(), states.get(start)) else {
                return unsupported("of a lasso outside its trace");
            };
            // TLC records a step it holds no action for as `Action.UNKNOWN`'s: unnamed, at
            // the null location.
            let closing = match closing {
                Some(closing) => action(Some(closing))?,
                None => {
                    let location = run(record(vec![
                        ("beginLine", Value::Int(0)),
                        ("beginColumn", Value::Int(0)),
                        ("endLine", Value::Int(0)),
                        ("endColumn", Value::Int(0)),
                        ("module", text("--TLA+ BUILTINS--")),
                    ]))?;
                    run(record(vec![
                        ("name", text("UnnamedAction")),
                        ("location", location),
                    ]))?
                }
            };
            steps.push(Value::tuple(vec![last.clone(), closing, first.clone()]));
        }
        let fields = vec![
            ("action", run(set_of(steps))?),
            ("state", run(set_of(states))?),
        ];
        run(Value::counter_example(
            fields
                .into_iter()
                .map(|(name, value)| (evaluator.counterexample_field(name, is_dumped), value))
                .collect(),
        ))
    }
}

// The parameters of the operator TLC splits an action from (`Action.getParameters`), with the
// values the action's scope binds them to.
fn action_parameters<'ir>(
    evaluator: &mut Evaluator<'ir>,
    action: &tla_ir::Action,
) -> Result<Vec<(&'ir str, Value)>, Unsupported> {
    let ir = evaluator.ir;
    // The operator TLC split the action from, whose parameters the action's scope binds. None
    // stands for an action of no operator, which has no parameters, or for an operator a LET
    // defines, which a label naming the values of parameters gives away.
    let Some(index) = action.definition else {
        return if ir.texts[action.label as usize].contains('(') {
            unsupported("of an action of an operator a LET defines")
        } else {
            Ok(Vec::new())
        };
    };
    let DefinitionForm::Operator(params) =
        &evaluator.definition(ir.definitions[index as usize]).form
    else {
        return unsupported("of an action of a function definition");
    };
    let mut bound = Vec::with_capacity(params.len());
    for param in params {
        // The innermost binding of the parameter's name in the action's scope.
        let mut scope = action.scope;
        let binding = loop {
            let Some(index) = scope else {
                break None;
            };
            let entry = &ir.scopes[index as usize];
            if entry.name == param.name {
                break Some(&entry.binding);
            }
            scope = entry.parent;
        };
        match binding {
            Some(ScopeBinding::Value(Some(value))) => {
                bound.push((
                    &*ir.texts[param.name as usize],
                    run(evaluator.value(*value))?,
                ));
            }
            // TLC leaves out a parameter bound to an operator.
            Some(ScopeBinding::Closure { .. }) => {}
            _ => return unsupported("of an action whose parameters its scope doesn't bind"),
        }
    }
    Ok(bound)
}
