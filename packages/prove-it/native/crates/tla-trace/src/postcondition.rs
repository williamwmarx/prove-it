//! TLC's check of a POSTCONDITION once the search is over (`findPostconditionViolation`): the
//! definition evaluated with no state, reading what TLCGet and TLCExt's CounterExample give then.

use crate::eval::{Context, Runtime};
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
/// cycle starts at with the position in the model's actions of the step back to it.
pub struct CounterExample<'a> {
    pub trace: &'a Trace,
    pub cycle: Option<(usize, u32)>,
}

/// What TLC finds of a postcondition, and what it printed as TLC evaluated it.
#[derive(Debug, PartialEq, Eq)]
pub struct Checked {
    pub verdict: Verdict,
    pub printed: Vec<Vec<String>>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Verdict {
    Holds,
    False,
    /// The message of the error TLC reports evaluating it.
    Failed(String),
}

fn unsupported<T>(reason: &str) -> Result<T, Unsupported> {
    Err(Unsupported(format!("a postcondition {reason}")))
}

impl Rebuilder<'_> {
    /// Evaluates the model's postcondition at `index` as TLC checks it.
    pub fn postcondition(
        &mut self,
        index: usize,
        inputs: &PostconditionInputs<'_>,
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
        // The module the postcondition is defined in, the spec's.
        let module = ir.nodes.arena[evaluator
            .definition(ir.definitions[definition as usize])
            .body as usize]
            .range
            .map(|range| range.module);
        let text = |name: &str| Value::Str(evaluator.text_of(name.encode_utf16().collect()));
        let record = |fields: Vec<(&str, Value)>| {
            Value::record(
                fields
                    .into_iter()
                    .map(|(name, value)| (evaluator.text_of(name.encode_utf16().collect()), value))
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
        // The named registers hold each `_POSSIBLE` count TLC took, by name.
        let counted: Vec<_> = inputs
            .possible
            .iter()
            .filter(|(_, count)| *count >= 0)
            .collect();
        let named = if counted.is_empty() {
            run(sorted_function(Vec::new(), Vec::new(), Class::Plain))?
        } else {
            let mut counts = Vec::with_capacity(counted.len());
            for (_, count) in &counted {
                let Ok(count) = int(*count) else {
                    return unsupported("reading a count past an int");
                };
                counts.push(count);
            }
            let names = counted.iter().map(|(name, _)| text(name)).collect();
            let counts = run(sorted_function(names, counts, Class::Plain))?;
            run(sorted_function(
                vec![text("s:_possible")],
                vec![Value::tuple(vec![counts])],
                Class::Plain,
            ))?
        };
        let counter_example = match &inputs.counter_example {
            None => run(record(vec![
                ("action", Value::empty_set()),
                ("state", Value::empty_set()),
            ]))?,
            Some(counter_example) => {
                let states = counter_example
                    .trace
                    .states
                    .iter()
                    .enumerate()
                    .map(|(position, state)| {
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
                    if action.scope.is_some() {
                        return unsupported("of an action with parameters");
                    }
                    let label = &ir.texts[action.label as usize];
                    // A label names an action with the values of its parameters, which the
                    // record holds apart.
                    let name = label.split(" line ").next().unwrap_or(label);
                    if name.contains('(') {
                        return unsupported("of an action with parameters");
                    }
                    let Some(range) = ir.nodes.arena[action.expression as usize].range else {
                        return unsupported("of an action without a range");
                    };
                    // TLC records an action another module defines, as through an INSTANCE, as
                    // the unnamed action of the statement that brings it in, which the IR
                    // doesn't carry.
                    if Some(range.module) != module {
                        return unsupported("of an action another module defines");
                    }
                    let location = run(record(vec![
                        ("beginLine", Value::Int(range.start_line)),
                        ("beginColumn", Value::Int(range.start_column)),
                        ("endLine", Value::Int(range.end_line)),
                        ("endColumn", Value::Int(range.end_column)),
                        ("module", text(&ir.texts[range.module as usize])),
                    ]))?;
                    run(record(vec![("name", text(name)), ("location", location)]))
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
                    steps.push(Value::tuple(vec![
                        last.clone(),
                        action(Some(closing))?,
                        first.clone(),
                    ]));
                }
                run(record(vec![
                    ("action", run(set_of(steps))?),
                    ("state", run(set_of(states))?),
                ]))?
            }
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
        });
        let result = evaluator.evaluate(body, &Context::default());
        evaluator.runtime = None;
        let printed = std::mem::take(&mut evaluator.printed);
        let verdict = match result {
            Ok(Value::Bool(true)) => Verdict::Holds,
            Ok(Value::Bool(false)) => Verdict::False,
            Ok(_) => return unsupported("that isn't a boolean"),
            Err(error) => match error.message {
                Some(message) => Verdict::Failed(message.text),
                None => return Err(Unsupported(format!("a postcondition: {}", error.reason))),
            },
        };
        Ok(Checked { verdict, printed })
    }
}
