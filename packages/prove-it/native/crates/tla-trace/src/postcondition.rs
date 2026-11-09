//! TLC's check of a POSTCONDITION once the search is over (`findPostconditionViolation`): the
//! definition evaluated with no state, reading what TLCGet and TLCExt's CounterExample give then.

use std::collections::HashMap;

use tla_ir::{DefinitionForm, ScopeBinding};

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
        // The values TLC binds the parameters of each action of the trace's steps to.
        let mut parameters = HashMap::new();
        if let Some(counter_example) = &inputs.counter_example {
            let positions = counter_example
                .trace
                .states
                .iter()
                .skip(1)
                .map(|state| state.action)
                .chain(counter_example.cycle.map(|(_, closing)| Some(closing)));
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
        // The named registers, each the tuple of one worker's value: those TLCSet set, and each
        // `_POSSIBLE` count TLC took, by name.
        let counted: Vec<_> = inputs
            .possible
            .iter()
            .filter(|(_, count)| *count >= 0)
            .collect();
        let (mut names, mut values): (Vec<_>, Vec<_>) = evaluator
            .registers
            .named
            .iter()
            .map(|(name, value)| (name.clone(), Value::tuple(vec![value.clone()])))
            .unzip();
        let possible_counts = if counted.is_empty() {
            run(sorted_function(Vec::new(), Vec::new(), Class::Plain))?
        } else {
            let mut counts = Vec::with_capacity(counted.len());
            for (_, count) in &counted {
                let Ok(count) = int(*count) else {
                    return unsupported("reading a count past an int");
                };
                counts.push(count);
            }
            let counted_names = counted.iter().map(|(name, _)| text(name)).collect();
            let counts = run(sorted_function(counted_names, counts, Class::Plain))?;
            names.push(text("s:_possible"));
            values.push(Value::tuple(vec![counts.clone()]));
            counts
        };
        let named = run(sorted_function(names, values, Class::Plain))?;
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
            possible_counts,
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

// The parameters of the operator TLC splits an action from (`Action.getParameters`), with the
// values the action's scope binds them to.
fn action_parameters<'ir>(
    evaluator: &mut Evaluator<'ir>,
    action: &tla_ir::Action,
) -> Result<Vec<(&'ir str, Value)>, Unsupported> {
    let ir = evaluator.ir;
    // A label names the values of an action's parameters, and an action of no operator has
    // none.
    let name = &*ir.texts[action.name as usize];
    if !ir.texts[action.label as usize].contains('(') || name == "UnnamedAction" {
        return Ok(Vec::new());
    }
    let operators: Vec<_> = ir
        .definitions
        .iter()
        .map(|&node| evaluator.definition(node))
        .filter(|definition| {
            &*ir.texts[definition.name as usize] == name
                && matches!(definition.form, DefinitionForm::Operator(_))
        })
        .collect();
    // Where several operators share the name, as in a LET, the action's is the one whose body it
    // is.
    let operator = match operators[..] {
        [operator] => operator,
        _ => match operators
            .iter()
            .find(|definition| definition.body == action.expression)
        {
            Some(operator) => operator,
            None => return unsupported("of an action whose operator the IR doesn't single out"),
        },
    };
    let DefinitionForm::Operator(params) = &operator.form else {
        return unsupported("of an action whose operator the IR doesn't single out");
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
