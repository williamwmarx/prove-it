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
    pub printed: Vec<Vec<String>>,
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
        // TLC builds a safety violation's counterexample from the ALIAS of each state, the last
        // state's with itself as the next (`Worker.doPostCondition`, `evalAlias`), and a
        // liveness checker's lasso from the states.
        let aliases = match &inputs.counter_example {
            Some(counter_example) if counter_example.cycle.is_none() => {
                self.alias(counter_example.trace, None, None, false, false, None)?
            }
            _ => None,
        };
        let counter_example = match &inputs.counter_example {
            Some(counter_example) => {
                Some(self.counter_example_value(counter_example, aliases.as_deref(), false)?)
            }
            None => None,
        };
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
        let stats = stats_record(evaluator, &inputs.stats)?;
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
        let counter_example = match counter_example {
            Some(counter_example) => counter_example,
            None => run(record(vec![
                ("action", Value::empty_set()),
                ("state", Value::empty_set()),
            ]))?,
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
            named: Some(named),
            stats,
            counter_example: Some(counter_example),
            possible_counts: Some(possible_counts),
        });
        let result = evaluator.evaluate(body, &Context::default());
        evaluator.runtime = None;
        let printed = std::mem::take(&mut evaluator.printed);
        let verdict = match result {
            Ok(Value::Bool(true)) => Verdict::Holds,
            Ok(Value::Bool(false)) => Verdict::False,
            Ok(_) => return unsupported("that isn't a boolean"),
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
    /// TLC dumps (`is_dumped`) ranks the field names as the trace modules intern them.
    pub(crate) fn counter_example_value(
        &mut self,
        counter_example: &CounterExample<'_>,
        aliases: Option<&[Alias]>,
        is_dumped: bool,
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
                    if fields.iter().any(|(name, _)| name == "_ALIASEvalError") {
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
            let bound = position
                .and_then(|position| parameters.get(&position))
                .map_or(&[][..], Vec::as_slice);
            action_record(evaluator, action, bound, is_dumped)
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
        run(record(vec![
            ("action", run(set_of(steps))?),
            ("state", run(set_of(states))?),
        ]))
    }
}

/// TLCGet("stats") (`AbstractChecker.getStatistics`), as the main thread reads it: worker 0.
pub(crate) fn stats_record(evaluator: &Evaluator<'_>, stats: &Stats) -> Result<Value, Unsupported> {
    let Ok(counts) = [
        stats.queue,
        stats.distinct,
        stats.initial,
        stats.generated,
        stats.diameter,
        stats.duration,
    ]
    .map(|count| i32::try_from(count).map(Value::Int))
    .into_iter()
    .collect::<Result<Vec<_>, _>>() else {
        return Err(Unsupported(
            "TLCGet(\"stats\") of counts past an int".into(),
        ));
    };
    run(Value::record(
        [
            "queue",
            "distinct",
            "initial",
            "generated",
            "diameter",
            "duration",
        ]
        .into_iter()
        .zip(counts)
        .chain([("worker", Value::Int(0))])
        .map(|(name, value)| (evaluator.counterexample_field(name, false), value))
        .collect(),
    ))
}

/// TLC's record of the action that took a step (`RecordValue(Action)`, as `TLCStateInfo` holds
/// it): its name and location, and the values `bound` gives its operator's parameters, by name and
/// in order.
pub(crate) fn action_record(
    evaluator: &Evaluator<'_>,
    action: &tla_ir::Action,
    bound: &[(&str, Value)],
    is_dumped: bool,
) -> Result<Value, Unsupported> {
    let ir = evaluator.ir;
    let Some(range) = action.location else {
        return unsupported("of an action without a location");
    };
    let site = InitialAction {
        name: ir.texts[action.name as usize].to_string(),
        module: ir.texts[range.module as usize].to_string(),
        lines: [
            range.start_line,
            range.start_column,
            range.end_line,
            range.end_column,
        ],
    };
    site_record(evaluator, &site, bound, is_dumped)
}

/// The initial predicate TLC's simulation gives each initial state as its action
/// (`Tool.getInitStates`), as TLC's `Action` names it, and where it is written: its module and
/// its first line and column, then its last.
pub struct InitialAction {
    pub name: String,
    pub module: String,
    pub lines: [i32; 4],
}

// TLC's record of an action named and placed as `site` says, with the values `bound` gives its
// operator's parameters.
pub(crate) fn site_record(
    evaluator: &Evaluator<'_>,
    site: &InitialAction,
    bound: &[(&str, Value)],
    is_dumped: bool,
) -> Result<Value, Unsupported> {
    let text = |name: &str| Value::Str(evaluator.text_of(name.encode_utf16().collect()));
    let record = |fields: Vec<(&str, Value)>| {
        Value::record(
            fields
                .into_iter()
                .map(|(name, value)| (evaluator.counterexample_field(name, is_dumped), value))
                .collect(),
        )
    };
    let [begin_line, begin_column, end_line, end_column] = site.lines;
    let location = run(record(vec![
        ("beginLine", Value::Int(begin_line)),
        ("beginColumn", Value::Int(begin_column)),
        ("endLine", Value::Int(end_line)),
        ("endColumn", Value::Int(end_column)),
        ("module", text(&site.module)),
    ]))?;
    let mut fields = vec![("name", text(&site.name)), ("location", location)];
    // TLC adds the parameters bound to values, by name and in order.
    if !bound.is_empty() {
        // A dump writes a value TLC wrote before as a reference to it, and TLC binds a parameter
        // to the very value its set holds, which a state may hold too.
        let is_shareable = |value: &Value| {
            !matches!(
                value,
                Value::Bool(_) | Value::Int(_) | Value::Model(_) | Value::Interval(..)
            )
        };
        if is_dumped && bound.iter().any(|(_, value)| is_shareable(value)) {
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
}

// The parameters of the operator TLC splits an action from (`Action.getParameters`), with the
// values the action's scope binds them to.
pub(crate) fn action_parameters<'ir>(
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
