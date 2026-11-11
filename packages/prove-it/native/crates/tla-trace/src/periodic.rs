//! TLC's `_PERIODIC` expression (`ModelChecker.doPeriodicWork`): the definition's body, evaluated
//! afresh with no state on TLC's main thread each time it is about to print its progress, which
//! stops the search where it is FALSE.

use crate::Unsupported;
use crate::eval::{Context, Runtime};
use crate::postcondition::{Stats, stats_record};
use crate::rebuild::{Rebuilder, run};
use crate::value::Value;
use tla_ir::DefinitionForm;

/// What TLC found of the `_PERIODIC` expression, and what it printed as TLC evaluated it.
#[derive(Debug, PartialEq, Eq)]
pub struct Periodic {
    /// Whether it is TRUE: FALSE stops the search.
    pub holds: bool,
    pub printed: Vec<Vec<String>>,
}

impl Rebuilder<'_> {
    /// Evaluates the model's `_PERIODIC` expression as TLC does once the search counts `stats`,
    /// after the startup's definitions, which keep the values TLC computed for them.
    /// `Unsupported` where it fails to evaluate or isn't a boolean, which TLC reports as a failure
    /// of the run, where it sets a register, which TLC's main thread sets for every worker, and
    /// where it reads what the evaluator doesn't hold then: TLC's registers, CounterExample and
    /// TLCGet("duration").
    pub fn periodic(&mut self, stats: &Stats) -> Result<Periodic, Unsupported> {
        let evaluator = self.evaluator();
        let ir = evaluator.ir;
        let Some(definition) = ir.model.periodic.as_ref().and_then(|name| name.definition) else {
            return Err(Unsupported("a _PERIODIC the IR doesn't define".into()));
        };
        // The definitions the configuration names TLC evaluated as it read the configuration,
        // which the evaluator would evaluate again.
        if !ir.model.startup.predicates.is_empty() {
            return Err(Unsupported(
                "a _PERIODIC after the configuration's predicates".into(),
            ));
        }
        let width = ir.variables.len();
        evaluator.current = vec![None; width];
        evaluator.next = vec![None; width];
        // TLC evaluates it with its empty state, of the initial level.
        evaluator.level = 1;
        run(evaluator.compute_startup())?;
        evaluator.printed.clear();
        let stats = stats_record(evaluator, stats)?;
        evaluator.runtime = Some(Runtime {
            named: None,
            stats,
            counter_example: None,
            possible_counts: None,
        });
        let writes = evaluator.register_writes;
        let defined = evaluator.definition(ir.definitions[definition as usize]);
        // TLC compares the function a function definition is with FALSE, and fails.
        if matches!(defined.form, DefinitionForm::Function(_)) {
            return Err(Unsupported(
                "a _PERIODIC naming a function definition".into(),
            ));
        }
        let body = defined.body;
        let result = evaluator.evaluate(body, &Context::default());
        evaluator.runtime = None;
        let printed = std::mem::take(&mut evaluator.printed);
        if evaluator.register_writes != writes {
            return Err(Unsupported("a _PERIODIC that sets a register".into()));
        }
        match result {
            Ok(Value::Bool(holds)) => Ok(Periodic { holds, printed }),
            // TLC fails comparing another value with FALSE (`BoolValue.equals`).
            Ok(_) => Err(Unsupported("a _PERIODIC that isn't a boolean".into())),
            Err(error) => Err(Unsupported(format!(
                "a _PERIODIC that fails to evaluate: {}",
                error.reason
            ))),
        }
    }
}
