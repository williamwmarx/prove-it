//! TLC's `_PERIODIC` expression (`ModelChecker.doPeriodicWork`): the definition's body, evaluated
//! afresh with no state on TLC's main thread 3 s after its workers start and before each progress
//! report after (`AbstractChecker.runTLC`), at a time of TLC's own; FALSE stops the search.

use crate::Unsupported;
use crate::eval::Context;
use crate::rebuild::{Rebuilder, run};
use crate::value::Value;
use tla_ir::DefinitionForm;

impl Rebuilder<'_> {
    /// Whether the `_PERIODIC` expression can't change what TLC prints, whenever TLC evaluates it:
    /// evaluated with TLC's empty state of the initial level and none of the run's counts, it is
    /// TRUE and prints nothing. An expression that reads anything of the run, a count, a register
    /// or the state, fails to evaluate here. `Unsupported` where it fails, isn't a boolean, or
    /// reads or sets a register.
    pub fn is_periodic_inert(&mut self) -> Result<bool, Unsupported> {
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
        evaluator.runtime = None;
        let (reads, writes) = (evaluator.register_reads, evaluator.register_writes);
        let defined = evaluator.definition(ir.definitions[definition as usize]);
        // TLC compares the function a function definition is with FALSE, and fails.
        if matches!(defined.form, DefinitionForm::Function(_)) {
            return Err(Unsupported(
                "a _PERIODIC naming a function definition".into(),
            ));
        }
        let body = defined.body;
        let result = evaluator.evaluate(body, &Context::default());
        let printed = std::mem::take(&mut evaluator.printed);
        if evaluator.register_writes != writes {
            return Err(Unsupported("a _PERIODIC that sets a register".into()));
        }
        if evaluator.register_reads != reads {
            return Err(Unsupported("a _PERIODIC that reads a register".into()));
        }
        match result {
            Ok(Value::Bool(holds)) => Ok(holds && printed.is_empty()),
            // TLC fails comparing another value with FALSE (`BoolValue.equals`).
            Ok(_) => Err(Unsupported("a _PERIODIC that isn't a boolean".into())),
            Err(error) => Err(Unsupported(format!(
                "a _PERIODIC that reads the run or fails to evaluate: {}",
                error.reason
            ))),
        }
    }
}
