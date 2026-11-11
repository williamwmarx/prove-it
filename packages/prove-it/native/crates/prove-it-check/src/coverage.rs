//! TLC's coverage report (`-coverage`): what `tla-trace`'s coverage pass counts once the search is
//! over, printed where TLC's `printSummary` prints it, before the statistics.

use std::collections::HashMap;
use std::path::Path;

use tla_engine::search::{SearchOutcome, ViolationKind};
use tla_ir::Ir;
use tla_trace::{CoverageMessage, Rebuilder};

use crate::host::Host;
use crate::messages::{Level, Printer};
use crate::stack::on_search_stack;

/// TLC's report of a run, none where TLC prints none, or why the binary can't print it.
pub(crate) fn compute(
    ir: &Ir,
    outcome: &SearchOutcome,
    host: &dyn Host,
    directories: &[&Path],
    polynomial: usize,
) -> Result<Vec<CoverageMessage>, String> {
    let counts = match outcome {
        SearchOutcome::Complete { counts, .. } => (counts.generated, counts.distinct),
        SearchOutcome::Stopped {
            violation: Some(violation),
            ..
        } if matches!(
            violation.kind,
            ViolationKind::Invariant(_)
                | ViolationKind::InitialInvariant(_)
                | ViolationKind::Deadlock { accepted: None }
        ) =>
        {
            (violation.counts.generated, violation.counts.distinct)
        }
        _ => return Err("coverage of a run that ends other than at a violation or its end".into()),
    };
    // The sources of the modules the IR places nodes in, which place the nodes SANY makes.
    let mut sources = HashMap::new();
    for node in &ir.nodes.arena {
        if let Some(range) = node.range {
            let name = &ir.texts[range.module as usize];
            if !sources.contains_key(&**name)
                && let Some(text) = host.load_module(directories, name)
            {
                sources.insert(name.to_string(), text);
            }
        }
    }
    let report = on_search_stack(|| {
        Rebuilder::new(ir).and_then(|mut rebuilder| {
            rebuilder.coverage(&|name| sources.get(name).cloned(), polynomial)
        })
    })
    .map_err(|unsupported| format!("coverage: {}", unsupported.0))?;
    if !report.messages.is_empty() && (report.generated, report.distinct) != counts {
        return Err(format!(
            "coverage: TLC's search counted {} states generated and {} distinct where the engine counted {} and {}",
            report.generated, report.distinct, counts.0, counts.1
        ));
    }
    Ok(report.messages)
}

/// The report as TLC prints it, between its 2201 and 2202 messages.
pub(crate) fn print(printer: &mut Printer, messages: &[CoverageMessage]) {
    if messages.is_empty() {
        return;
    }
    let date = printer.date();
    printer.print(
        2201,
        Level::None,
        &format!(
            "The coverage statistics at {date} (see https://explain.tlapl.us/module-coverage-statistics for how to interpret the following statistics)."
        ),
    );
    for message in messages {
        printer.print(message.code, Level::None, &message.text);
    }
    printer.print(2202, Level::None, "End of statistics.");
}
