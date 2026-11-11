//! TLC's coverage report (`-coverage`): what `tla-trace`'s coverage pass counts once the search is
//! over, printed where TLC's `printSummary` prints it, before the statistics.

use std::collections::HashMap;
use std::path::Path;
use std::time::Duration;

use tla_engine::search::{SearchOutcome, ViolationKind};
use tla_ir::Ir;
use tla_trace::{CoverageMessage, Rebuilder};

use crate::args::Parsed;
use crate::host::Host;
use crate::messages::{Level, Printer};
use crate::stack::on_search_stack;

/// The longest native run whose report is native: the binary with coverage took at least 3.45
/// times as long as TLC on the perf suite, so TLC's run took well under the 5 minutes past which
/// it ends its report with 2777 (design/cli.md, "-coverage").
pub(crate) const CUT: Duration = Duration::from_secs(60);

/// With -coverage, how many progress reports TLC prints before the one it follows with a
/// coverage report: `coverageInterval / progressInterval`, -coverage's minutes as milliseconds in
/// a Java int over the 60 s between progress reports.
pub(crate) fn get_countdown(args: &Parsed) -> Option<i32> {
    let minutes: i32 = args.first("-coverage")?.parse().ok()?;
    Some(minutes.wrapping_mul(60 * 1000) / (60 * 1000))
}

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
                | ViolationKind::Deadlock {
                    accepted: None,
                    atom: None
                }
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

#[cfg(test)]
mod tests {
    use super::*;

    fn get_countdown_of(minutes: &str) -> Option<i32> {
        let args = [minutes, "Spec"].map(String::from);
        get_countdown(
            &Parsed::parse(&[&["-coverage".to_string()][..], &args].concat(), true)
                .expect("options"),
        )
    }

    #[test]
    fn counts_down_the_progress_reports_before_tlc_reports_coverage() {
        // At the first progress report for -coverage 0, the (N + 1)-th for -coverage N.
        assert_eq!(get_countdown_of("0"), Some(0));
        assert_eq!(get_countdown_of("1"), Some(1));
        assert_eq!(get_countdown_of("+3"), Some(3));
        // 71583 minutes are 4294980000 ms, which a Java int holds as 12704.
        assert_eq!(get_countdown_of("71583"), Some(0));
        let args = Parsed::parse(&["Spec".to_string()], true).expect("options");
        assert_eq!(get_countdown(&args), None);
    }
}
