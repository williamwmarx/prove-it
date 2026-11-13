//! `prove-it -simulate`: TLC's random simulation (`Simulator`), which the engine runs as TLC's
//! one worker does, and its report: the banner, the initial states, a violation's trace, the
//! statistics and the progress, as TLC prints them.

use std::sync::mpsc;

use tla_engine::clock::Instant;
use tla_engine::search::{SearchOutcome, Settings, Violation, ViolationKind};
use tla_engine::simulate::{Simulated, Simulation, SimulationOutcome, simulate};
use tla_front::config::ModelConfig;
use tla_front::errors::FrontError;
use tla_front::model::StartupMessage;
use tla_values::print::{format_value, is_printable};
use tla_values::store::{KIND_FUNCTION, KIND_SET, KIND_TUPLE};
use tla_values::{Id, Store};

use crate::args::Parsed;
use crate::check::{
    ASSUMPTION_VIOLATION, DEADLOCK, Event, Relay, SAFETY_VIOLATION, SUCCESS, print_coded_failure,
    print_finished, print_small_sets, print_startup_message, print_violation, report_not_native,
};
use crate::dump_trace::TraceDumps;
use crate::failure::print_assumption_failure;
use crate::messages::{self as code, Level, Printer};
use crate::stack::alongside;
use crate::trace::{TraceChecks, format_texts, format_variables, rebuild_simulated};

const ERROR_STATE: u32 = 2120;
const MODE_SIMULATION: u32 = 2188;
const PROGRESS_SIMULATION: u32 = 2209;
const STATS_SIMULATION: u32 = 2210;

// TLC's default depth of a trace (`TLC.traceDepth`), and the depth `-depth -1` stands for.
const DEFAULT_DEPTH: i32 = 100;

/// The simulation the command line asks for, if it asks for one: TLC simulates a spec with
/// `-simulate`, and otherwise ignores `-depth` and `-aril`.
pub fn get_simulation(args: &Parsed) -> Option<Simulation> {
    let traces = args.get("-simulate")?.first();
    let seed = args
        .first("-seed")
        .and_then(|seed| seed.parse::<i64>().ok());
    let depth = args
        .first("-depth")
        .and_then(|depth| depth.parse::<i32>().ok())
        .unwrap_or(DEFAULT_DEPTH);
    // TLC skips -aril draws only of a generator it seeds with -seed (`RandomGenerator.setSeed`).
    let aril = args
        .first("-aril")
        .and_then(|aril| aril.parse::<i64>().ok())
        .filter(|_| seed.is_some())
        .unwrap_or(0)
        .max(0);
    Some(Simulation {
        // TLC generates one trace for a number below one.
        traces: traces
            .and_then(|traces| traces.parse::<i64>().ok())
            .map(|traces| traces.max(0) as u64),
        depth: if depth == -1 { i32::MAX } else { depth },
        seed: seed.unwrap_or(0),
        aril,
    })
}

/// TLC.printStartupBanner of a simulation, with what runs Prove It in place of the JVM.
pub fn print_banner(printer: &mut Printer, seed: i64, workers: usize) {
    let machine = printer.host.machine();
    let (system, release, arch) = (&machine.system, &machine.release, &machine.arch);
    printer.print(
        MODE_SIMULATION,
        Level::None,
        &format!(
            "Running Random Simulation with seed {seed} with {workers} worker{} on {} cores with {}MB heap and 0MB offheap memory [pid: {}] ({system} {release} {arch}, prove-it native {}bit).",
            if workers == 1 { "" } else { "s" },
            machine.cores,
            machine.memory_megabytes,
            machine.pid,
            usize::BITS,
        ),
    );
}

/// What the simulation of a model needs besides the IR.
pub struct Simulating<'s> {
    pub simulation: Simulation,
    pub config: &'s ModelConfig,
    /// What -dumpTrace writes, a postcondition TLC's simulator checks too.
    pub dumps: &'s TraceDumps,
    pub startup_messages: Vec<StartupMessage>,
    /// How TLC labels an initial state of a trace, where the front end knows.
    pub initial_label: Option<String>,
    pub workers: usize,
    /// Whether `-continue` asks TLC's simulator to go on past a violation.
    pub is_continued: bool,
    pub start: Instant,
}

/// Simulates the model as TLC does and reports it, returning TLC's exit code.
pub fn check_simulation(printer: &mut Printer, ir: &tla_ir::Ir, simulating: Simulating) -> i32 {
    let model = &ir.model;
    let why = if simulating.workers > 1 {
        Some("a simulation on several workers")
    } else if !model.live_formula.is_empty() {
        Some("a simulation that checks temporal properties")
    } else if !model.postconditions.is_empty() {
        Some("a simulation with a POSTCONDITION")
    } else if simulating.dumps.has_command_line_dumps() {
        Some("a simulation with -dumpTrace, whose postcondition TLC's simulator checks")
    } else if !model.possible.is_empty() {
        Some("a simulation with a _POSSIBLE predicate")
    } else if model.startup.symmetry.is_some() {
        Some("a simulation under SYMMETRY")
    } else if simulating.config.periodic.is_some() {
        Some("_PERIODIC, which TLC evaluates as it prints its progress")
    } else if model.next.is_none() {
        Some("a simulation without a next-state relation")
    } else {
        None
    };
    if let Some(why) = why {
        return report_not_native(printer, why);
    }
    let Simulating {
        simulation,
        config,
        dumps,
        startup_messages,
        initial_label,
        workers,
        is_continued,
        start,
    } = simulating;
    let settings = Settings {
        is_violation_reported: true,
        workers,
        ..Settings::default()
    };
    // The trace evaluator reads TLCGet as the model checker does.
    let is_reading = ir
        .builtins
        .iter()
        .any(|builtin| &*ir.texts[builtin.name as usize] == "TLCGet");
    let (sender, receiver) = mpsc::channel();
    let is_tool = printer.is_tool;
    let is_plain = printer.host.is_plain();
    let mut is_misprinted = false;
    let (outcome, assumed_printed) = alongside(
        move || {
            let mut relay = Relay::new(sender, ir, is_tool, is_plain, workers, startup_messages);
            relay.undelegated =
                is_reading.then_some("an assumption of a simulation that reads TLCGet");
            let outcome = simulate(ir, &settings, &simulation, &mut relay);
            (outcome, relay.assumed_printed)
        },
        || {
            for event in receiver.iter() {
                match event {
                    Event::InitialStatesProgress(count) => printer.print(
                        code::COMPUTING_INIT_PROGRESS,
                        Level::None,
                        &format!("Computed {count} initial states..."),
                    ),
                    // TLC words the count of a simulation's initial states with no plural.
                    Event::InitialStates(_, kept) => {
                        let date = printer.date();
                        printer.print(
                            code::INIT_GENERATED_1,
                            Level::None,
                            &format!(
                                "Finished computing initial states: {kept} distinct state generated at {date}."
                            ),
                        );
                    }
                    Event::SimulationProgress(generated, traces, lengths) => {
                        print_progress(printer, generated, traces, lengths);
                        printer.flush();
                    }
                    Event::Print(Some(text)) => printer.line(&text),
                    Event::StartupMessage(message) => print_startup_message(printer, &message),
                    Event::SymmetrySetsTooSmall(names) => print_small_sets(printer, &names),
                    Event::Print(None) => {
                        is_misprinted = true;
                        break;
                    }
                    _ => {}
                }
            }
            drop(receiver);
        },
    );
    if is_misprinted {
        return report_not_native(
            printer,
            "printing a value whose text depends on how TLC built it",
        );
    }
    let started = match outcome {
        SimulationOutcome::Simulated(simulated) => Ok(simulated),
        SimulationOutcome::Declined(reason) => {
            return report_not_native(printer, &format!("the engine declined: {reason}"));
        }
        SimulationOutcome::Started(started) => Err(*started),
    };
    let simulated = match started {
        Ok(simulated) => simulated,
        Err(SearchOutcome::Declined(reason)) => {
            return report_not_native(printer, &format!("the engine declined: {reason}"));
        }
        Err(SearchOutcome::AssumptionFailed { .. }) if is_reading => {
            return report_not_native(printer, "an assumption of a simulation that reads TLCGet");
        }
        Err(SearchOutcome::AssumptionFailed {
            position,
            failed_startup,
        }) => {
            return print_assumption_failure(
                printer,
                ir,
                position,
                &failed_startup,
                &assumed_printed,
                workers,
                start,
            )
            .unwrap_or_else(|why| {
                report_not_native(
                    printer,
                    &format!("an assumption that fails to evaluate: {why}"),
                )
            });
        }
        Err(SearchOutcome::ConfigError { message }) => {
            return match FrontError::Config(message).get_coded(printer.is_tool) {
                Some(coded) => print_coded_failure(printer, &coded, start),
                None => report_not_native(printer, "a configuration error without TLC's code"),
            };
        }
        Err(SearchOutcome::AssumptionViolated { name }) => {
            printer.print(
                code::ASSUMPTION_FALSE,
                Level::Error,
                &format!("Assumption {name} is false."),
            );
            print_finished(printer, start);
            return ASSUMPTION_VIOLATION;
        }
        Err(_) => {
            return report_not_native(printer, "the engine stopped as TLC started");
        }
    };
    let Some(violation) = &simulated.violation else {
        print_progress(
            printer,
            simulated.generated,
            simulated.traces,
            simulated.lengths,
        );
        print_summary(printer, &simulated, &simulation);
        print_finished(printer, start);
        return SUCCESS;
    };
    // The simulator checks the trace exploration spec's postcondition on the violation's trace,
    // which writes the trace's file.
    if dumps.is_trace_recorded() {
        return report_not_native(
            printer,
            "the trace file of a simulation's violation, which the trace exploration spec's postcondition writes",
        );
    }
    // TLC's simulator reports the violation and goes on generating traces (`Simulator`'s
    // `TLCGlobals.continuation`).
    if is_continued {
        return report_not_native(printer, "a simulation's violation under -continue");
    }
    // TLC checks the initial states before it simulates, and reports one that violates an
    // invariant as the model checker does.
    if let ViolationKind::InitialInvariant(_) = violation.kind {
        return print_violation(
            printer,
            ir,
            config,
            violation,
            None,
            TraceChecks { dumps, run: None },
            start,
        )
        .unwrap_or_else(|why| {
            report_not_native(printer, &format!("an initial state's violation: {why}"))
        });
    }
    // TLC's worker goes on generating traces as the main thread prints the violation, and is
    // stopped at no particular one: the counts race, but for a violation in the last trace.
    if simulation
        .traces
        .is_none_or(|traces| simulated.traces < traces.max(1))
    {
        return report_not_native(
            printer,
            "a simulation's violation before its last trace, whose counts race TLC's worker",
        );
    }
    let (headline_code, headline, exit_code) = match &violation.kind {
        ViolationKind::Invariant(owner) => {
            let name = match owner.checked_sub(model.invariants.len()) {
                None => model.invariants[*owner].root.name,
                Some(property) => match model.property_invariant_names.get(property) {
                    Some(&name) => name,
                    None => return report_not_native(printer, "a name the IR doesn't carry"),
                },
            };
            (
                code::INVARIANT_VIOLATED_BEHAVIOR,
                format!("Invariant {} is violated.", ir.texts[name as usize]),
                SAFETY_VIOLATION,
            )
        }
        ViolationKind::Deadlock { .. } => (
            code::DEADLOCK_REACHED,
            "Deadlock reached.".to_string(),
            DEADLOCK,
        ),
        _ => return report_not_native(printer, "a simulation's violation of another kind"),
    };
    let texts = match get_state_texts(ir, config, dumps, violation, printer.is_tool) {
        Ok(texts) => texts,
        Err(why) => return report_not_native(printer, &format!("a simulation's trace: {why}")),
    };
    // TLC prints the behavior unless the depth is unbounded, and then the error state alone,
    // as it is, without an ALIAS.
    let is_unbounded = simulation.depth == i32::MAX;
    if is_unbounded && config.alias.is_some() {
        return report_not_native(printer, "a simulation's error state under an ALIAS");
    }
    let mut labels = Vec::with_capacity(texts.len());
    if !is_unbounded {
        let Some(initial_label) = initial_label else {
            return report_not_native(printer, "the label of an initial predicate");
        };
        labels.push(initial_label.as_str().to_string());
        for label in &violation.labels {
            let action = label.and_then(|action| model.actions.get(action as usize));
            let Some(action) = action else {
                return report_not_native(printer, "a step whose action the trace lacks");
            };
            labels.push(ir.texts[action.label as usize].to_string());
        }
    }
    printer.print(headline_code, Level::Error, &headline);
    if is_unbounded {
        printer.print(ERROR_STATE, Level::None, "The error state is:\n");
        let text = texts.last().map_or("", String::as_str);
        printer.print(code::STATE_PRINT_1, Level::State, &format!(":\n{text}"));
    } else {
        printer.print(
            code::BEHAVIOR_UP_TO_THIS_POINT,
            Level::Error,
            "The behavior up to this point is:",
        );
        for (position, (text, label)) in texts.iter().zip(&labels).enumerate() {
            printer.print(
                code::STATE_PRINT_2,
                Level::State,
                &format!("{}: <{label}>\n{text}", position + 1),
            );
        }
    }
    print_summary(printer, &simulated, &simulation);
    print_progress(
        printer,
        simulated.generated,
        simulated.traces,
        simulated.lengths,
    );
    print_finished(printer, start);
    exit_code
}

// Each state of the trace as TLC prints it: as the store holds it where its text can't depend on
// how TLC built it, and otherwise as the trace evaluator rebuilds it.
fn get_state_texts(
    ir: &tla_ir::Ir,
    config: &ModelConfig,
    dumps: &TraceDumps,
    violation: &Violation,
    is_tool: bool,
) -> Result<Vec<String>, String> {
    let store = &violation.store;
    let is_held = config.alias.is_none()
        && !violation.holds_collapsed
        && violation
            .states
            .iter()
            .flatten()
            .all(|&value| is_printable(store, value));
    if is_held {
        return violation
            .states
            .iter()
            .map(|state| {
                let texts = state
                    .iter()
                    .map(|&value| format_value(store, value))
                    .collect::<Result<Vec<String>, _>>()
                    .map_err(|bail| bail.0.to_string())?;
                Ok(format_texts(ir, &texts))
            })
            .collect();
    }
    // The trace evaluator sorts a record's fields as TLC's fingerprints do, where TLC's
    // simulation fingerprints no state and sorts a record only where it happens to compare it.
    if violation
        .states
        .iter()
        .flatten()
        .any(|&value| holds_record(store, value))
    {
        return Err("a record of several fields, which TLC may or may not have sorted".into());
    }
    let trace = rebuild_simulated(
        ir,
        violation,
        TraceChecks { dumps, run: None },
        is_tool,
        false,
    )?;
    Ok(trace
        .states
        .iter()
        .map(|state| format_variables(&state.variables))
        .collect())
}

// Whether a value holds a record of more than one field, whose fields TLC prints in the order
// it holds them.
fn holds_record(store: &Store, value: Id) -> bool {
    let size = store.size_of(value);
    match store.kind_of(value) {
        KIND_SET => (0..size).any(|index| holds_record(store, store.element_at(value, index))),
        KIND_TUPLE => {
            (0..size).any(|index| holds_record(store, store.get_range_value(value, index)))
        }
        KIND_FUNCTION => {
            (size > 1 && store.is_record(value))
                || (0..size).any(|index| {
                    store
                        .peek_key(value, index)
                        .is_some_and(|key| holds_record(store, key))
                        || holds_record(store, store.get_range_value(value, index))
                })
        }
        _ => false,
    }
}

/// `Simulator.printSummary`: with -tool the progress, then the states generated and the seed.
fn print_summary(printer: &mut Printer, simulated: &Simulated, simulation: &Simulation) {
    if printer.is_tool {
        print_progress(
            printer,
            simulated.generated,
            simulated.traces,
            simulated.lengths,
        );
    }
    printer.print(
        STATS_SIMULATION,
        Level::None,
        &format!(
            "The number of states generated: {}\nSimulation using seed {} and aril {}",
            simulated.generated, simulation.seed, simulation.aril
        ),
    );
}

/// TLC's report of a simulation's progress (`ProgressReport`): the states checked, the traces
/// generated and the mean, variance and deviation of their lengths, or with -tool the counts as
/// the model checker's progress words them.
fn print_progress(printer: &mut Printer, generated: u64, traces: u64, lengths: i64) {
    let text = if printer.is_tool {
        format!(
            "Progress({traces}) at {}: {generated} states generated, -1 distinct states found, -1 states left on queue.",
            printer.date()
        )
    } else {
        let mean = lengths as u64 & 0xFFFF_FFFF;
        let variance = ((lengths as u64) >> 32) as f64 / (traces as f64 + 1.0);
        let round = |value: f64| (value + 0.5).floor() as i64;
        format!(
            "Progress: {generated} states checked, {traces} traces generated (trace length: mean={mean}, var(x)={}, sd={})",
            round(variance),
            round(variance.sqrt())
        )
    };
    printer.print(PROGRESS_SIMULATION, Level::None, &text);
}

#[cfg(test)]
mod tests {
    use tla_engine::simulate::add_length;

    #[test]
    fn keeps_the_lengths_as_tlc_packs_them() {
        // Lengths 4, 5 and 3: TLC's integer Welford mean 4 and squared deviations 2.
        let lengths = [4, 5, 3]
            .iter()
            .enumerate()
            .fold(0, |lengths, (index, &length)| {
                add_length(lengths, length, index as u64 + 1)
            });
        assert_eq!((lengths & 0xFFFF_FFFF, lengths >> 32), (4, 2));
    }
}
