//! `prove-it -simulate`: TLC's random simulation (`Simulator`), which the engine runs as TLC's
//! one worker does, and its report: the banner, the initial states, a violation's trace, the
//! statistics and the progress, as TLC prints them.

use std::sync::mpsc;

use tla_engine::clock::Instant;
use tla_engine::search::{ErrorSite, SearchOutcome, Settings, Violation, ViolationKind};
use tla_engine::simulate::{Simulated, Simulation, SimulationOutcome, simulate};
use tla_front::config::ModelConfig;
use tla_front::errors::FrontError;
use tla_front::model::StartupMessage;
use tla_trace::{CounterExample, Ending, Rebuilder, Site, Stats, Unsupported};
use tla_values::print::{format_value, is_printable};
use tla_values::store::{KIND_FUNCTION, KIND_SET, KIND_TUPLE};
use tla_values::{Id, Store};

use crate::args::Parsed;
use crate::check::{
    ASSUMPTION_VIOLATION, DEADLOCK, Event, Relay, SAFETY_VIOLATION, SUCCESS, print_coded_failure,
    print_finished, print_postcondition_failure, print_small_sets, print_startup_message,
    print_violation, report_not_native,
};
use crate::dump_trace::TraceDumps;
use crate::failure::print_assumption_failure;
use crate::messages::{self as code, Level, Printer};
use crate::stack::{alongside, on_search_stack};
use crate::trace::{
    PostconditionRun, Postconditions, TraceChecks, check, format_texts, format_variables,
    rebuild_simulated,
};

const ERROR_STATE: u32 = 2120;
const MODE_SIMULATION: u32 = 2188;
const PROGRESS_SIMULATION: u32 = 2209;
const STATS_SIMULATION: u32 = 2210;
/// `EC.TLC_INITIAL_STATE`: an error and the initial state TLC was working on.
const INITIAL_STATE: u32 = 2102;
/// `EC.TLC_ACTION_PROPERTY_VIOLATED_BEHAVIOR`.
const ACTION_PROPERTY_VIOLATED: u32 = 2112;

// The statuses TLC exits with after an error it didn't expect, a failure to evaluate an
// invariant, and an action property's violation or failure (`EC.ExitStatus`).
const ERROR: i32 = 255;
const FAILURE_SAFETY_EVAL: i32 = 76;
const VIOLATION_LIVENESS: i32 = 13;

// TLC's default depth of a trace (`TLC.traceDepth`), and the depth `-depth -1` stands for.
const DEFAULT_DEPTH: i32 = 100;

/// The simulation the command line asks for, if it asks for one: TLC simulates a spec with
/// `-simulate`, and otherwise ignores `-depth` and `-aril`.
pub fn get_simulation(args: &Parsed) -> Option<Simulation> {
    // Each `num=` sets the number of traces, which a later -simulate without one keeps.
    args.get("-simulate")?;
    let traces = args
        .options
        .iter()
        .rev()
        .filter(|(option, _)| option == "-simulate")
        .find_map(|(_, values)| values.first());
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
        is_generated: args.has("-generate"),
        initial_action: None,
    })
}

/// The initial predicate's name and place the front end found, as texts of the IR, which TLC's
/// simulator records as an initial state's action.
pub fn get_initial_action(
    ir: &tla_ir::Ir,
    initial_action: Option<&(String, String, [i32; 4])>,
) -> Option<(tla_ir::TextId, tla_ir::SourceRange)> {
    let (name, module, [start_line, start_column, end_line, end_column]) = initial_action?;
    let find = |text: &str| {
        ir.texts
            .iter()
            .position(|known| **known == *text)
            .map(|position| position as tla_ir::TextId)
    };
    Some((
        find(name)?,
        tla_ir::SourceRange {
            module: find(module)?,
            start_line: *start_line,
            start_column: *start_column,
            end_line: *end_line,
            end_column: *end_column,
        },
    ))
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
    } else if !model.live_formula.is_empty()
        && (!model.postconditions.is_empty() || is_effectful(ir) || model.view.is_some())
    {
        // TLC's behavior graph of a simulated behavior keys its nodes by the states'
        // fingerprints, which a VIEW makes.
        Some(
            "a simulation that checks temporal properties with a POSTCONDITION, a VIEW, registers or random draws",
        )
    } else if !model.postconditions.is_empty()
        && (simulating.config.alias.is_some()
            || is_effectful(ir)
            || simulating.simulation.depth == i32::MAX)
    {
        Some(
            "a simulation with a POSTCONDITION, an ALIAS, registers, random draws or an unbounded depth",
        )
    } else if simulating.dumps.has_command_line_dumps() {
        Some("a simulation with -dumpTrace, whose postcondition TLC's simulator checks")
    } else if !model.possible.is_empty() {
        Some("a simulation with a _POSSIBLE predicate")
    } else if simulating.config.alias.is_some() && !is_trace_read_past_actions(ir) {
        // The simulator's Trace gives each state's record its action's too (`TLCExt.getTrace`'s
        // `RecordValue(state, state.getAction())`), which an ALIAS may print.
        Some("a simulation whose ALIAS may read TLCExt's Trace")
    } else if ir
        .builtins
        .iter()
        .any(|builtin| &*ir.texts[builtin.name as usize] == "_Track")
    {
        // `_Counts` merges the registers of the simulator's workers (`Simulator.getAllNamedValues`).
        Some("a simulation that applies _Track")
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
    let mut is_unnamed = false;
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
                    Event::Print(Some(text)) => printer.user_print(&text),
                    Event::StartupMessage(message) => print_startup_message(printer, &message),
                    Event::SymmetrySetsTooSmall(names) => {
                        if !print_small_sets(printer, &names) {
                            is_unnamed = true;
                            break;
                        }
                    }
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
    if is_unnamed {
        return report_not_native(printer, crate::check::SMALL_SET_UNNAMED);
    }
    let started = match outcome {
        SimulationOutcome::Simulated(simulated) => Ok(simulated),
        SimulationOutcome::Declined(reason) => {
            return report_not_native(printer, &format!("the engine declined: {reason}"));
        }
        SimulationOutcome::Started(started) => Err(*started),
        SimulationOutcome::Unsatisfied { generated } => {
            let (code, constrained) = if generated == 0 {
                (code::NO_STATES_SATISFYING_INIT, "")
            } else {
                (
                    code::NO_STATES_SATISFYING_INIT_AND_CONSTRAINT,
                    " and the state-constraint(s)",
                )
            };
            printer.print(
                code,
                Level::Error,
                &format!("There is no state satisfying the initial state predicate{constrained}."),
            );
            print_finished(printer, start);
            return ERROR;
        }
        SimulationOutcome::InitialIncomplete {
            state,
            holds_collapsed,
            store,
        } => {
            // TLC's trace exploration spec reads the error's state, which it hasn't fully.
            if holds_collapsed || printer.trace_spec.is_some() || printer.is_trace_recorded {
                return report_not_native(
                    printer,
                    "a simulation's incomplete initial state with unrenderable values or trace files",
                );
            }
            let values = state
                .iter()
                .map(|&id| {
                    if id == tla_engine::UNASSIGNED {
                        Ok(None)
                    } else {
                        tla_trace::from_store(&store, id).map(Some)
                    }
                })
                .collect::<Result<Vec<_>, _>>();
            let Ok(values) = values else {
                return report_not_native(
                    printer,
                    "a simulation's incomplete initial state has an unrenderable value",
                );
            };
            let refs: Vec<_> = values.iter().map(Option::as_ref).collect();
            let variables = crate::trace::get_partial_variables(ir, &refs, printer.host.is_plain());
            // `Simulator.simulate` returns the error as it prints it, without the summary.
            printer.outcome.status = Some("error");
            printer.report(
                code::INCOMPLETE_INITIAL,
                &format!(
                    "State is not completely specified by the initial predicate:\n{}",
                    crate::trace::format_variables(&variables)
                ),
            );
            print_finished(printer, start);
            return ERROR;
        }
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
        Err(SearchOutcome::ConfigError { .. }) if !model.postconditions.is_empty() => {
            return report_not_native(
                printer,
                "a configuration error of a simulation with a POSTCONDITION, which TLC may report after it simulates",
            );
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
        // `Simulator.simulate` checks the postconditions once its workers are done, then reports
        // its progress, and the summary only where no error was found.
        let reported = match print_postconditions(printer, ir, None) {
            Ok(reported) => reported,
            Err(why) => {
                return report_not_native(printer, &format!("a simulation's POSTCONDITION: {why}"));
            }
        };
        let status = reported.status;
        if reported.is_rejected {
            print_finished(printer, start);
            return status;
        }
        print_progress(
            printer,
            simulated.generated,
            simulated.traces,
            simulated.lengths,
        );
        if status == SUCCESS {
            print_summary(printer, &simulated, &simulation);
        }
        print_finished(printer, start);
        return status;
    };
    if let ViolationKind::Error { site } = violation.kind {
        if !model.postconditions.is_empty() {
            return report_not_native(
                printer,
                "a failure in a simulation with a POSTCONDITION, which TLC checks of its trace",
            );
        }
        let failing = Failing {
            ir,
            config,
            dumps,
            simulated: &simulated,
            simulation: &simulation,
            initial_label: initial_label.as_deref(),
        };
        if simulated.is_incomplete {
            return print_simulated_incomplete(printer, &failing, violation, start).unwrap_or_else(
                |why| {
                    report_not_native(
                        printer,
                        &format!("an incomplete successor in a simulation: {why}"),
                    )
                },
            );
        }
        return print_simulated_failure(printer, &failing, violation, site, start).unwrap_or_else(
            |why| {
                report_not_native(
                    printer,
                    &format!("a failure evaluating the model in a simulation: {why}"),
                )
            },
        );
    }
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
        // The postconditions TLC checks of the state are checked first, as the report isn't
        // undone.
        let checked = match check_postconditions_of(ir, Some((violation, Ending::Violation))) {
            Ok(checked) => checked,
            Err(why) => {
                return report_not_native(printer, &format!("a simulation's POSTCONDITION: {why}"));
            }
        };
        // TLC rejects the postcondition within its check of the initial states, which reports
        // the rejection as a failure on the state.
        if matches!(checked, Some(Checking::Rejected(_))) {
            return report_not_native(
                printer,
                "a constant POSTCONDITION after an initial state's violation",
            );
        }
        let status = match (&checked, &violation.kind) {
            // `Simulator.simulate` prints the state as it holds it, which the postconditions'
            // check found it can.
            (Some(_), ViolationKind::InitialInvariant(owner)) => {
                print_initial_violation(printer, ir, config, dumps, violation, *owner)
            }
            _ => print_violation(
                printer,
                ir,
                config,
                violation,
                None,
                TraceChecks {
                    workers: None,
                    dumps,
                    run: None,
                },
                start,
            )
            .map_err(String::from),
        };
        return match status {
            Ok(status) => match report_postconditions(printer, ir, checked.as_ref()) {
                Ok(reported) => more_severe(status, reported.status),
                Err(why) => report_not_native(printer, why),
            },
            Err(why) => report_not_native(printer, &format!("an initial state's violation: {why}")),
        };
    }
    // TLC's worker prints a counterexample to the temporal properties itself, and stops at it
    // (`LiveCheck1.printErrorTrace`, `LiveException`).
    if let ViolationKind::SimulatedLasso {
        loop_start,
        back,
        ref violated,
    } = violation.kind
    {
        let failing = Failing {
            ir,
            config,
            dumps,
            simulated: &simulated,
            simulation: &simulation,
            initial_label: initial_label.as_deref(),
        };
        return print_simulated_lasso(printer, &failing, violation, (loop_start, back, violated))
            .inspect(|_| print_finished(printer, start))
            .unwrap_or_else(|why| {
                report_not_native(
                    printer,
                    &format!("a simulated behavior that violates the temporal properties: {why}"),
                )
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
        // `SimulationWorker.addElement`'s violation of an action property by the step.
        ViolationKind::ActionProperty(position) => {
            let Some(property) = model.action_properties.get(*position) else {
                return report_not_native(printer, "an action property the model doesn't have");
            };
            (
                ACTION_PROPERTY_VIOLATED,
                format!(
                    "Action property {} is violated.",
                    ir.texts[property.name as usize]
                ),
                VIOLATION_LIVENESS,
            )
        }
        _ => return report_not_native(printer, "a simulation's violation of another kind"),
    };
    let texts = match get_state_texts(ir, config, dumps, violation, printer.is_tool)
        .and_then(without_alias_output)
    {
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
    // TLC checks the postconditions of the violation's trace (`getCounterExample`).
    let ending = match violation.kind {
        ViolationKind::Deadlock { .. } => Ending::Kept,
        _ => Ending::Violation,
    };
    let exit_code = match print_postconditions(printer, ir, Some((violation, ending))) {
        Ok(reported) if reported.is_rejected => {
            print_finished(printer, start);
            return reported.status;
        }
        Ok(reported) => more_severe(exit_code, reported.status),
        Err(why) => {
            return report_not_native(printer, &format!("a simulation's POSTCONDITION: {why}"));
        }
    };
    print_progress(
        printer,
        simulated.generated,
        simulated.traces,
        simulated.lengths,
    );
    print_finished(printer, start);
    exit_code
}

// `LiveCheck1.printErrorTrace` of a simulated behavior: the properties the states it prints
// violate, the states, from the behavior's first, each with the action that made it, and the
// step back into the cycle by the behavior's next step, or stuttering. The simulator then prints
// its summary, and its progress once more as it ends.
fn print_simulated_lasso(
    printer: &mut Printer,
    failing: &Failing<'_>,
    violation: &Violation,
    (loop_start, back, violated): (usize, Option<u32>, &[usize]),
) -> Result<i32, String> {
    let ir = failing.ir;
    let model = &ir.model;
    // TLC checks the postconditions of the counterexample, and an ALIAS rewrites the states it
    // prints and compares.
    if !model.postconditions.is_empty() || failing.config.alias.is_some() {
        return Err("a POSTCONDITION or an ALIAS".into());
    }
    let label_of = |action: u32| -> Result<String, String> {
        let action = model
            .actions
            .get(action as usize)
            .ok_or("a step whose action the trace lacks")?;
        Ok(ir.texts[action.label as usize].to_string())
    };
    let mut labels = vec![
        failing
            .initial_label
            .ok_or("the label of an initial predicate")?
            .to_string(),
    ];
    for label in &violation.labels {
        labels.push(label_of(
            label.ok_or("a step whose action the trace lacks")?,
        )?);
    }
    // The ALIAS, which may print, declined above.
    let texts = get_state_texts(
        ir,
        failing.config,
        failing.dumps,
        violation,
        printer.is_tool,
    )
    .and_then(without_alias_output)?;
    let headline =
        crate::check::properties_headline(ir, violated).ok_or("a property the IR doesn't name")?;
    // All that may fail is found before anything is printed.
    let back = back.map(label_of).transpose()?;
    printer.outcome.status = Some("liveness-violation");
    printer.report(code::TEMPORAL_PROPERTY_VIOLATED, &headline);
    printer.print(
        code::COUNTER_EXAMPLE,
        Level::Error,
        "The following behavior constitutes a counter-example:\n",
    );
    for (position, (text, label)) in texts.iter().zip(&labels).enumerate() {
        printer.print(
            code::STATE_PRINT_2,
            Level::State,
            &format!("{}: <{label}>\n{text}", position + 1),
        );
    }
    match back {
        None => printer.print(
            code::STATE_PRINT_3,
            Level::State,
            &format!("{}: Stuttering", texts.len() + 1),
        ),
        Some(back) => {
            let label = format!(": <{back}>\n");
            if printer.is_tool {
                printer.print(
                    code::BACK_TO_STATE,
                    Level::State,
                    &format!("{}: Back to state{label}", loop_start + 1),
                );
            } else {
                printer.line(&format!("Back to state {}{label}", loop_start + 1));
            }
        }
    }
    print_summary(printer, failing.simulated, failing.simulation);
    print_progress(
        printer,
        failing.simulated.generated,
        failing.simulated.traces,
        failing.simulated.lengths,
    );
    Ok(VIOLATION_LIVENESS)
}

/// `EC.TLC_INVARIANT_VIOLATED_INITIAL` as `Simulator.simulate` reports it: the invariant and the
/// state, which it then checks the postconditions of.
fn print_initial_violation(
    printer: &mut Printer,
    ir: &tla_ir::Ir,
    config: &ModelConfig,
    dumps: &TraceDumps,
    violation: &Violation,
    owner: usize,
) -> Result<i32, String> {
    let name = invariant_name(ir, owner).ok_or("a name the IR doesn't carry")?;
    let (texts, alias_output) = get_state_texts(ir, config, dumps, violation, printer.is_tool)?;
    let state = texts
        .first()
        .ok_or("an initial state the violation lacks")?;
    // TLC evaluates the ALIAS on the state as it builds the message (`Simulator.simulate`).
    for line in alias_output.first().into_iter().flatten() {
        printer.replayed(ir, line)?;
    }
    printer.outcome.status = Some("invariant-violation");
    printer.report(
        code::INVARIANT_VIOLATED_INITIAL,
        &format!("Invariant {name} is violated by the initial state:\n{state}"),
    );
    Ok(SAFETY_VIOLATION)
}

// Whether the model sets registers or draws at random, which evaluating its model again doesn't
// follow as the simulation did.
// Whether the spec reads TLCExt's Trace nowhere but as `Len(Trace)`, `Len(Tail(Trace))`,
// `Head(Trace).v`, `Trace[1].v` or `Trace[Len(Trace)].v` of a variable v, or through
// definitions without parameters that are just Trace: none of which reads the field `_action` the simulator's Trace
// gives each state's record (`TLCExt.getTrace`), nor fails printing the records, since the trace
// holds at least the state.
fn is_trace_read_past_actions(ir: &tla_ir::Ir) -> bool {
    use tla_ir::{DefinitionForm, NodeKind, Resolution};
    let arena = &ir.nodes.arena;
    let named = |node: usize| match &arena[node].kind {
        NodeKind::Identifier(name) | NodeKind::OperatorReference(name) => Some(*name),
        NodeKind::Apply { name, args } if args.is_empty() => Some(*name),
        _ => None,
    };
    let is_builtin = |resolution: Resolution, name: &str| {
        matches!(resolution, Resolution::Builtin(index)
            if ir.builtins.get(index as usize).is_some_and(|builtin| &*ir.texts[builtin.name as usize] == name))
    };
    // A definition without parameters by its node, of a global definition.
    let definition = |index: usize| {
        let node = *ir.definitions.get(index)? as usize;
        match &arena.get(node)?.kind {
            NodeKind::Definition(definition) if matches!(&definition.form, DefinitionForm::Operator(params) if params.is_empty()) => {
                Some((node, definition.body as usize))
            }
            _ => None,
        }
    };
    // Whether a node is Trace: the builtin, a global definition without parameters that is
    // Trace, or a name bound locally that a LET defines so somewhere (`lets`).
    let is_trace_in = |node: usize, lets: &[tla_ir::TextId]| {
        let mut node = node;
        for _ in 0..64 {
            // A node met again stands where it is written for the node it names.
            if let NodeKind::Reference(again) = arena[node].kind {
                node = again as usize;
                continue;
            }
            let Some(name) = named(node) else {
                return false;
            };
            if name.is_local && lets.contains(&name.text) {
                return true;
            }
            match name.resolution {
                resolved if is_builtin(resolved, "Trace") => return true,
                Resolution::Definition(index) => match definition(index as usize) {
                    Some((_, body)) => node = body,
                    None => return false,
                },
                _ => return false,
            }
        }
        false
    };
    // The names of the LET definitions without parameters that are Trace, which stand for it
    // wherever a name bound locally is written so.
    let mut lets: Vec<tla_ir::TextId> = Vec::new();
    let let_definitions: Vec<(tla_ir::TextId, usize, usize)> = arena
        .iter()
        .flat_map(|node| match &node.kind {
            NodeKind::Let { definitions, .. } => definitions.clone(),
            _ => Vec::new(),
        })
        .filter_map(|node| match &arena.get(node as usize)?.kind {
            NodeKind::Definition(definition)
                if matches!(&definition.form, DefinitionForm::Operator(params) if params.is_empty()) =>
            {
                Some((definition.name, node as usize, definition.body as usize))
            }
            _ => None,
        })
        .collect();
    loop {
        let found: Vec<tla_ir::TextId> = let_definitions
            .iter()
            .filter(|(name, _, body)| !lets.contains(name) && is_trace_in(*body, &lets))
            .map(|(name, _, _)| *name)
            .collect();
        if found.is_empty() {
            break;
        }
        lets.extend(found);
    }
    let is_trace = |node: usize| is_trace_in(node, &lets);
    // Whether a node is `Tail(Trace)`, which the trace holding the state never fails.
    let is_tail = |node: usize| {
        matches!(&arena[node].kind, NodeKind::Apply { name, args }
            if args.len() == 1 && is_builtin(name.resolution, "Tail") && is_trace(args[0] as usize))
    };
    // `Len(Trace)` or `Len(Tail(Trace))`.
    let is_length = |node: usize| {
        matches!(&arena[node].kind, NodeKind::Apply { name, args }
            if args.len() == 1
                && is_builtin(name.resolution, "Len")
                && (is_trace(args[0] as usize) || is_tail(args[0] as usize)))
    };
    let mut parents = vec![usize::MAX; arena.len()];
    for (position, node) in arena.iter().enumerate() {
        for child in node.kind.children() {
            if let Some(parent) = parents.get_mut(child as usize) {
                *parent = position;
            }
        }
    }
    let parent = |node: usize| {
        parents
            .get(node)
            .copied()
            .filter(|&parent| parent != usize::MAX)
    };
    let is_variable_field = |access: usize, record: usize| {
        matches!(&arena[access].kind, NodeKind::FieldAccess { record: of, field }
            if *of as usize == record
                && ir.variables.iter().any(|&variable| ir.texts[variable as usize] == ir.texts[*field as usize]))
    };
    let global_bodies: Vec<usize> = (0..ir.definitions.len())
        .filter_map(|index| definition(index).map(|(node, _)| node))
        .chain(let_definitions.iter().map(|&(_, node, _)| node))
        .collect();
    (0..arena.len()).filter(|&node| is_trace(node)).all(|node| {
        let Some(above) = parent(node) else {
            return false;
        };
        // The body of a definition without parameters that is just Trace, whose uses are
        // checked themselves.
        if global_bodies.contains(&above) {
            return true;
        }
        if is_length(above) || is_tail(above) && parent(above).is_some_and(is_length) {
            return true;
        }
        let is_state = match &arena[above].kind {
            NodeKind::Apply { name, args } => {
                args.len() == 1 && is_builtin(name.resolution, "Head")
            }
            NodeKind::FunctionApplication { function, args } => {
                *function as usize == node
                    && args.len() == 1
                    && (matches!(arena[args[0] as usize].kind, NodeKind::Number(1))
                        || is_length(args[0] as usize))
            }
            _ => false,
        };
        is_state && parent(above).is_some_and(|access| is_variable_field(access, above))
    })
}

fn is_effectful(ir: &tla_ir::Ir) -> bool {
    ir.builtins.iter().any(|builtin| {
        builtin.flags & tla_ir::Builtin::EXTERNAL_CLASS != 0
            || matches!(
                &*ir.texts[builtin.name as usize],
                "TLCSet"
                    | "TLCGetAndSet"
                    | "_Track"
                    | "RandomElement"
                    | "RandomSubset"
                    | "RandomSubsetSet"
                    | "RandomSetOfSubsets"
                    | "TestRandomSetOfSubsets"
            )
    })
}

// Of two statuses TLC could exit with, the one of the more severe error (`Simulator.simulate`
// compares `EC.ExitStatus`'s): a violation's over a postcondition's.
fn more_severe(status: i32, other: i32) -> i32 {
    status.max(other)
}

/// The configuration's postconditions as TLC's simulator checks them
/// (`checkPostConditionWithCounterExample`, `checkPostCondition`), with CounterExample the trace
/// of the violation, where there is one, as the simulator holds it: what they printed and the first
/// that doesn't hold. None for a model without postconditions.
fn check_postconditions_of(
    ir: &tla_ir::Ir,
    violation: Option<(&Violation, Ending)>,
) -> Result<Option<Checking>, String> {
    if ir.model.postconditions.is_empty() {
        return Ok(None);
    }
    if let Some((violation, _)) = violation {
        let store = &violation.store;
        if store.is_empty_tuple_ambiguous()
            || violation.holds_collapsed
            || violation
                .states
                .iter()
                .flatten()
                .any(|&value| !is_printable(store, value) || holds_record(store, value))
        {
            return Err("a trace whose values TLC may hold otherwise than the engine".into());
        }
    }
    let run = PostconditionRun {
        possible: Vec::new(),
        stats: Stats {
            queue: 0,
            distinct: 0,
            initial: 0,
            generated: 0,
            diameter: 0,
            duration: 0,
        },
    };
    on_search_stack(|| {
        let mut rebuilder = Rebuilder::new(ir)?;
        // TLC holds a constant definition it computed as it started as its value, which it
        // rejects as a postcondition once it has simulated, before it checks any
        // (`Spec.getPostConditionSpecs`).
        for postcondition in &ir.model.postconditions {
            let Some(definition) = postcondition.definition else {
                return Err(Unsupported(
                    "a postcondition the model doesn't define".into(),
                ));
            };
            if rebuilder.is_computed_at_startup(definition)? {
                return Ok(Checking::Rejected(format!(
                    "The post condition {} cannot be a constant.",
                    ir.texts[postcondition.name as usize]
                )));
            }
        }
        let mut rebuilder = Rebuilder::new(ir)?;
        rebuilder.set_simulation();
        rebuilder.set_workers(1);
        let trace = match violation {
            Some((violation, ending)) => {
                let store = &violation.store;
                rebuilder.set_startup(store, &violation.startup, violation.startup_random)?;
                rebuilder.set_chosen(store, &violation.chosen);
                let states: Vec<&[Id]> = violation.states.iter().map(Vec::as_slice).collect();
                Some(rebuilder.rebuild(store, &states, &violation.labels, ending)?)
            }
            None => None,
        };
        let counter_example = trace
            .as_ref()
            .map(|trace| CounterExample { trace, cycle: None });
        check(&mut rebuilder, ir, &run, counter_example).map(Checking::Checked)
    })
    .map(Some)
    .map_err(|Unsupported(why)| why)
}

// What TLC's simulator finds of its postconditions: what they printed and the first that doesn't
// hold, or the configuration's error that rejects one.
enum Checking {
    Checked(Postconditions),
    Rejected(String),
}

// `EC.TLC_CONFIG_ID_MUST_NOT_BE_CONSTANT`, and the status TLC exits with after it.
const MUST_NOT_BE_CONSTANT: u32 = 2233;
const ERROR_CONFIG_PARSE: i32 = 151;

// What reporting the postconditions leaves: the status TLC exits with, and whether TLC goes on to
// report its progress, which it doesn't once it rejected one.
struct Reported {
    status: i32,
    is_rejected: bool,
}

/// Prints what the postconditions printed and the first that doesn't hold, and returns the
/// status TLC exits with for them.
fn report_postconditions(
    printer: &mut Printer,
    ir: &tla_ir::Ir,
    checking: Option<&Checking>,
) -> Result<Reported, &'static str> {
    let checked = match checking {
        None => {
            return Ok(Reported {
                status: SUCCESS,
                is_rejected: false,
            });
        }
        Some(Checking::Rejected(message)) => {
            printer.outcome.status = Some("error");
            printer.report(MUST_NOT_BE_CONSTANT, message);
            return Ok(Reported {
                status: ERROR_CONFIG_PARSE,
                is_rejected: true,
            });
        }
        Some(Checking::Checked(checked)) => checked,
    };
    for line in &checked.printed {
        printer.replayed(ir, line)?;
    }
    if checked.failure.is_none() {
        return Ok(Reported {
            status: SUCCESS,
            is_rejected: false,
        });
    }
    printer.outcome.status = Some("postcondition-violation");
    print_postcondition_failure(printer, ir, Some(checked));
    Ok(Reported {
        status: ASSUMPTION_VIOLATION,
        is_rejected: false,
    })
}

fn print_postconditions(
    printer: &mut Printer,
    ir: &tla_ir::Ir,
    violation: Option<(&Violation, Ending)>,
) -> Result<Reported, String> {
    let checking = check_postconditions_of(ir, violation)?;
    report_postconditions(printer, ir, checking.as_ref()).map_err(String::from)
}

// What the report of a simulation's failure reads.
struct Failing<'a> {
    ir: &'a tla_ir::Ir,
    config: &'a ModelConfig,
    dumps: &'a TraceDumps,
    simulated: &'a Simulated,
    simulation: &'a Simulation,
    initial_label: Option<&'a str>,
}

/// TLC's simulator's report of a failure evaluating the model (`Simulator.simulate`): on the main
/// thread, as it computes the initial states (a general error) or checks one (`EC.TLC_INITIAL_STATE`
/// with the state), then the summary; on the worker, as it checks a successor (an invariant's or
/// an action property's failure, with the trace to the successor), or anywhere else, as the
/// exception it is, with the trace to the state it was expanding: a TLCRuntimeException at its
/// own code without the summary (`printBehavior(TLCRuntimeException, ...)`), and any other as a
/// general error with it. The progress reporter then reports once more.
fn print_simulated_failure(
    printer: &mut Printer,
    failing: &Failing<'_>,
    violation: &Violation,
    site: ErrorSite,
    start: Instant,
) -> Result<i32, String> {
    let Failing {
        ir,
        config,
        dumps,
        simulated,
        simulation,
        initial_label,
    } = *failing;
    if dumps.is_trace_recorded() {
        return Err("the trace exploration spec's postcondition, which TLC checks of it".into());
    }
    // TLC's message may write a value of the run TLC holds as an empty record.
    if violation.store.is_empty_tuple_ambiguous() {
        return Err("a model that reads the statistics or registers of the run".into());
    }
    // The model sets registers or draws at random as the search did, which evaluating the failure
    // again doesn't follow.
    if is_effectful(ir) {
        return Err("a model that sets registers or draws at random".into());
    }
    // A check of a successor that fails is an error TLC's worker reports as it goes on to its
    // next trace, so the counts race it but in the last trace; an exception stops the worker.
    let is_successor = matches!(site, ErrorSite::Invariant(_) | ErrorSite::ActionProperty(_));
    if is_successor
        && simulation
            .traces
            .is_none_or(|traces| simulated.traces < traces.max(1))
    {
        return Err(
            "a successor's check that fails before the last trace, whose counts race TLC's worker"
                .into(),
        );
    }
    let trace_site = match site {
        ErrorSite::Init => Site::Init,
        ErrorSite::InitialInvariant(position) => Site::InitialInvariant(position),
        ErrorSite::Next => Site::Next,
        ErrorSite::Invariant(position) => Site::Invariant(position),
        ErrorSite::ActionProperty(position) => Site::ActionProperty(position),
        _ => return Err("a site TLC's simulator doesn't fail at".into()),
    };
    // The states TLC holds, whose texts can't depend on how TLC built them, which it built
    // without fingerprinting them.
    let store = &violation.store;
    if violation.holds_collapsed
        || violation
            .states
            .iter()
            .flatten()
            .any(|&value| !is_printable(store, value) || holds_record(store, value))
    {
        return Err("a state whose values TLC may hold otherwise than the engine".into());
    }
    let failure = {
        let states: Vec<&[Id]> = violation.states.iter().map(Vec::as_slice).collect();
        let workers = 1;
        on_search_stack(|| {
            let mut rebuilder = Rebuilder::new(ir)?;
            rebuilder.set_simulation();
            rebuilder.set_workers(workers);
            rebuilder.set_startup(store, &violation.startup, violation.startup_random)?;
            rebuilder.set_chosen(store, &violation.chosen);
            rebuilder.evaluate_simulated_failure(
                store,
                &states,
                &violation.labels,
                trace_site,
                simulated.failed_action,
            )
        })
        .map_err(|Unsupported(why)| why)?
    };
    let message = if printer.is_tool {
        &failure.tool_text
    } else {
        &failure.text
    };
    let general = |class_name: &str| {
        format!(
            "TLC threw an unexpected exception.\nThis was probably caused by an error in the spec or model.\nSee the User Output or TLC Console for clues to what happened.\nThe exception was a {class_name}\n: {message}"
        )
    };
    let texts = get_state_texts(ir, config, dumps, violation, printer.is_tool)
        .and_then(without_alias_output)?;
    // TLC's main thread reports a failure among the initial states with its summary.
    let (code, headline, exit_code, is_summarized) = match site {
        ErrorSite::Init => (code::GENERAL, general(failure.class_name), ERROR, true),
        ErrorSite::InitialInvariant(_) => {
            let state = texts.first().ok_or("an initial state the failure lacks")?;
            (
                INITIAL_STATE,
                format!("{message}\nWhile working on the initial state:\n{state}"),
                ERROR,
                true,
            )
        }
        ErrorSite::Invariant(owner) => {
            let name = invariant_name(ir, owner as usize).ok_or("a name the IR doesn't carry")?;
            (
                tla_trace::SIMULATED_INVARIANT_FAILED,
                format!("Evaluating invariant {name} failed.\n{message}"),
                FAILURE_SAFETY_EVAL,
                true,
            )
        }
        ErrorSite::ActionProperty(position) => {
            let property = ir
                .model
                .action_properties
                .get(position as usize)
                .ok_or("an action property the model doesn't have")?;
            (
                tla_trace::SIMULATED_ACTION_PROPERTY_FAILED,
                format!(
                    "Evaluating action property {} failed.\n{message}",
                    ir.texts[property.name as usize]
                ),
                VIOLATION_LIVENESS,
                true,
            )
        }
        _ if failure.is_tlc_runtime => match failure.code.filter(|&code| code != code::GENERAL) {
            Some(code) => {
                let exit_code =
                    exit_status(code).ok_or("a failure whose code TLC exits by otherwise")?;
                let text = if printer.is_tool {
                    failure.body_tool_text.clone()
                } else {
                    failure.text.clone()
                };
                (code, text, exit_code, false)
            }
            None => (code::GENERAL, general(failure.class_name), ERROR, false),
        },
        _ => (code::GENERAL, general(failure.class_name), ERROR, true),
    };
    let is_main = matches!(site, ErrorSite::Init | ErrorSite::InitialInvariant(_));
    printer.outcome.status = Some("error");
    printer.report(code, &headline);
    if !is_main {
        print_behavior(printer, ir, simulation, violation, &texts, initial_label)?;
    }
    if is_summarized {
        print_summary(printer, simulated, simulation);
    }
    if !is_main {
        print_progress(
            printer,
            simulated.generated,
            simulated.traces,
            simulated.lengths,
        );
    }
    print_finished(printer, start);
    Ok(exit_code)
}

// `SimulationWorker.addElement`'s report of a successor its action left a variable unassigned in
// (`EC.TLC_STATE_NOT_COMPLETELY_SPECIFIED_NEXT`), which `Simulator.simulate` prints with the
// trace to the successor, whatever -continue says, then its summary: the variables it lacks, by
// name, and the action, where the next-state relation has several, by `Action.getName`; the
// successor prints a variable it lacks as null. The worker goes on to its next trace as the main
// thread prints, so the counts race it but in the last trace.
fn print_simulated_incomplete(
    printer: &mut Printer,
    failing: &Failing<'_>,
    violation: &Violation,
    start: Instant,
) -> Result<i32, String> {
    let Failing {
        ir,
        config,
        dumps,
        simulated,
        simulation,
        initial_label,
    } = *failing;
    if dumps.is_trace_recorded() || dumps.has_command_line_dumps() {
        return Err("the trace files of the behavior".into());
    }
    if config.alias.is_some() {
        return Err("an ALIAS of a state that lacks a variable".into());
    }
    // With -depth -1 TLC prints the error state alone.
    if simulation.depth == i32::MAX {
        return Err("the error state of an unbounded behavior".into());
    }
    if simulation
        .traces
        .is_none_or(|traces| simulated.traces < traces.max(1))
    {
        return Err("a failure before the last trace, whose counts race TLC's worker".into());
    }
    let store = &violation.store;
    let unassigned = tla_engine::machine::UNASSIGNED;
    let values = || {
        violation
            .states
            .iter()
            .flatten()
            .filter(|&&value| value != unassigned)
    };
    if violation.holds_collapsed
        || values().any(|&value| !is_printable(store, value) || holds_record(store, value))
    {
        return Err("a state whose values TLC may hold otherwise than the engine".into());
    }
    let successor = violation.states.last().ok_or("a trace without states")?;
    let action = simulated
        .failed_action
        .and_then(|action| ir.model.actions.get(action as usize))
        .ok_or("an action the IR lacks")?;
    if violation.labels.last().copied().flatten() != simulated.failed_action {
        return Err("a successor of another action than the one that failed".into());
    }
    let actions = &ir.model.actions;
    // `TLCStateMut.getUnassigned` sorts the names.
    let mut names: Vec<&str> = (successor.iter().enumerate())
        .filter(|&(_, &value)| value == unassigned)
        .map(|(variable, _)| ir.texts[ir.variables[variable] as usize].as_ref())
        .collect();
    names.sort_unstable();
    if names.is_empty() {
        return Err("a successor that lacks no variable".into());
    }
    let subject = if actions.len() == 1 {
        "the next-state action".to_string()
    } else {
        format!(
            "action {} of the next-state relation",
            ir.texts[action.name as usize]
        )
    };
    let (noun, verb) = if names.len() > 1 {
        ("variables", "are")
    } else {
        ("variable", "is")
    };
    let texts = violation
        .states
        .iter()
        .map(|state| {
            let texts = state
                .iter()
                .map(|&value| match value {
                    value if value == unassigned => Ok("null".to_string()),
                    value => format_value(store, value),
                })
                .collect::<Result<Vec<String>, _>>()
                .map_err(|bail| bail.0.to_string())?;
            Ok(format_texts(ir, &texts))
        })
        .collect::<Result<Vec<String>, String>>()?;
    printer.outcome.status = Some("error");
    printer.report(
        code::INCOMPLETE_SUCCESSOR,
        &format!(
            "Successor state is not completely specified by {subject}. The following {noun} {verb} not defined: {}.\n",
            names.join(", ")
        ),
    );
    print_behavior(printer, ir, simulation, violation, &texts, initial_label)?;
    print_summary(printer, simulated, simulation);
    print_progress(
        printer,
        simulated.generated,
        simulated.traces,
        simulated.lengths,
    );
    print_finished(printer, start);
    Ok(crate::failure::FAILURE_SPEC_EVAL)
}

// The status TLC exits with after an error of this code (`EC.ExitStatus.errorConstantToExitStatus`),
// where it is the general one: the codes it maps otherwise aren't followed.
fn exit_status(code: u32) -> Option<i32> {
    const MAPPED: &[u32] = &[
        2253, 2109, 2115, 2103, 2147, 2111, 2146, 2107, 2110, 2112, 2113, 2116, 2108, 2114, 2104,
        2105, 2404, 2405, 2780, 2132, 2222, 2223, 2224, 2225, 2280, 2281, 2226, 2227, 2228, 2229,
        2230, 2231, 2232, 2233, 2234, 2235, 2236, 2237, 2238, 2239, 2240, 2241, 2272, 2273, 2274,
        2242, 2243, 2244, 2245, 5001, 5002, 5003, 5004, 5005, 5006, 5007, 2171, 3002, 1000,
    ];
    (!MAPPED.contains(&code)).then_some(ERROR)
}

// The name TLC gives the invariant at this position of the model's, then of its properties
// checked as invariants.
fn invariant_name(ir: &tla_ir::Ir, owner: usize) -> Option<&str> {
    let model = &ir.model;
    let name = match owner.checked_sub(model.invariants.len()) {
        None => model.invariants[owner].root.name,
        Some(property) => *model.property_invariant_names.get(property)?,
    };
    Some(&ir.texts[name as usize])
}

/// `Simulator.printBehavior`: the trace, or with an unbounded depth the error state alone.
fn print_behavior(
    printer: &mut Printer,
    ir: &tla_ir::Ir,
    simulation: &Simulation,
    violation: &Violation,
    texts: &[String],
    initial_label: Option<&str>,
) -> Result<(), String> {
    if simulation.depth == i32::MAX {
        let text = texts.last().map_or("", String::as_str);
        printer.print(ERROR_STATE, Level::None, "The error state is:\n");
        printer.print(code::STATE_PRINT_1, Level::State, &format!(":\n{text}"));
        return Ok(());
    }
    let initial_label = initial_label.ok_or("the label of an initial predicate")?;
    let mut labels = vec![initial_label.to_string()];
    for label in &violation.labels {
        let action = label.and_then(|action| ir.model.actions.get(action as usize));
        let action = action.ok_or("a step whose action the trace lacks")?;
        labels.push(ir.texts[action.label as usize].to_string());
    }
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
    Ok(())
}

type AliasOutput = Vec<Vec<crate::trace::PrintedOutput>>;

// A simulation's trace whose ALIAS prints nothing. TLC prints what an ALIAS prints before each
// state of a simulated behavior (`Simulator.printBehavior`), and again as it holds the
// behavior's counterexample for the postconditions after its summary
// (`SimulationWorkerError.getTrace`), which the binary doesn't follow.
fn without_alias_output(
    (texts, alias_output): (Vec<String>, AliasOutput),
) -> Result<Vec<String>, String> {
    if alias_output.iter().any(|output| !output.is_empty()) {
        return Err("a simulated behavior printed through an ALIAS that prints".into());
    }
    Ok(texts)
}

// Each state of the trace as TLC prints it: as the store holds it where its text can't depend on
// how TLC built it, and otherwise as the trace evaluator rebuilds it; with what the ALIAS prints
// as TLC evaluates it on each.
fn get_state_texts(
    ir: &tla_ir::Ir,
    config: &ModelConfig,
    dumps: &TraceDumps,
    violation: &Violation,
    is_tool: bool,
) -> Result<(Vec<String>, AliasOutput), String> {
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
            .collect::<Result<_, _>>()
            .map(|texts| (texts, Vec::new()));
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
        TraceChecks {
            workers: None,
            dumps,
            run: None,
        },
        is_tool,
        false,
    )?;
    Ok(trace
        .states
        .into_iter()
        .map(|state| (format_variables(&state.variables), state.alias_output))
        .unzip())
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
