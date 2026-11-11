//! `prove-it <Spec>...`: `checkSpecs` and `checkSpec` in `src/cli/tlc.ts`. Each spec is checked as
//! TLC would in a process of its own; the exit code is the first that is not success.

use std::path::Path;
use std::sync::mpsc;
use std::time::Duration;
use tla_engine::Prints;
use tla_engine::clock::Instant;

use tla_engine::search::{
    Continued, ContinuedTrace, Delegated, ErrorSite, MINIMUM_SHARED_LEVEL, Reporter, SearchOutcome,
    Settings, Violation, ViolationKind, search,
};
use tla_live::{Liveness, Verdict};
use tla_values::print::{is_printable, is_printable_normalized, write_value};
use tla_values::{Id, Store};

use crate::args::{Java, Parsed, Stop, USAGE, get_java_launch, is_auto};
use crate::coverage;
use crate::dump_trace::{TraceDumps, is_writable, write};
use crate::failure::{ErrorStop, print_assumption_failure, print_failure};
use crate::front::{Failure, Read, read_front};
use crate::host::{Files, Host};
use crate::jar::{get_tools_jar, is_174};
use crate::messages::{self as code, Level, Output, Printer};
use crate::outcome::{Counts, Reported, ReportedState};
use crate::simulation::{Simulating, check_simulation, get_simulation, print_banner};
use crate::stack::{alongside, on_search_stack};
use crate::summary::{
    actual_probability, fingerprint_distance, format_count, format_probability,
    optimistic_probability, out_degree_summary,
};
use crate::te_spec::{self, TraceSpec};
use crate::time::format_duration;
use crate::trace::{
    PostconditionRun, Postconditions, PrintedState, PrintedTrace, TraceChecks,
    check_postconditions, format_print, format_texts, format_variables, rebuild_accepted,
    rebuild_continued, rebuild_trace,
};
use crate::xml_exporter::run_xml_exporter;
use tla_front::TlcVersion;
use tla_front::config::{ModelConfig, parse_config};
use tla_front::errors::{FrontError, UNEXPECTED_EXCEPTION};
use tla_front::model::StartupMessage;
use tla_front::tlc_messages::CodedError;
use tla_trace::{Rebuilder, Site, Unsupported, pretty_print};
use tla_trace::{Stats, Verdict as PostconditionVerdict};

// TLC's exit statuses, from EC.ExitStatus.
pub(crate) const SUCCESS: i32 = 0;
pub(crate) const DEADLOCK: i32 = 11;
pub(crate) const ASSUMPTION_VIOLATION: i32 = 10;
pub(crate) const SAFETY_VIOLATION: i32 = 12;
const LIVENESS_VIOLATION: i32 = 13;
const NO_NEXT_ACTION: i32 = 75;
const SPEC_PARSE_ERROR: i32 = 150;
const CONFIG_PARSE_ERROR: i32 = 151;

/// The exit code of a run that needs something the binary doesn't do natively yet.
const NOT_NATIVE: i32 = 1;
// How much of the -dump file's text the relay holds before it sends it to be written.
const DUMP_PART_BYTES: usize = 1 << 20;

const GLOB_CHARACTERS: [char; 4] = ['*', '?', '[', '{'];

/// Runs the command line `args` as TLC (or SANY's XMLExporter) would, writing to `output`, and
/// returns the exit code.
pub fn run(args: &[String], output: &mut Output<'_>) -> i32 {
    if args.first().is_some_and(|arg| arg == "tlapm") {
        return not_native(output, "tlapm");
    }
    let Some(mut launch) = get_java_launch(args) else {
        return check_specs(args, &Java::default(), false, output);
    };
    // Without -Dtla-ts.tlc, the jar on the class path picks the TLC to reproduce.
    let jar = launch.java.class_path.as_deref().and_then(get_tools_jar);
    if let (None, Some(jar)) = (launch.java.tlc_version, jar) {
        launch.java.tlc_version = match is_174(output.host, jar) {
            Ok(true) => Some(TlcVersion::V1_7_4),
            Ok(false) => Some(TlcVersion::Master),
            Err(reason) => {
                return not_native(output, &format!("the version of {jar}: {reason}"));
            }
        };
    }
    match launch.main_class.as_str() {
        "tlc2.TLC" => match &launch.java.unmodelled_property {
            Some(property) => not_native(output, &format!("the system property {property}")),
            None => check_specs(&launch.args, &launch.java, true, output),
        },
        "tla2sany.xml.XMLExporter" => match &launch.java.unmodelled_property {
            Some(property) => not_native(output, &format!("the system property {property}")),
            // TLC 1.7.4's XMLExporter is retired, and only master's is ported.
            None if launch.java.tlc_version == Some(TlcVersion::V1_7_4) => {
                not_native(output, "TLC 1.7.4")
            }
            None => run_xml_exporter(&launch.args, output)
                .unwrap_or_else(|reason| not_native(output, &reason)),
        },
        other => {
            let _ = writeln!(
                output.err,
                "Error: tla-ts runs the Java classes tlc2.TLC and tla2sany.xml.XMLExporter, not {other}."
            );
            1
        }
    }
}

fn not_native(output: &mut Output<'_>, what: &str) -> i32 {
    let _ = writeln!(output.err, "prove-it: not native yet: {what}");
    NOT_NATIVE
}

fn file_name(path: &str) -> String {
    Path::new(path).file_name().map_or_else(
        || path.to_string(),
        |name| name.to_string_lossy().into_owned(),
    )
}

// With `is_tlc` the command line is `tlc2.TLC`'s, which names one module.
fn check_specs(args: &[String], java: &Java, is_tlc: bool, output: &mut Output<'_>) -> i32 {
    if java.tlc_version == Some(TlcVersion::V1_7_4) {
        return not_native(output, "TLC 1.7.4");
    }
    let parsed = match Parsed::parse(args, is_tlc) {
        Ok(parsed) => parsed,
        Err(Stop::NotNative(what)) => return not_native(output, &what),
        Err(Stop::Error { message, is_tool }) => {
            return print_command_line_error(&mut Printer::new(is_tool, true, output), &message);
        }
    };
    // TLC takes Spec.cfg for a module of that name.
    if is_tlc && parsed.positionals.iter().any(|path| path.ends_with(".cfg")) {
        return not_native(output, "a module named as a configuration file");
    }
    if parsed
        .positionals
        .iter()
        .any(|path| path.contains(GLOB_CHARACTERS))
    {
        return not_native(output, "globs");
    }
    let is_configured = parsed.has("-config");
    // Like TLC, a spec named without an extension is the .tla file of that name.
    let spec_paths: Vec<String> = parsed
        .positionals
        .iter()
        .map(|path| match path.strip_suffix(".cfg") {
            Some(stem) => format!("{stem}.tla"),
            None if path.ends_with(".tla") => path.clone(),
            None => format!("{path}.tla"),
        })
        .collect();
    if spec_paths.is_empty() {
        let _ = writeln!(output.err, "{USAGE}");
        return 1;
    }
    if is_configured && spec_paths.len() > 1 {
        let _ = writeln!(
            output.err,
            "Error: -config applies to one specification, but several were given."
        );
        return 1;
    }
    // TLC also looks for the spec itself in the library directories.
    let mut paths: Vec<String> = Vec::new();
    for path in spec_paths.clone() {
        let found = if output.host.is_file(Path::new(&path)) || Path::new(&path).is_absolute() {
            path
        } else {
            java.libraries
                .iter()
                .map(|directory| Path::new(directory).join(&path))
                .find(|candidate| output.host.is_file(candidate))
                .map(|candidate| candidate.to_string_lossy().into_owned())
                .unwrap_or(path)
        };
        if !paths.contains(&found) {
            paths.push(found);
        }
    }
    if paths.len() > 1 && !output.host.is_checking_several() {
        return not_native(
            output,
            "several specifications in one check of a host's sources",
        );
    }
    let mut exit_codes = Vec::new();
    for (index, (path, given)) in paths.iter().zip(&spec_paths).enumerate() {
        let mut printer = Printer::new(parsed.has("-tool"), !parsed.has("-nowarning"), output);
        if index > 0 {
            printer.line("");
        }
        // TLC checks one spec, so Prove It names each of several it checks.
        if paths.len() > 1 {
            let name = file_name(path);
            let stem = name.strip_suffix(".tla").unwrap_or(&name);
            printer.line(&format!("Checking {name} with {stem}.cfg"));
        }
        // TLC names the trace exploration spec's directory by the path it was given, not where it
        // found the spec.
        let main_file = (path == given).then(|| given.strip_suffix(".tla").unwrap_or(given));
        let exit_code = check_spec(path, main_file, &parsed, java, &mut printer);
        // The other specs are checked as after any spec the binary declines.
        exit_codes.push(match printer.trace_spec_decline.take() {
            Some(reason) => report_not_native(&mut printer, &reason),
            None => exit_code,
        });
    }
    exit_codes
        .into_iter()
        .find(|&exit_code| exit_code != SUCCESS)
        .unwrap_or(SUCCESS)
}

fn print_welcome(printer: &mut Printer) {
    printer.print(
        code::VERSION,
        Level::None,
        &format!("TLC2 Version {} (rev: tla-ts)", package_version()),
    );
}

/// The version of the npm package the binary is built with.
fn package_version() -> &'static str {
    const PACKAGE: &str = include_str!("../../../../package.json");
    PACKAGE
        .split_once("\"version\": \"")
        .and_then(|(_, rest)| rest.split_once('"'))
        .map_or("0.0.0", |(version, _)| version)
}

/// TLC.printErrorMsg: TLC says which version it is, then why it can't read its options.
fn print_command_line_error(printer: &mut Printer, message: &str) -> i32 {
    print_welcome(printer);
    printer.print(
        code::COMMAND_LINE_ERROR,
        Level::Error,
        &format!("{message}\nUsage: java tlc2.TLC [-help] [-option] inputfile"),
    );
    1
}

// A whole number an environment variable sets.
fn get_number(host: &dyn Host, name: &str) -> Option<usize> {
    host.get_variable(name)?.parse().ok()
}

/// TLC.printStartupBanner, with what runs Prove It in place of the JVM.
fn print_startup_banner(
    printer: &mut Printer,
    fingerprint_index: usize,
    seed: i64,
    workers: usize,
) {
    let machine = printer.host.machine();
    let (system, release, arch) = (&machine.system, &machine.release, &machine.arch);
    printer.print(
        code::MODEL_CHECKING,
        Level::None,
        &format!(
            "Running breadth-first search Model-Checking with fp {fingerprint_index} and seed {seed} with {workers} worker{} on {} cores with {}MB heap and 0MB offheap memory [pid: {}] ({system} {release} {arch}, prove-it native {}bit, MemFPSet, MemStateQueue).",
            if workers == 1 { "" } else { "s" },
            machine.cores,
            machine.memory_megabytes,
            machine.pid,
            usize::BITS,
        ),
    );
}

/// JavaScript's `Math.max(1, Number.parseInt(value, 10) || 1)`.
/// What the search reports as it runs, relayed from its thread.
pub(crate) enum Event {
    /// What TLC prints itself as it starts, after the constant definitions and before the
    /// assumptions, as tla-front writes it.
    StartupMessage(StartupMessage),
    InitialStatesStarted,
    InitialStatesProgress(u64),
    InitialStates(u64, u64),
    Progress(u64, u64, u64, u64),
    /// TLC checks the temporal properties part way through the search: of how many branches, on
    /// behavior graphs of how many states in all.
    LivenessStarted(u64, u64),
    LivenessFinished,
    /// What Print or PrintT printed, or nothing when TLC's text isn't known.
    Print(Option<String>),
    /// TLC warns that the sets the symmetry permutes, by these names, hold fewer than two
    /// elements.
    SymmetrySetsTooSmall(Vec<String>),
    /// TLC would evaluate the `_PERIODIC` expression now, as it prints its progress, which the
    /// engine doesn't: the search ends as not native.
    Periodic,
    /// TLC would print a coverage report now, as it prints its progress, at a point that depends
    /// on how fast it runs: the search ends as not native.
    CoverageReported,
    /// A simulation's progress: the states checked, the traces generated, and TLC's packed mean
    /// and squared deviations of their lengths.
    SimulationProgress(u64, u64, i64),
    /// A part of the `-dump` file's text, in order, for the host to append.
    Dumped(String),
    /// Under -continue, a violation the search went on past, as TLC reports it.
    Continued(Box<ContinuedReport>),
    /// The relay can't print what TLC prints next, for this reason: the search ends as not
    /// native.
    Declined(String),
}

/// A violation TLC reports under -continue and goes on past: its headline, and its trace with
/// each step's label, or the initial state alone.
pub(crate) struct ContinuedReport {
    code: u32,
    headline: String,
    trace: PrintedTrace,
    labels: Vec<String>,
    is_initial: bool,
}

pub(crate) struct Relay<'ir> {
    sender: mpsc::Sender<Event>,
    /// Whether something printed has a text TLC's isn't known to be, which ends the search.
    is_misprinted: bool,
    /// Whether the configuration names a `_PERIODIC` expression, which TLC evaluates as it prints
    /// its progress; the search ends there, if it gets that far.
    is_periodic: bool,
    is_periodic_reached: bool,
    /// With -coverage, how many more progress reports TLC prints before the one it follows with
    /// a coverage report (`count` in `AbstractChecker.runTLC`).
    coverage_countdown: Option<i32>,
    is_coverage_reached: bool,
    /// Whether the relay sent `Event::Declined`.
    is_declined: bool,
    /// Whether `-dump` writes each state the search found, as TLC's `StateWriter` does: the relay
    /// sends the text in parts (`Event::Dumped`) for the host to write.
    is_dumped: bool,
    /// Whether the dump holds every state, or why it doesn't, once the search handed them over.
    dumped: Option<Result<(), &'static str>>,
    ir: &'ir tla_ir::Ir,
    is_tool: bool,
    /// Whether a trace's states carry plain data (`Host::is_plain`).
    is_plain: bool,
    workers: usize,
    /// What TLC prints itself at `startup_done`, as tla-front writes it.
    startup_messages: Vec<StartupMessage>,
    /// What the substitutes and constant definitions printed as the store words it, where it
    /// does, until `startup_done`.
    startup_worded: Option<Vec<Option<String>>>,
    /// What the assumptions printed as the store words it, or as the trace evaluator printed an
    /// assumption the engine left to it, from `startup_done` on.
    assumed_worded: Vec<Option<String>>,
    /// What the run printed of the assumptions, from `startup_done` on.
    pub(crate) assumed_printed: Vec<String>,
    /// Why the trace evaluator mustn't check an assumption the engine leaves to it, as where it
    /// would read the model checker's TLCGet in a simulation.
    pub(crate) undelegated: Option<&'static str>,
    /// What the trace evaluator finds the assumptions print, in order, where the store forgot how
    /// TLC built a value one prints.
    assumed_texts: Option<Option<Vec<String>>>,
    /// What the trace evaluator finds they print, as TLC built the values, where the store
    /// forgot how TLC built one.
    startup_texts: Option<Option<Vec<String>>>,
}

impl<'ir> Relay<'ir> {
    pub(crate) fn new(
        sender: mpsc::Sender<Event>,
        ir: &'ir tla_ir::Ir,
        is_tool: bool,
        is_plain: bool,
        workers: usize,
        startup_messages: Vec<StartupMessage>,
    ) -> Self {
        Relay {
            sender,
            is_misprinted: false,
            is_periodic: false,
            is_periodic_reached: false,
            coverage_countdown: None,
            is_coverage_reached: false,
            is_declined: false,
            is_dumped: false,
            dumped: None,
            ir,
            is_tool,
            is_plain,
            workers,
            startup_messages,
            startup_worded: Some(Vec::new()),
            assumed_worded: Vec::new(),
            assumed_printed: Vec::new(),
            assumed_texts: None,
            startup_texts: None,
            undelegated: None,
        }
    }

    fn send_print(&mut self, printed: Option<String>) {
        self.is_misprinted |= printed.is_none();
        let _ = self.sender.send(Event::Print(printed));
    }

    // What an assumption prints, which the trace evaluator prints as TLC built it where the store
    // forgot, as long as it prints the same: each print before it the store worded alike.
    fn word_assumed(&mut self, worded: Option<String>) -> Option<String> {
        self.assumed_worded.push(worded.clone());
        if self.assumed_texts.is_none() && worded.is_some() {
            return worded;
        }
        let ir = self.ir;
        let (workers, is_tool) = (self.workers, self.is_tool);
        let worded_prints = &self.assumed_worded;
        let texts = self.assumed_texts.get_or_insert_with(|| {
            // Each assumption's prints in turn, up to one the evaluator doesn't follow, as TLC
            // stops at an assumption that doesn't hold.
            let mut texts = Vec::new();
            for position in 0..ir.model.startup.assumptions.len() as u32 {
                let checked = Rebuilder::new(ir).and_then(|mut rebuilder| {
                    rebuilder.set_workers(workers);
                    rebuilder.check_assumption(position, is_tool)
                });
                let Ok(checked) = checked else {
                    break;
                };
                texts.extend(checked.printed.iter().map(|print| format_print(print)));
                if checked.holds != Some(true) {
                    break;
                }
            }
            let index = worded_prints.len() - 1;
            (texts.len() > index
                && worded_prints[..index]
                    .iter()
                    .zip(&texts)
                    .all(|(worded, text)| worded.as_ref() == Some(text)))
            .then_some(texts)
        });
        let index = self.assumed_worded.len() - 1;
        texts
            .as_ref()
            .and_then(|texts| texts.get(index))
            .filter(|text| worded.as_ref().is_none_or(|worded| worded == *text))
            .cloned()
    }
}

impl Reporter for Relay<'_> {
    fn is_cancelled(&self) -> bool {
        self.is_misprinted
            || self.is_periodic_reached
            || self.is_coverage_reached
            || self.is_declined
    }

    // TLC prints each violation with its trace as it finds it under -continue (`printTrace`).
    fn continued(&mut self, continued: ContinuedTrace<'_>) {
        let ir = self.ir;
        let (kind, code, headline) = match continued.kind {
            Continued::InitialInvariant(owner) => (
                ViolationKind::InitialInvariant(owner),
                code::INVARIANT_VIOLATED_INITIAL,
                invariant_name(ir, owner)
                    .map(|name| format!("Invariant {name} is violated by the initial state:")),
            ),
            Continued::Invariant(owner) => (
                ViolationKind::Invariant(owner),
                code::INVARIANT_VIOLATED_BEHAVIOR,
                invariant_name(ir, owner).map(|name| format!("Invariant {name} is violated.")),
            ),
            Continued::ActionProperty(position) => (
                ViolationKind::ActionProperty(position),
                code::ACTION_PROPERTY_VIOLATED_BEHAVIOR,
                action_property_headline(ir, position),
            ),
        };
        let is_initial = matches!(kind, ViolationKind::InitialInvariant(_));
        let report = headline.map_err(String::from).and_then(|headline| {
            let trace = rebuild_continued(ir, &continued, &kind, self.is_tool, self.is_plain)?;
            let labels = trace_labels(ir, &trace)?
                .into_iter()
                .map(String::from)
                .collect();
            Ok(ContinuedReport {
                code,
                headline,
                trace,
                labels,
                is_initial,
            })
        });
        match report {
            Ok(report) => {
                let _ = self.sender.send(Event::Continued(Box::new(report)));
            }
            Err(reason) => {
                self.is_declined = true;
                let _ = self.sender.send(Event::Declined(format!(
                    "a trace under -continue: {reason}"
                )));
            }
        }
    }

    fn initial_states_started(&mut self) {
        let _ = self.sender.send(Event::InitialStatesStarted);
    }

    fn initial_states_progress(&mut self, count: u64) {
        let _ = self.sender.send(Event::InitialStatesProgress(count));
    }

    fn initial_states(&mut self, generated: u64, distinct: u64) {
        let _ = self.sender.send(Event::InitialStates(generated, distinct));
    }

    // TLC evaluates the `_PERIODIC` expression in `doPeriodicWork` just before it prints its
    // progress, and not at all in a run that ends first (AbstractChecker.runTLC).
    fn progress(&mut self, generated: u64, distinct: u64, queued: u64, depth: u64) {
        if self.is_periodic {
            self.is_periodic_reached = true;
            let _ = self.sender.send(Event::Periodic);
            return;
        }
        // TLC prints a coverage report after the progress where `count` is 0, which it counts
        // down from -coverage's minutes once per progress report (ModelChecker.runTLCContinueDoing).
        if let Some(countdown) = &mut self.coverage_countdown {
            if *countdown == 0 {
                self.is_coverage_reached = true;
                let _ = self.sender.send(Event::CoverageReported);
                return;
            }
            *countdown -= 1;
        }
        let _ = self
            .sender
            .send(Event::Progress(generated, distinct, queued, depth));
    }

    fn liveness_started(&mut self, branches: u64, _expanded: u64, states: u64, _counts: [u64; 3]) {
        let _ = self.sender.send(Event::LivenessStarted(branches, states));
    }

    fn liveness_finished(&mut self) {
        let _ = self.sender.send(Event::LivenessFinished);
    }

    fn simulation_progress(&mut self, generated: u64, traces: u64, lengths: i64) {
        let _ = self
            .sender
            .send(Event::SimulationProgress(generated, traces, lengths));
    }

    fn print(&mut self, store: &Store, prints: &Prints) {
        self.send_print(format_printed(store, prints));
    }

    // What the substitutes and constant definitions print, which the trace evaluator prints as
    // TLC built it where the store forgot, as long as it prints the same: each print the store
    // words alike, and as many.
    fn startup_print(&mut self, store: &Store, prints: &Prints) {
        let worded = format_printed(store, prints);
        let Some(worded_prints) = self.startup_worded.as_mut() else {
            let printed = self.word_assumed(worded);
            self.assumed_printed.extend(printed.clone());
            self.send_print(printed);
            return;
        };
        worded_prints.push(worded.clone());
        if self.startup_texts.is_none() && worded.is_some() {
            self.send_print(worded);
            return;
        }
        let ir = self.ir;
        let startup = &ir.model.startup;
        let texts = self.startup_texts.get_or_insert_with(|| {
            let texts = startup
                .symmetry
                .is_none()
                .then(|| Rebuilder::new(ir).and_then(|mut rebuilder| rebuilder.startup_prints()))
                .and_then(Result::ok)?;
            let texts: Vec<String> = texts.iter().map(|print| format_print(print)).collect();
            // The prints already sent, which the store worded, must be the evaluator's.
            let index = worded_prints.len() - 1;
            (texts.len() > index
                && worded_prints[..index]
                    .iter()
                    .zip(&texts)
                    .all(|(worded, text)| worded.as_ref() == Some(text)))
            .then_some(texts)
        });
        let index = worded_prints.len() - 1;
        let printed = texts
            .as_ref()
            .and_then(|texts| texts.get(index))
            .filter(|text| worded.as_ref().is_none_or(|worded| worded == *text))
            .cloned();
        self.send_print(printed);
    }

    fn startup_done(&mut self) {
        let count = self.startup_worded.take().map(|worded| worded.len());
        if let Some(Some(texts)) = &self.startup_texts
            && Some(texts.len()) != count
        {
            self.send_print(None);
        }
        for message in self.startup_messages.drain(..) {
            let _ = self.sender.send(Event::StartupMessage(message));
        }
    }

    // The trace evaluator words TLC's messages, which AssertError compares. It runs on the
    // search's thread, with its stack.
    fn check_assumption(&mut self, position: u32) -> Result<Delegated, String> {
        if let Some(reason) = self.undelegated {
            return Err(reason.into());
        }
        let checked = Rebuilder::new(self.ir)
            .and_then(|mut rebuilder| {
                rebuilder.set_workers(self.workers);
                rebuilder.check_assumption(position, self.is_tool)
            })
            .map_err(|Unsupported(reason)| format!("checking an assumption again: {reason}"))?;
        // What the run printed of the assumption before it left it to the trace evaluator must be
        // what TLC prints first, after what the assumptions before it print.
        let expected: Vec<String> = checked
            .printed_before
            .iter()
            .chain(&checked.printed)
            .map(|print| format_print(print))
            .collect();
        if !expected.starts_with(&self.assumed_printed) {
            self.send_print(None);
            return Err("printing other than TLC prints".into());
        }
        for text in &expected[self.assumed_printed.len()..] {
            self.assumed_worded.push(Some(text.clone()));
            self.assumed_printed.push(text.clone());
            self.send_print(Some(text.clone()));
        }
        Ok(Delegated {
            holds: checked.holds,
            random: checked.random,
        })
    }

    fn symmetry_sets_too_small(&mut self, names: &[String]) {
        let _ = self
            .sender
            .send(Event::SymmetrySetsTooSmall(names.to_vec()));
    }

    // TLC writes "State N:", from 1, then the state as it prints it (`TLCStateMut.toString`) and
    // a blank line.
    fn dumped(&mut self, store: &Store, states: &[Id], width: usize) {
        if !self.is_dumped {
            return;
        }
        let ir = self.ir;
        if width == 0 || width != ir.variables.len() {
            self.dumped = Some(Err("-dump of states other than the variables' values"));
            return;
        }
        let mut text = String::new();
        let written = states
            .chunks(width)
            .enumerate()
            .try_for_each(|(index, state)| {
                let texts = state
                    .iter()
                    .map(|&id| {
                        let mut text = Vec::new();
                        // TLC fingerprints a state, which normalizes it, before it writes it.
                        is_printable_normalized(store, id)
                            .then(|| write_value(store, id, &mut text).ok())
                            .flatten()
                            .and_then(|()| String::from_utf16(&text).ok())
                    })
                    .collect::<Option<Vec<_>>>()
                    .ok_or("dumping a value whose text depends on how TLC built it")?;
                text.push_str(&format!(
                    "State {}:\n{}\n",
                    index + 1,
                    format_texts(ir, &texts)
                ));
                if text.len() >= DUMP_PART_BYTES {
                    let _ = self.sender.send(Event::Dumped(std::mem::take(&mut text)));
                }
                Ok(())
            });
        if !text.is_empty() {
            let _ = self.sender.send(Event::Dumped(text));
        }
        self.dumped = Some(written);
    }
}

// What Print or PrintT prints of the values: TLC's text of each that the engine knew, or that the
// store words, unless the store has forgotten how TLC built one.
fn format_printed(store: &Store, prints: &Prints) -> Option<String> {
    let printed = match &prints.texts {
        Some(texts) => texts.iter().map(|text| pretty_print(text)).collect(),
        None => prints
            .values
            .iter()
            .map(|&id| {
                if !is_printable(store, id) {
                    return None;
                }
                let mut text = Vec::new();
                write_value(store, id, &mut text).ok()?;
                Some(pretty_print(&text))
            })
            .collect::<Option<Vec<_>>>()?,
    };
    Some(printed.join("  "))
}

/// The counts a Progress line reports.
#[derive(Clone, Copy)]
pub(crate) struct Statistics {
    pub generated: u64,
    pub distinct: u64,
    pub queued: u64,
    pub depth: u64,
}

impl Statistics {
    pub fn counts(&self) -> Counts {
        Counts {
            generated: self.generated,
            distinct: self.distinct,
            queued: self.queued,
            depth: self.depth,
        }
    }
}

/// TLC reports a depth of at least 1, even before it finds a state, and rates a minute only once
/// the search has started.
fn print_progress(printer: &mut Printer, statistics: &Statistics, start: Option<Instant>) {
    let rate = |count: u64, unit: &str| {
        start.map_or_else(String::new, |start| {
            let minutes = (start.elapsed().as_millis().max(1) as f64) / 60_000.0;
            format!(
                " ({} {unit}/min)",
                format_count((count as f64 / minutes).floor() as u64)
            )
        })
    };
    printer.print(
        code::PROGRESS,
        Level::None,
        &format!(
            "Progress({}) at {}: {} states generated{}, {} distinct states found{}, {} states left on queue.",
            statistics.depth.max(1),
            printer.date(),
            format_count(statistics.generated),
            rate(statistics.generated, "s"),
            format_count(statistics.distinct),
            rate(statistics.distinct, "ds"),
            format_count(statistics.queued),
        ),
    );
}

fn print_initial_states(printer: &mut Printer, generated: u64, distinct: u64) {
    let date = printer.date();
    if generated == distinct {
        printer.print(
            code::INIT_GENERATED_1,
            Level::None,
            &format!(
                "Finished computing initial states: {distinct} distinct state{} generated at {date}.",
                if distinct == 1 { "" } else { "s" }
            ),
        );
    } else {
        printer.print(
            code::INIT_GENERATED_2,
            Level::None,
            &format!(
                "Finished computing initial states: {generated} state{} generated, with {distinct} of them distinct at {date}.",
                if generated == 1 { "" } else { "s" }
            ),
        );
    }
}

fn check_spec(
    spec_path: &str,
    main_file: Option<&str>,
    args: &Parsed,
    java: &Java,
    printer: &mut Printer,
) -> i32 {
    let started = printer.host.now();
    let seed = args
        .first("-seed")
        .and_then(|seed| seed.parse::<i64>().ok())
        .unwrap_or(0);
    // Without -fp, TLC picks a polynomial at random; Prove It picks the first.
    let fingerprint_index = args
        .first("-fp")
        .and_then(|index| index.parse().ok())
        .unwrap_or(0);
    let dump = args.get("-dump");
    let workers = match args.first("-workers") {
        Some(workers) if is_auto(workers) => printer.host.machine().cores,
        Some(workers) => workers.parse().unwrap_or(1),
        None => 1,
    };
    // With several workers TLC's counts depend on how the workers interleave.
    if args.has("-coverage") && workers > 1 {
        return report_not_native(
            printer,
            "coverage on more than one worker is timing-dependent in TLC",
        );
    }
    let simulation = get_simulation(args);
    // TLC's simulator also prints a coverage report, which the coverage pass, a replay of the
    // model checker's search, doesn't count.
    if args.has("-coverage") && simulation.is_some() {
        return report_not_native(printer, "coverage of a simulation");
    }
    print_welcome(printer);
    match &simulation {
        Some(simulation) => print_banner(printer, simulation.seed, workers),
        None => print_startup_banner(printer, fingerprint_index, seed, workers),
    }
    // TLC opens the file before it reads the configuration, and names it with a suffix of .dump
    // unless it has one.
    let dump = match dump {
        None => None,
        Some([file]) if !file.starts_with("${metadir}") => {
            let path = if file.ends_with(".dump") {
                file.clone()
            } else {
                format!("{file}.dump")
            };
            if !printer.host.write_file(Path::new(&path), b"", false) {
                return report_not_native(printer, "-dump into a file it can't create");
            }
            Some(path)
        }
        Some([_]) => return report_not_native(printer, "-dump into the meta directory"),
        Some(_) => return report_not_native(printer, "-dump dot"),
    };
    let config_path = match args.first("-config") {
        Some(path) => Some(path.to_string()),
        None => Some(match spec_path.strip_suffix(".tla") {
            Some(stem) => format!("{stem}.cfg"),
            None => spec_path.to_string(),
        }),
    };
    if !config_path
        .as_deref()
        .is_some_and(|path| printer.host.is_file(Path::new(path)))
    {
        printer.print(
            code::CONFIG_FILE_ERROR,
            Level::Error,
            &format!(
                "TLC encountered the following error when trying to read the configuration file {}:\nFile not found.",
                config_path.unwrap_or_default()
            ),
        );
        return CONFIG_PARSE_ERROR;
    }
    let start = Instant::now();
    // TLC reads the configuration file before it parses the spec, and reports one it can't parse
    // as it reports a TlaConfigError (`printFailure`).
    let config_text = config_path.and_then(|path| printer.host.read_text(Path::new(&path)));
    let parsed = config_text
        .as_deref()
        .map(|text| parse_config(text, TlcVersion::Master));
    let config = match parsed {
        Some(Ok(config)) => config,
        Some(Err(error)) => {
            let Some(coded) = FrontError::Config(error.message).get_coded(printer.is_tool) else {
                return report_not_native(printer, "a configuration file the front end rejects");
            };
            return print_coded_failure(printer, &coded, start);
        }
        None => return report_not_native(printer, "a configuration file the front end rejects"),
    };
    let mut dumps = TraceDumps::new(
        args,
        &config,
        is_trace_recorded(args, spec_path),
        main_file.map(|main_file| {
            let (directory, _, name) = te_spec::get_files_place(main_file, started);
            format!("{directory}/{name}.bin")
        }),
    );
    let front = match read_front(
        spec_path,
        config_text.as_deref().unwrap_or_default(),
        !args.has("-nowarning"),
        &Files {
            spec: Path::new(spec_path),
            libraries: &java.libraries,
            temporary: java.temporary_directory.as_deref(),
            metadir: args.first("-metadir"),
            jar: java.class_path.as_deref().and_then(get_tools_jar),
            is_174: false,
            root_extendees: &dumps.get_root_extendees(),
        },
        printer.host,
        printer.is_tool,
        seed,
    ) {
        Ok(Read::Model(front)) => front,
        // TLC rejects a temporal formula as it builds its liveness checker, which a simulation
        // builds only as it checks a trace.
        Ok(Read::Failed(failure))
            if simulation.is_some()
                && failure
                    .error
                    .as_ref()
                    .is_some_and(|coded| coded.text.contains("emporal formula")) =>
        {
            return report_not_native(printer, "a simulation of a temporal formula TLC rejects");
        }
        Ok(Read::Failed(failure)) => return print_failed_front(printer, &failure, start),
        Err(reason) => return report_not_native(printer, &reason),
    };
    // Everything the check reads, it has read by now: a host still missing some answers it first.
    if !printer.host.is_complete() {
        return NOT_NATIVE;
    }
    let mut ir = match tla_ir::decode(&front.ir) {
        Ok(ir) => ir,
        Err(error) => {
            return report_not_native(printer, &format!("the engine IR doesn't decode: {error}"));
        }
    };
    // TLCGet("-Dname") reads a system property, which the engine takes for unset.
    if let Some(name) = java
        .properties
        .iter()
        .find(|name| ir.texts.iter().any(|text| **text == format!("-D{name}")))
    {
        return report_not_native(
            printer,
            &format!("TLCGet of the system property {name}, which the command line sets"),
        );
    }
    // TLC looks an ALIAS up among the definitions, the constants and TRUE, FALSE, BOOLEAN and
    // STRING (`SpecProcessor.processSpec`'s `defns`, `Spec.getAliasSpec`). Where the IR has no
    // definition of it, the binary reports it as one TLC doesn't find but where the configuration
    // assigns it as a constant or it names one of the others.
    let is_alias_undefined_unsure = ir.model.alias.as_ref().is_some_and(|alias| {
        let name = &*ir.texts[alias.name as usize];
        alias.definition.is_none()
            && (["TRUE", "FALSE", "BOOLEAN", "STRING"].contains(&name)
                || config
                    .constants
                    .iter()
                    .any(|constant| constant.name == name)
                || config
                    .substitutions
                    .iter()
                    .any(|substitution| substitution.name == name))
    });
    if is_alias_undefined_unsure {
        return report_not_native(printer, "an ALIAS that names a constant");
    }
    // TLC names a postcondition with where its definition's body is written.
    let is_postcondition_unplaced = ir.model.postconditions.iter().any(|postcondition| {
        postcondition.definition.is_none_or(|definition| {
            match &ir.nodes.arena[ir.definitions[definition as usize] as usize].kind {
                tla_ir::NodeKind::Definition(definition) => {
                    ir.nodes.arena[definition.body as usize].range.is_none()
                }
                _ => true,
            }
        })
    });
    if is_postcondition_unplaced {
        return report_not_native(printer, "a POSTCONDITION without a place in the source");
    }
    // TLC rejects the ALIAS as it prints each state, and the POSTCONDITIONs as it is to check
    // them, where one takes arguments or is a definition it computed as it started
    // (`Spec.getAliasSpec`, `getPostConditionSpecs`). The rebuild of a trace reports the ALIAS;
    // the binary declines where it can't tell whether TLC computed one.
    let takes_arguments = |definition: u32| {
        matches!(
            &ir.nodes.arena[ir.definitions[definition as usize] as usize].kind,
            tla_ir::NodeKind::Definition(tla_ir::Definition {
                form: tla_ir::DefinitionForm::Operator(params),
                ..
            }) if !params.is_empty()
        )
    };
    let is_computed_at_startup = |definition: u32| {
        Rebuilder::new(&ir).and_then(|mut rebuilder| rebuilder.is_computed_at_startup(definition))
    };
    let alias_definition = (ir.model.alias.as_ref())
        .and_then(|alias| alias.definition)
        .filter(|&definition| !takes_arguments(definition));
    if alias_definition.is_some_and(|definition| is_computed_at_startup(definition).is_err()) {
        return report_not_native(printer, "an ALIAS TLC may compute as it starts");
    }
    let mut rejected_postcondition = None;
    for postcondition in &ir.model.postconditions {
        let Some(definition) = postcondition.definition else {
            continue;
        };
        let name = &ir.texts[postcondition.name as usize];
        if takes_arguments(definition) {
            rejected_postcondition = Some((
                format!(
                    "TLC requires post condition not to take any argument, but one was given: {name}"
                ),
                code::CONFIG_ID_REQUIRES_NO_ARG,
            ));
            break;
        }
        match is_computed_at_startup(definition) {
            Ok(false) => {}
            Ok(true) => {
                rejected_postcondition = Some((
                    format!("The post condition {name} cannot be a constant."),
                    code::CONFIG_ID_MUST_NOT_BE_CONSTANT,
                ));
                break;
            }
            Err(_) => {
                return report_not_native(printer, "a POSTCONDITION TLC may compute as it starts");
            }
        }
    }
    if let Some(sany) = &front.sany {
        print_sany(printer, sany);
        printer.is_trace_recorded = is_trace_recorded(args, spec_path);
        if is_trace_spec_written(args, spec_path) {
            if args.has("-teSpecOutDir") {
                return report_not_native(printer, "-teSpecOutDir");
            }
            let Some(main_file) = main_file else {
                return report_not_native(
                    printer,
                    "the trace exploration spec of a spec found in a library directory",
                );
            };
            printer.trace_spec = Some(TraceSpec::new(
                main_file,
                started,
                &ir,
                &config,
                &front.defined_names,
                fingerprint_index,
            ));
        }
    } else {
        dumps.leave_out_trace_file();
    }
    // TLC loads the classes of the modules before it computes the constant definitions.
    for message in &front.override_messages {
        print_startup_message(printer, message);
    }
    // TLC seeds its generator with -seed, which an IR tla-front lowers doesn't hold.
    ir.model.random_seed = seed as u64;
    ir.model.fingerprint_index = fingerprint_index;
    if args.has("-deadlock") {
        ir.model.check_deadlock = false;
    }
    // The front end evaluates nothing, so the IR it lowers has none of TLC's actions, which the
    // trace evaluator finds as check.ts does. A model it can't split keeps none, and its traces
    // name no actions natively. The evaluator recurses, so it runs with the search's stack.
    if ir.model.actions.is_empty() {
        let split = on_search_stack(|| tla_trace::add_actions(&ir).ok());
        if let Some(split) = split {
            ir = split;
        }
    }
    if let Some(simulation) = simulation {
        let simulating = Simulating {
            simulation,
            config: &config,
            dumps: &dumps,
            startup_messages: front.startup_messages,
            initial_label: front.initial_label,
            workers,
            is_continued: args.has("-continue"),
            start,
        };
        return check_simulation(printer, &ir, simulating);
    }
    // TLC checks the temporal properties as the search goes, unless -lncheck asks for one check at
    // the end.
    let is_liveness_periodic = !args
        .first("-lncheck")
        .is_some_and(|check| ["final", "seqfinal"].contains(&check.to_lowercase().as_str()));
    let is_dumped = dump.is_some();
    if is_dumped && (ir.model.view.is_some() || ir.model.startup.symmetry.is_some()) {
        return report_not_native(printer, "-dump under SYMMETRY or a VIEW");
    }
    // TLC writes each state again as it adds the state's stuttering step to the behavior graph
    // (`Worker.doNextCheckLiveness`).
    if is_dumped && !ir.model.live_formula.is_empty() {
        return report_not_native(printer, "-dump with temporal properties");
    }
    // Under -continue TLC reports each invariant and action property violated with its trace and
    // goes on. Where it checks more than those, the binary doesn't follow.
    let is_continued = args.has("-continue");
    if is_continued {
        let model = &ir.model;
        let is_built_in = |names: &[&str]| {
            ir.builtins
                .iter()
                .any(|builtin| names.contains(&&*ir.texts[builtin.name as usize]))
        };
        let unfollowed = if !model.live_formula.is_empty() {
            Some("-continue with temporal properties")
        } else if model.view.is_some() || model.startup.symmetry.is_some() {
            Some("-continue under SYMMETRY or a VIEW")
        } else if !model.postconditions.is_empty() {
            Some("-continue with a POSTCONDITION")
        } else if !dumps.is_empty() {
            Some("-continue with -dumpTrace")
        } else if is_built_in(&["Print", "PrintT", "TLCSet"]) {
            // TLC prints what the spec prints as it evaluates, before the violation it then
            // reports, and sets its registers again as it rebuilds each trace (`printTrace`),
            // which the search goes on reading.
            Some("-continue with a spec that prints or sets TLC's registers")
        } else if is_built_in(&[
            "RandomElement",
            "RandomSubset",
            "RandomSetOfSubsets",
            "RandomSubsetSet",
        ]) {
            // TLC fails to recover the traces of a spec that draws at random as it goes on
            // (RandomElement, RandomSubsetNext): "Failed to recover the initial state".
            Some("-continue with random draws")
        } else {
            None
        };
        if let Some(reason) = unfollowed {
            return report_not_native(printer, reason);
        }
    }
    let settings = Settings {
        is_violation_reported: true,
        workers,
        // The search shares its levels and the liveness checker's atoms between as many threads
        // as TLC has workers, and finds what one thread finds. PROVE_IT_WORKERS asks for another
        // number, such as to check that under -workers 1; PROVE_IT_SHARED_LEVEL sets the fewest
        // states a level shares.
        threads: get_number(printer.host, "PROVE_IT_WORKERS")
            .unwrap_or(workers)
            .clamp(1, printer.host.machine().cores),
        minimum_shared_level: get_number(printer.host, "PROVE_IT_SHARED_LEVEL")
            .unwrap_or(MINIMUM_SHARED_LEVEL),
        is_liveness_periodic,
        test_live_check_at: printer
            .host
            .get_variable("PROVE_IT_TEST_LIVE_CHECK_AT")
            .and_then(|at| at.parse().ok()),
        test_memo_entries: get_number(printer.host, "PROVE_IT_TEST_MEMO_ENTRIES"),
        test_progress_at: get_number(printer.host, "PROVE_IT_TEST_PROGRESS_AT"),
        test_evaluations: printer
            .host
            .get_variable("PROVE_IT_TEST_EVALUATIONS")
            .and_then(|evaluations| evaluations.parse().ok()),
        is_dumped,
        is_continued,
        large_region_advice: printer.host.large_region_advice(),
        is_file_system: printer.host.is_file_system(),
        ..Settings::default()
    };
    let threads = settings.threads;
    let (sender, receiver) = mpsc::channel();
    let is_tool = printer.is_tool;
    let is_plain = printer.host.is_plain();
    // How many initial states TLC generated, which TLCGet("stats") reports.
    let mut initial_generated = 0;
    // When the check of the temporal properties part way through the search that found a
    // counterexample started.
    let mut checking = None;
    let mut is_misprinted = false;
    let mut is_periodic_reached = false;
    let mut is_coverage_reached = false;
    let mut is_dump_unwritten = false;
    let mut declined = None;
    let is_periodic = config.periodic.is_some();
    let ir_ref = &ir;
    let (outcome, assumed_printed, dumped) = alongside(
        move || {
            let ir = ir_ref;
            let mut relay = Relay::new(
                sender,
                ir,
                is_tool,
                is_plain,
                workers,
                front.startup_messages,
            );
            relay.is_periodic = is_periodic;
            relay.is_dumped = is_dumped;
            relay.coverage_countdown = coverage::get_countdown(args);
            let outcome = search(ir, &settings, &mut relay);
            (outcome, relay.assumed_printed, relay.dumped)
        },
        || {
            loop {
                // TLC prints each line as it goes, so what waits in the buffer goes out whenever
                // the search has nothing more to say yet.
                let event = match receiver.try_recv() {
                    Ok(event) => event,
                    Err(_) => {
                        printer.flush();
                        let Ok(event) = receiver.recv() else {
                            break;
                        };
                        event
                    }
                };
                match event {
                    Event::InitialStatesStarted => printer.print(
                        code::COMPUTING_INIT,
                        Level::None,
                        "Computing initial states...",
                    ),
                    Event::InitialStatesProgress(count) => printer.print(
                        code::COMPUTING_INIT_PROGRESS,
                        Level::None,
                        &format!("Computed {count} initial states..."),
                    ),
                    Event::InitialStates(generated, distinct) => {
                        initial_generated = generated;
                        print_initial_states(printer, generated, distinct)
                    }
                    Event::Progress(generated, distinct, queued, depth) => {
                        let statistics = Statistics {
                            generated,
                            distinct,
                            queued,
                            depth,
                        };
                        print_progress(printer, &statistics, Some(start));
                        printer.flush();
                    }
                    Event::LivenessStarted(branches, states) => {
                        checking = Some(print_liveness_check(printer, branches, states, "current"));
                    }
                    Event::LivenessFinished => {
                        if let Some(checking) = checking.take() {
                            print_liveness_finished(printer, checking);
                        }
                    }
                    Event::Print(Some(text)) => printer.printed(&text),
                    Event::StartupMessage(message) => print_startup_message(printer, &message),
                    Event::SymmetrySetsTooSmall(names) => print_small_sets(printer, &names),
                    // Nothing more this run prints can be right, so it prints nothing more, and the
                    // search, which the relay cancels, ends with the events it sends unread.
                    Event::Print(None) => {
                        is_misprinted = true;
                        break;
                    }
                    Event::Periodic => {
                        is_periodic_reached = true;
                        break;
                    }
                    Event::CoverageReported => {
                        is_coverage_reached = true;
                        break;
                    }
                    Event::SimulationProgress(..) => {}
                    Event::Continued(report) => print_continued(printer, &report),
                    Event::Declined(reason) => {
                        declined = Some(reason);
                        break;
                    }
                    Event::Dumped(text) => {
                        let path = Path::new(dump.as_deref().unwrap_or_default());
                        is_dump_unwritten |= !printer.host.write_file(path, text.as_bytes(), true);
                    }
                }
            }
            drop(receiver);
        },
    );
    if let Some(reason) = declined {
        return report_not_native(printer, &reason);
    }
    if is_dump_unwritten {
        return report_not_native(printer, "-dump into a file it can't write");
    }
    if is_periodic_reached {
        return report_not_native(
            printer,
            "_PERIODIC, which TLC evaluates as it prints its progress",
        );
    }
    if is_coverage_reached {
        return report_not_native(
            printer,
            "coverage TLC reports part way through the search is timing-dependent",
        );
    }
    if is_misprinted {
        return report_not_native(
            printer,
            "printing a value whose text depends on how TLC built it",
        );
    }
    // A search that found no state hands none over, and one that stopped computing its initial
    // states hands over none of those it found.
    let is_stateless = matches!(
        outcome,
        SearchOutcome::Declined(_)
            | SearchOutcome::AssumptionViolated { .. }
            | SearchOutcome::ConfigError { .. }
            | SearchOutcome::AssumptionFailed { .. }
    );
    // Under -continue TLC reports an error or a deadlock otherwise than it does without it, with
    // other traces and exit codes, which the binary doesn't follow.
    if is_continued
        && !matches!(
            outcome,
            SearchOutcome::Complete { .. } | SearchOutcome::Declined(_)
        )
    {
        return report_not_native(printer, "-continue to a search that stops");
    }
    // Where an invariant fails to evaluate, TLC expands the state again to print the call stack,
    // and writes the new states it finds then too.
    let is_replayed = matches!(
        &outcome,
        SearchOutcome::Stopped {
            violation: Some(violation),
            ..
        } if !violation.fingerprints.is_empty()
    );
    match dumped {
        Some(Err(reason)) => return report_not_native(printer, reason),
        Some(Ok(())) if is_replayed => {
            return report_not_native(printer, "-dump of states TLC finds as it replays a step");
        }
        None if is_dumped && !is_stateless => {
            return report_not_native(
                printer,
                "-dump of a search stopped computing its initial states",
            );
        }
        _ => {}
    }
    if args.has("-coverage") {
        let directory = Path::new(spec_path).parent().unwrap_or(Path::new("."));
        let directories: Vec<&Path> = std::iter::once(directory)
            .chain(java.libraries.iter().map(Path::new))
            .collect();
        match coverage::compute(&ir, &outcome, printer.host, &directories, fingerprint_index) {
            Ok(messages) => printer.coverage = Some(messages),
            Err(why) => return report_not_native(printer, &why),
        }
        // TLC ends a report of a run of more than 5 minutes with 2777 rather than 2202, by its own
        // clock, which a native run past the cut can't rule out (design/cli.md, "-coverage").
        let cut = printer
            .host
            .get_variable("PROVE_IT_TEST_COVERAGE_CUT")
            .and_then(|seconds| seconds.parse().ok())
            .map_or(coverage::CUT, Duration::from_secs);
        if printer
            .coverage
            .as_ref()
            .is_some_and(|messages| !messages.is_empty())
            && start.elapsed() > cut
        {
            return report_not_native(
                printer,
                "coverage of a run TLC may take more than 5 minutes over, which ends its report otherwise",
            );
        }
    }
    let (counts, fingerprints) = match outcome {
        SearchOutcome::Complete {
            counts,
            fingerprints,
            liveness,
            violation,
            possible,
            registers,
            ..
        } => {
            // Once the search completes, TLC reports a _POSSIBLE predicate the search never
            // witnessed, and then checks the postconditions.
            if possible.iter().any(|&count| count <= 0) {
                return report_not_native(
                    printer,
                    "a _POSSIBLE predicate the search didn't witness",
                );
            }
            // TLC fails on a POSTCONDITION it rejects as it is to check them, with an unexpected
            // exception, and then reports the statistics (`ModelChecker.modelCheck`).
            if let Some((text, code)) = &rejected_postcondition {
                if liveness.is_some() || !config.possible.is_empty() || is_continued {
                    return report_not_native(
                        printer,
                        "a POSTCONDITION TLC rejects after temporal properties, _POSSIBLE or \
                         under -continue",
                    );
                }
                let message = if printer.is_tool {
                    format!("@!@!@STARTMSG {code}:0 @!@!@\n{text}\n@!@!@ENDMSG {code} @!@!@")
                } else {
                    text.clone()
                };
                printer.print(
                    code::GENERAL,
                    Level::Error,
                    &format!("{UNEXPECTED_EXCEPTION}{message}"),
                );
                let statistics = Statistics {
                    generated: counts.generated,
                    distinct: counts.distinct,
                    queued: counts.queued,
                    depth: counts.depth,
                };
                print_statistics(printer, &statistics, start);
                print_finished(printer, start);
                return crate::failure::ERROR;
            }
            if let Some(liveness) = liveness {
                // TLC stops at a node that accepts every behavior as it searches, so it checks
                // nothing once the search is done.
                let is_lasso = matches!(liveness.verdict, Verdict::Lasso { .. });
                let is_accepted = matches!(liveness.verdict, Verdict::Accepted { .. });
                if let Some(violation) = violation.filter(|_| is_lasso || is_accepted) {
                    let run = postcondition_run(
                        &ir,
                        Some(&possible),
                        &Statistics {
                            generated: counts.generated,
                            distinct: counts.distinct,
                            queued: counts.queued,
                            depth: counts.depth,
                        },
                        counts.initial_generated,
                        start,
                    );
                    return print_violation(
                        printer,
                        &ir,
                        &config,
                        &violation,
                        is_lasso.then_some((&liveness, checking)),
                        TraceChecks {
                            dumps: &dumps,
                            run: Some(&run),
                        },
                        start,
                    )
                    .unwrap_or_else(|why| {
                        report_not_native(
                            printer,
                            &format!("a temporal property's counterexample: {why}"),
                        )
                    });
                }
                let why = match &liveness.verdict {
                    Verdict::Holds => None,
                    Verdict::Lasso { .. }
                        if ir.model.startup.symmetry.is_some() || ir.model.view.is_some() =>
                    {
                        Some(
                            "a temporal property's counterexample: under SYMMETRY or a VIEW".into(),
                        )
                    }
                    Verdict::Lasso { .. } => Some(
                        "a temporal property's counterexample: a lasso the engine doesn't hand over".into(),
                    ),
                    Verdict::Accepted { .. } => {
                        Some("a temporal property's counterexample: an accepting node".into())
                    }
                    Verdict::Declined(declined) => {
                        Some(format!("the liveness checker declined: {}", declined.0))
                    }
                    Verdict::Unexpanded => Some(format!(
                        "the liveness checker declined: {}",
                        tla_live::UNEXPANDED
                    )),
                };
                if let Some(why) = why {
                    return report_not_native(printer, &why);
                }
                let statistics = Statistics {
                    generated: counts.generated,
                    distinct: counts.distinct,
                    queued: counts.queued,
                    depth: counts.depth,
                };
                let Some(branches) = liveness.branches else {
                    return report_not_native(
                        printer,
                        "temporal properties of branches not counted",
                    );
                };
                let checking = print_liveness_started(printer, &statistics, branches);
                print_liveness_finished(printer, checking);
            }
            if !ir.model.postconditions.is_empty() {
                let statistics = Statistics {
                    generated: counts.generated,
                    distinct: counts.distinct,
                    queued: counts.queued,
                    depth: counts.depth,
                };
                let run = postcondition_run(
                    &ir,
                    Some(&possible),
                    &statistics,
                    counts.initial_generated,
                    start,
                );
                let checked = match check_postconditions(&ir, &run, registers.as_deref()) {
                    Ok(checked) => checked,
                    Err(reason) => return report_not_native(printer, &reason),
                };
                // What the postconditions print comes as TLC evaluates them; TLC reports one that
                // doesn't hold in place of the success, with the statistics.
                for line in &checked.printed {
                    printer.printed(line);
                }
                if checked.failure.is_some() {
                    printer.outcome.status = Some("postcondition-violation");
                    print_postcondition_failure(printer, &ir, Some(&checked));
                    print_statistics(printer, &statistics, start);
                    print_finished(printer, start);
                    return ASSUMPTION_VIOLATION;
                }
            }
            (counts, fingerprints)
        }
        SearchOutcome::Declined(reason) => {
            return report_not_native(printer, &format!("the engine declined: {reason}"));
        }
        SearchOutcome::AssumptionFailed { position } => {
            return print_assumption_failure(
                printer,
                &ir,
                position,
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
        // TLC rejects the value of a constant definition the configuration names as it reads
        // the configuration.
        SearchOutcome::ConfigError { message } => {
            return match FrontError::Config(message).get_coded(printer.is_tool) {
                Some(coded) => print_coded_failure(printer, &coded, start),
                None => report_not_native(printer, "a configuration error without TLC's code"),
            };
        }
        // TLC reports a false assumption with no statistics, since it hasn't searched.
        SearchOutcome::AssumptionViolated { name } => {
            printer.outcome.status = Some("assumption-violation");
            printer.report(
                code::ASSUMPTION_FALSE,
                &format!("Assumption {name} is false."),
            );
            print_finished(printer, start);
            return ASSUMPTION_VIOLATION;
        }
        SearchOutcome::Stopped {
            violation: Some(violation),
            reason,
            ..
        } => {
            let printed = match violation.kind {
                // TLC's worker fails on a POSTCONDITION it rejects as it is to check it on the
                // trace of a safety violation, after printing the trace, and reports nothing more
                // (`Worker.doPostCondition`). Elsewhere the binary doesn't follow TLC.
                // TLC rejects the configuration's postconditions as it collects them all, before
                // it evaluates any, so -dumpTrace's write nothing (`Spec.getPostConditionSpecs`).
                _ if rejected_postcondition.is_some() && !dumps.is_empty() => {
                    Err("-dumpTrace with a POSTCONDITION TLC rejects".to_string())
                }
                _ if rejected_postcondition.is_some()
                    && (!config.possible.is_empty()
                        || !matches!(
                            violation.kind,
                            ViolationKind::Invariant(_)
                                | ViolationKind::ActionProperty(_)
                                | ViolationKind::Deadlock { .. }
                        )) =>
                {
                    Err("a POSTCONDITION TLC rejects".to_string())
                }
                // TLC stops with no statistics, before it would search, as at an error the
                // library throws, so the outcome has no status.
                ViolationKind::NoNextState => {
                    printer.print(
                        code::NO_NEXT_ACTION,
                        Level::Error,
                        "No next state actions defined to generate successor states from.",
                    );
                    print_finished(printer, start);
                    Ok(NO_NEXT_ACTION)
                }
                // TLC's report of a failure evaluating the model, which it replays. It prints the
                // trace through the ALIAS, which the printing follows for a failure in the
                // next-state relation or an invariant.
                ViolationKind::Error { .. } if !config.possible.is_empty() => {
                    Err("a failure with a _POSSIBLE predicate".to_string())
                }
                // After a failure TLC checks the postconditions only as its worker goes on to
                // check the state for deadlock, having generated no successor of it
                // (`Worker.run`): which the search's counts say only of the first state expanded.
                // TLC reports a failure among the initial states with the state as it is, and
                // ends there, with no postcondition checked (`ModelChecker#doInit`). With
                // -dumpTrace TLC's worker may check them on a trace it fails to find again.
                ViolationKind::Error { site }
                    if !is_initial_site(site)
                        && (dumps.has_command_line_dumps()
                            || !config.postconditions.is_empty()
                                && match site {
                                    ErrorSite::Invariant(_) => false,
                                    ErrorSite::Next => {
                                        ir.model.check_deadlock
                                            && violation.counts.generated != initial_generated
                                    }
                                    _ => true,
                                }) =>
                {
                    Err("a failure with a POSTCONDITION or -dumpTrace".to_string())
                }
                ViolationKind::Error { site }
                    if config.alias.is_some()
                        && !is_initial_site(site)
                        && !matches!(
                            site,
                            ErrorSite::Next | ErrorSite::NextAtom { .. } | ErrorSite::Invariant(_)
                        ) =>
                {
                    Err("a failure outside the next-state relation with an ALIAS".to_string())
                }
                ViolationKind::Error { site } => {
                    let counts = &violation.counts;
                    let stop = ErrorStop {
                        reason: &reason,
                        store: &violation.store,
                        states: violation.states.iter().map(Vec::as_slice).collect(),
                        actions: violation.labels.clone(),
                        site: match site {
                            ErrorSite::Init => Site::Init,
                            ErrorSite::Next => Site::Next,
                            ErrorSite::Invariant(position) => Site::Invariant(position),
                            ErrorSite::InitialConstraint(position) => {
                                Site::InitialConstraint(position)
                            }
                            ErrorSite::InitialInvariant(position) => {
                                Site::InitialInvariant(position)
                            }
                            ErrorSite::InitialPredicate(position) => {
                                Site::InitialPredicate(position)
                            }
                            ErrorSite::Atom { atom, is_extra } => Site::Atom { atom, is_extra },
                            ErrorSite::NextAtom { atom, is_extra } => {
                                Site::NextAtom { atom, is_extra }
                            }
                            ErrorSite::InitialAtom { atom, replayed } => {
                                Site::InitialAtom { atom, replayed }
                            }
                        },
                        statistics: Statistics {
                            generated: counts.generated,
                            distinct: counts.distinct,
                            queued: counts.queued,
                            depth: counts.depth,
                        },
                        out_degrees: &counts.out_degrees,
                        fingerprints: &violation.fingerprints,
                        replayed: (!is_initial_site(site)
                            && (config.alias.is_some() || !config.postconditions.is_empty()))
                        .then_some(&violation),
                        is_aliased: config.alias.is_some() && !is_initial_site(site),
                        postconditions: (!config.postconditions.is_empty()
                            && site == ErrorSite::Next
                            && ir.model.check_deadlock)
                            .then(|| {
                                postcondition_run(
                                    &ir,
                                    Some(&violation.possible),
                                    &Statistics {
                                        generated: counts.generated,
                                        distinct: counts.distinct,
                                        queued: counts.queued,
                                        depth: counts.depth,
                                    },
                                    initial_generated,
                                    start,
                                )
                            }),
                    };
                    print_failure(printer, &ir, &stop, start)
                }
                _ => {
                    let counts = &violation.counts;
                    let statistics = Statistics {
                        generated: counts.generated,
                        distinct: counts.distinct,
                        queued: counts.queued,
                        depth: counts.depth,
                    };
                    let run = postcondition_run(
                        &ir,
                        Some(&violation.possible),
                        &statistics,
                        initial_generated,
                        start,
                    );
                    print_violation(
                        printer,
                        &ir,
                        &config,
                        &violation,
                        None,
                        TraceChecks {
                            dumps: &dumps,
                            run: rejected_postcondition.is_none().then_some(&run),
                        },
                        start,
                    )
                    .map_err(str::to_string)
                }
            };
            return printed.unwrap_or_else(|why| {
                report_not_native(printer, &format!("the engine stopped: {reason}: {why}"))
            });
        }
        SearchOutcome::Stopped { reason, .. } => {
            return report_not_native(printer, &format!("the engine stopped: {reason}"));
        }
        SearchOutcome::Invariant(reason) => {
            return report_not_native(printer, &format!("an engine invariant failed: {reason}"));
        }
    };
    let optimistic = optimistic_probability(counts.distinct, counts.generated);
    let actual = fingerprint_distance(counts.distinct, counts.generated, &fingerprints, threads)
        .map(|distance| {
            format!(
                "\n  based on the actual fingerprints:  val = {}",
                format_probability(actual_probability(distance))
            )
        })
        .unwrap_or_default();
    printer.outcome.status = Some("success");
    printer.print(
        code::SUCCESS,
        Level::None,
        &format!(
            "Model checking completed. No error has been found.\n  Estimates of the probability that TLC did not check all reachable states\n  because two distinct states had the same fingerprint:\n  calculated (optimistic):  val = {}{actual}",
            format_probability(optimistic)
        ),
    );
    let statistics = Statistics {
        generated: counts.generated,
        distinct: counts.distinct,
        queued: counts.queued,
        depth: counts.depth,
    };
    print_statistics(printer, &statistics, start);
    if let Some(summary) = out_degree_summary(&counts.out_degrees) {
        printer.print(code::STATE_GRAPH_OUTDEGREE, Level::None, &summary);
    }
    print_finished(printer, start);
    SUCCESS
}

/// Once the search is complete, TLC reports how far it got, then checks the temporal properties
/// on the complete state graph (`liveness-started`): returns when it started.
fn print_liveness_started(
    printer: &mut Printer,
    statistics: &Statistics,
    branches: usize,
) -> Instant {
    print_progress(printer, statistics, None);
    let branches = branches as u64;
    // Each branch's behavior graph has every state once the search is complete.
    print_liveness_check(
        printer,
        branches,
        branches * statistics.distinct,
        "complete",
    )
}

/// TLC checks the temporal properties of its branches on behavior graphs of `states` states in
/// all, summed over the branches, of the complete or the current state space: returns when it
/// started.
fn print_liveness_check(printer: &mut Printer, branches: u64, states: u64, space: &str) -> Instant {
    let checking = Instant::now();
    let branch_text = if branches > 1 {
        format!("{branches} branches of ")
    } else {
        String::new()
    };
    printer.print(
        code::CHECKING_TEMPORAL,
        Level::None,
        &format!(
            "Checking {branch_text}temporal properties for the {space} state space with {states} total distinct states at ({})",
            printer.date()
        ),
    );
    checking
}

/// TLC has checked the temporal properties (`liveness-finished`).
fn print_liveness_finished(printer: &mut Printer, checking: Instant) {
    printer.print(
        code::CHECKING_TEMPORAL_END,
        Level::None,
        &format!(
            "Finished checking temporal properties in {} at {}",
            format_duration(checking.elapsed().as_millis()),
            printer.date()
        ),
    );
}

/// After a search, TLC prints how many states it found and how deep it went, after the progress
/// with -tool.
pub(crate) fn print_statistics(printer: &mut Printer, statistics: &Statistics, start: Instant) {
    printer.outcome.counts = statistics.counts();
    if let Some(messages) = printer.coverage.take() {
        coverage::print(printer, &messages);
    }
    if printer.is_tool {
        print_progress(printer, statistics, Some(start));
    }
    printer.print(
        code::STATS,
        Level::None,
        &format!(
            "{} states generated, {} distinct states found, {} states left on queue.",
            statistics.generated, statistics.distinct, statistics.queued
        ),
    );
    printer.print(
        code::SEARCH_DEPTH,
        Level::None,
        &format!(
            "The depth of the complete state graph search is {}.",
            statistics.depth
        ),
    );
}

const BOOK: &str = "(compare Chapter 8, page 87ff of Specifying Systems at https://lamport.azurewebsites.net/tla/book.html).";
const NO_SPECIFICATION_WARNING: &str = "The stuttering counterexample above may be caused by the absence of a behavior specification (SPECIFICATION). Only INIT and NEXT have been provided, so TLC permits infinite stuttering. To rule out such counterexamples, use SPECIFICATION Spec, with Spec asserting a suitable fairness constraint (compare Chapter 8, page 87ff of Specifying Systems at https://lamport.azurewebsites.net/tla/book.html).";

/// Why `print_violation` can't print a violation yet, where the IR doesn't name what it reports.
const NOT_IN_IR: &str = "a name the IR doesn't carry";

// Whether a failure is among the initial states, before TLC has taken a step.
fn is_initial_site(site: ErrorSite) -> bool {
    matches!(
        site,
        ErrorSite::Init
            | ErrorSite::InitialConstraint(_)
            | ErrorSite::InitialInvariant(_)
            | ErrorSite::InitialPredicate(_)
            | ErrorSite::InitialAtom { .. }
    )
}

/// Prints a violation the engine stopped at, or the lasso the liveness checker found, as
/// `printViolation` in `src/cli/tlc.ts` does, and returns the exit code, or why it can't print
/// it yet.
pub(crate) fn print_violation(
    printer: &mut Printer,
    ir: &tla_ir::Ir,
    config: &ModelConfig,
    violation: &Violation,
    liveness: Option<(&Liveness, Option<Instant>)>,
    checks: TraceChecks,
    start: Instant,
) -> Result<i32, &'static str> {
    let postconditions = checks.run;
    let started = liveness.and_then(|(_, started)| started);
    let liveness = liveness.map(|(liveness, _)| liveness);
    // TLC reports a _POSSIBLE predicate the search didn't witness before it stopped, which the
    // printing doesn't follow yet, before it checks the postconditions on the trace.
    let possible = postconditions.map_or(&[][..], |run| &run.possible[..]);
    if possible.len() != ir.model.possible.len() || possible.iter().any(|(_, count)| *count <= 0) {
        return Err("a _POSSIBLE predicate");
    }
    // TLC prints a trace once it has rebuilt all of it, and a state that the evaluator can't
    // rebuild as TLC built it keeps the run not native.
    let checked = postconditions.filter(|_| !ir.model.postconditions.is_empty());
    let checks = TraceChecks {
        run: checked,
        ..checks
    };
    let trace = match rebuild_trace(
        ir,
        violation,
        checks,
        printer.is_tool,
        printer.host.is_plain(),
    ) {
        Ok(trace) => trace,
        Err(reason) => return Ok(report_not_native(printer, &reason)),
    };
    if !is_writable(printer.host, &trace.dumped) {
        return Err("-dumpTrace into a directory that doesn't exist");
    }
    let dumped_lines: Vec<String> = trace
        .dumped
        .iter()
        .filter(|file| file.is_printed)
        .map(|file| file.get_line())
        .collect();
    // TLC adds a deadlocked state to the behavior graphs after it reports the deadlock, and
    // reports the tableau node that accepts every behavior it reaches next.
    let accepted = match &violation.kind {
        ViolationKind::Deadlock {
            accepted: Some(accepted),
        } => {
            if checked.is_some() || !checks.dumps.is_empty() {
                return Err("a postcondition after a deadlock that violates a temporal property");
            }
            match rebuild_accepted(
                ir,
                violation,
                accepted,
                printer.is_tool,
                printer.host.is_plain(),
            ) {
                Ok(trace) => Some((trace, properties_headline(ir, &accepted.violated))),
                Err(reason) => return Ok(report_not_native(printer, &reason)),
            }
        }
        _ => None,
    };
    let model = &ir.model;
    let (code, text, exit_code, status) = match violation.kind {
        ViolationKind::InitialInvariant(owner) => (
            code::INVARIANT_VIOLATED_INITIAL,
            format!(
                "Invariant {} is violated by the initial state:",
                invariant_name(ir, owner)?
            ),
            SAFETY_VIOLATION,
            "invariant-violation",
        ),
        ViolationKind::InitialPredicate(position) => (
            code::PROPERTY_VIOLATED_INITIAL,
            format!(
                "Property {} is violated by the initial state:",
                ir.texts[*model
                    .initial_predicate_names
                    .get(position)
                    .ok_or(NOT_IN_IR)? as usize]
            ),
            LIVENESS_VIOLATION,
            "liveness-violation",
        ),
        ViolationKind::Invariant(owner) => (
            code::INVARIANT_VIOLATED_BEHAVIOR,
            format!("Invariant {} is violated.", invariant_name(ir, owner)?),
            SAFETY_VIOLATION,
            "invariant-violation",
        ),
        ViolationKind::Deadlock { .. } => (
            code::DEADLOCK_REACHED,
            "Deadlock reached.".into(),
            DEADLOCK,
            "deadlock",
        ),
        ViolationKind::ActionProperty(position) => (
            code::ACTION_PROPERTY_VIOLATED_BEHAVIOR,
            action_property_headline(ir, position)?,
            LIVENESS_VIOLATION,
            "liveness-violation",
        ),
        ViolationKind::NoNextState | ViolationKind::Error { .. } => return Err(NOT_IN_IR),
        // Under SYMMETRY or a VIEW, TLC names the properties the lasso it rebuilt violates.
        ViolationKind::Lasso { .. } => (
            code::TEMPORAL_PROPERTY_VIOLATED,
            match &trace.violated {
                Some(violated) => properties_headline(ir, violated),
                None => temporal_headline(ir, liveness.ok_or(NOT_IN_IR)?),
            }
            .ok_or(NOT_IN_IR)?,
            LIVENESS_VIOLATION,
            "liveness-violation",
        ),
        // A tableau node that accepts every behavior: TLC reports it as it does a safety
        // violation.
        ViolationKind::Accepted { ref violated } => (
            code::TEMPORAL_PROPERTY_VIOLATED,
            properties_headline(ir, violated).ok_or(NOT_IN_IR)?,
            SAFETY_VIOLATION,
            "property-violation",
        ),
    };
    let is_counterexample = matches!(
        violation.kind,
        ViolationKind::Lasso { .. } | ViolationKind::Accepted { .. }
    );
    let lasso = match violation.kind {
        ViolationKind::Lasso {
            loop_start,
            loop_label,
            ..
        } => {
            // TLC ends a lasso whose last state is the cycle's first as a stuttering one: it
            // prints every state, then finds the last state's fingerprint the cycle state's
            // (`LiveWorker.printTrace`).
            let is_stuttering = loop_start + 1 == violation.states.len()
                || violation.states.last() == violation.states.get(loop_start);
            // TLC warns of a stuttering counterexample where the solution constrains the cycle,
            // and prints what the spec prints as it finds the step back into the cycle.
            let Verdict::Lasso {
                is_cycle_constrained,
                ..
            } = liveness.ok_or(NOT_IN_IR)?.verdict
            else {
                return Err(NOT_IN_IR);
            };
            let is_printing = ir
                .builtins
                .iter()
                .any(|builtin| matches!(&*ir.texts[builtin.name as usize], "Print" | "PrintT"));
            let is_warned = is_stuttering && is_cycle_constrained;
            if !is_stuttering && is_printing {
                return Err("a step back into the cycle of a spec that prints");
            }
            // TLC labels the step back into the cycle (`printBackToState`), but a stuttering one.
            let label = match loop_label.or(trace.loop_action) {
                Some(action) => Some(action_label(ir, action)?),
                None if is_stuttering => None,
                None => return Err("a step back into the cycle whose action the trace lacks"),
            };
            Some((loop_start, is_stuttering, label, is_warned))
        }
        _ => None,
    };
    let labels = trace_labels(ir, &trace)?;
    let accepted = match accepted {
        Some((accepted, headline)) => {
            let labels = trace_labels(ir, &accepted)?;
            Some((accepted, headline.ok_or(NOT_IN_IR)?, labels))
        }
        None => None,
    };
    let counts = &violation.counts;
    let statistics = Statistics {
        generated: counts.generated,
        distinct: counts.distinct,
        queued: counts.queued,
        depth: counts.depth,
    };
    printer.outcome.status = Some(status);
    // TLC prints the initial state that violates an invariant or a property in the same message,
    // and no statistics, since it checks the initial states before it searches.
    if let ViolationKind::InitialInvariant(_) | ViolationKind::InitialPredicate(_) = violation.kind
    {
        // TLC checks the postconditions then, with the counts of the initial states it found,
        // which the binary doesn't follow.
        if !ir.model.postconditions.is_empty() {
            return Err("a POSTCONDITION after an initial state's violation");
        }
        let state = trace.states.into_iter().next().ok_or(NOT_IN_IR)?;
        printer.print(
            code,
            Level::Error,
            &format!("{text}\n{}", format_variables(&state.variables)),
        );
        if !write(printer.host, &trace.dumped) {
            return Ok(report_not_native(
                printer,
                "-dumpTrace into a file it can't write",
            ));
        }
        printer.record(Reported {
            code,
            headline: text,
            states: vec![ReportedState {
                label: "Initial predicate".into(),
                variables: state.variables,
            }],
            loop_start: None,
        });
        for line in &dumped_lines {
            printer.line(line);
        }
        print_finished(printer, start);
        return Ok(exit_code);
    }
    let lasso_printed = match &violation.kind {
        ViolationKind::Lasso { printed, .. } => printed
            .iter()
            .map(|prints| format_printed(&violation.store, prints))
            .collect::<Option<Vec<_>>>()
            .ok_or("printing a value whose text depends on how TLC built it")?,
        _ => Vec::new(),
    };
    // A check part way through the search reported its start as it began.
    let checking = match liveness {
        Some(liveness) => Some(match started {
            Some(started) => started,
            None => print_liveness_started(
                printer,
                &statistics,
                liveness
                    .branches
                    .ok_or("temporal properties of branches not counted")?,
            ),
        }),
        None => None,
    };
    // What the spec printed as TLC rebuilt the trace: the first state's after the headline, each
    // later state's before it, and the rebuild after the trace. TLC rebuilds a counterexample
    // before it reports it, all of it as it recovers the first state (`printViolation`).
    let first_output = trace.states[0].output.iter();
    let (heading_code, heading) = if is_counterexample {
        for line in first_output.clone().chain(&trace.trace_output) {
            printer.line(line);
        }
        // What the atoms print as TLC finds the properties the lasso it rebuilt violates.
        for line in &lasso_printed {
            printer.line(line);
        }
        printer.report(code, &text);
        (
            code::COUNTER_EXAMPLE,
            "The following behavior constitutes a counter-example:\n",
        )
    } else {
        printer.report(code, &text);
        for line in first_output {
            printer.line(line);
        }
        (
            code::BEHAVIOR_UP_TO_THIS_POINT,
            "The behavior up to this point is:",
        )
    };
    printer.print(heading_code, Level::Error, heading);
    print_states(printer, &trace.states, &labels);
    // -dumpTrace's postconditions write their files as TLC checks them.
    if !write(printer.host, &trace.dumped) {
        return Ok(report_not_native(
            printer,
            "-dumpTrace into a file it can't write",
        ));
    }
    if let (Some(reported), Some((loop_start, ..))) = (printer.outcome.violations.last_mut(), lasso)
    {
        reported.loop_start = Some(loop_start);
    }
    // TLC rebuilds a violation's trace again for the counterexample the postconditions read,
    // so what that prints comes before what they print, -dumpTrace's first. TLC checks them on a
    // lasso once it has printed where the lasso closes (`LiveWorker.printTrace`).
    let postcondition_output = dumped_lines.iter().chain(
        trace
            .postconditions
            .iter()
            .flat_map(|checked| &checked.printed),
    );
    if lasso.is_none() && is_counterexample {
        for line in postcondition_output.clone() {
            printer.line(line);
        }
    }
    match lasso {
        None if is_counterexample => {}
        None => {
            for line in trace
                .trace_output
                .iter()
                .chain(postcondition_output.clone())
            {
                printer.line(line);
            }
        }
        Some((loop_start, true, _, _)) => {
            printer.print(
                code::STATE_PRINT_3,
                Level::State,
                &format!("{}: Stuttering", loop_start + 2),
            );
            printer.recorded_trace.record_stuttering();
        }
        Some((loop_start, false, label, _)) => {
            let label = format!(": <{}>\n", label.unwrap_or_default());
            let is_tool = printer.is_tool;
            printer
                .recorded_trace
                .record_back_to_state(loop_start + 1, is_tool);
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
    // TLC's Liveness#printStutteringCounterExampleWarning: without a SPECIFICATION, a warning
    // that names none; with one whose definition has no temporal conjunct, where the formula the
    // checker solves is the negated properties alone, one that names where it's defined.
    if lasso.is_some_and(|lasso| lasso.3) {
        match &config.specification {
            None => printer.print(
                code::NO_SPECIFICATION_BUT_PROPERTY,
                Level::Warning,
                NO_SPECIFICATION_WARNING,
            ),
            Some(name) => {
                let is_fair = matches!(model.live_formula.first(), Some(tla_ir::LiveTerm::And(_)));
                if let Some(range) = model.specification.filter(|_| !is_fair) {
                    let range = format!(
                        "line {}, col {} to line {}, col {} of module {}",
                        range.start_line,
                        range.start_column,
                        range.end_line,
                        range.end_column,
                        ir.texts[range.module as usize]
                    );
                    printer.print(
                        code::NO_FAIRNESS_BUT_PROPERTY,
                        Level::Warning,
                        &format!(
                            "The stuttering counterexample above may be caused by the absence of a fairness constraint in the behavior specification {name} defined at {range}. To rule out such counterexamples, conjoin a suitable fairness constraint to {name} {BOOK}"
                        ),
                    );
                }
            }
        }
    }
    if lasso.is_some() {
        for line in postcondition_output {
            printer.line(line);
        }
    }
    if let Some((accepted, headline, labels)) = accepted {
        for line in accepted.states[0]
            .output
            .iter()
            .chain(&accepted.trace_output)
        {
            printer.line(line);
        }
        printer.report(code::TEMPORAL_PROPERTY_VIOLATED, &headline);
        printer.print(
            code::COUNTER_EXAMPLE,
            Level::Error,
            "The following behavior constitutes a counter-example:\n",
        );
        print_states(printer, &accepted.states, &labels);
    }
    print_postcondition_failure(printer, ir, trace.postconditions.as_ref());
    if let Some(checking) = checking {
        print_liveness_finished(printer, checking);
    }
    print_statistics(printer, &statistics, start);
    print_finished(printer, start);
    Ok(exit_code)
}

// A trace's states, each after what the spec printed as TLC rebuilt it.
// How TLC names an invariant: an owner past the configuration's invariants is a property checked
// as one.
fn invariant_name(ir: &tla_ir::Ir, owner: usize) -> Result<&str, &'static str> {
    let model = &ir.model;
    let name = match owner.checked_sub(model.invariants.len()) {
        None => model.invariants[owner].root.name,
        Some(property) => *model
            .property_invariant_names
            .get(property)
            .ok_or(NOT_IN_IR)?,
    };
    Ok(&ir.texts[name as usize])
}

// TLC's report of a step that violates the action property at this position.
fn action_property_headline(ir: &tla_ir::Ir, position: usize) -> Result<String, &'static str> {
    let property = ir.model.action_properties.get(position).ok_or(NOT_IN_IR)?;
    Ok(format!(
        "Action property {} is violated.",
        ir.texts[property.name as usize]
    ))
}

fn action_label(ir: &tla_ir::Ir, action: u32) -> Result<&str, &'static str> {
    let action = ir.model.actions.get(action as usize).ok_or(NOT_IN_IR)?;
    Ok(&ir.texts[action.label as usize])
}

// TLC labels each step with the action it finds taking it as it rebuilds the trace.
fn trace_labels<'i>(
    ir: &'i tla_ir::Ir,
    trace: &PrintedTrace,
) -> Result<Vec<&'i str>, &'static str> {
    let mut labels = vec!["Initial predicate"];
    for state in trace.states.iter().skip(1) {
        let action = state
            .action
            .ok_or("a step whose action the rebuilt trace lacks")?;
        labels.push(action_label(ir, action)?);
    }
    Ok(labels)
}

// A violation under -continue as TLC prints it, without the statistics that end a stop: an
// initial state in the headline's message, any other with its trace.
fn print_continued(printer: &mut Printer, report: &ContinuedReport) {
    let trace = &report.trace;
    if report.is_initial {
        let variables = trace
            .states
            .first()
            .map_or_else(Vec::new, |state| state.variables.clone());
        printer.print(
            report.code,
            Level::Error,
            &format!("{}\n{}", report.headline, format_variables(&variables)),
        );
        printer.record(Reported {
            code: report.code,
            headline: report.headline.clone(),
            states: vec![ReportedState {
                label: "Initial predicate".into(),
                variables,
            }],
            loop_start: None,
        });
        return;
    }
    printer.report(report.code, &report.headline);
    for line in trace
        .states
        .first()
        .into_iter()
        .flat_map(|state| &state.output)
    {
        printer.line(line);
    }
    printer.print(
        code::BEHAVIOR_UP_TO_THIS_POINT,
        Level::Error,
        "The behavior up to this point is:",
    );
    let labels: Vec<&str> = report.labels.iter().map(String::as_str).collect();
    print_states(printer, &trace.states, &labels);
    for line in &trace.trace_output {
        printer.line(line);
    }
}

fn print_states(printer: &mut Printer, states: &[PrintedState], labels: &[&str]) {
    for (position, (state, label)) in states.iter().zip(labels).enumerate() {
        if position > 0 {
            for line in &state.output {
                printer.line(line);
            }
        }
        printer.state(position + 1, label, state.variables.clone());
        printer
            .recorded_trace
            .record_state(position + 1, state.values.clone());
    }
}

// TLC names the properties the lasso violates, or none when it can't tell which
// (`getTemporalHeadline`).
fn temporal_headline(ir: &tla_ir::Ir, liveness: &Liveness) -> Option<String> {
    let Verdict::Lasso { violated, .. } = &liveness.verdict else {
        return None;
    };
    properties_headline(ir, violated)
}

// The headline that names the temporal properties at `violated` in the model's properties.
fn properties_headline(ir: &tla_ir::Ir, violated: &[usize]) -> Option<String> {
    let mut names: Vec<&str> = Vec::new();
    for &position in violated {
        let name = &*ir.texts[ir.model.live_properties.get(position)?.name as usize];
        if !names.contains(&name) {
            names.push(name);
        }
    }
    Some(match names.as_slice() {
        [] => "Temporal properties were violated.\n".into(),
        [name] => format!("Temporal property {name} was violated.\n"),
        [rest @ .., last] => format!(
            "Temporal properties {}{} and {last} were violated.\n",
            rest.join(", "),
            if rest.len() > 1 { "," } else { "" }
        ),
    })
}

/// What TLCGet reads once the search is over, for the postconditions: each `_POSSIBLE`
/// predicate's count, where the search counted them, and TLCGet("stats").
fn postcondition_run(
    ir: &tla_ir::Ir,
    possible: Option<&[i64]>,
    statistics: &Statistics,
    initial_generated: u64,
    start: Instant,
) -> PostconditionRun {
    let counts = |count: u64| i64::try_from(count).unwrap_or(i64::MAX);
    PostconditionRun {
        possible: possible
            .map(|possible| {
                ir.model
                    .possible
                    .iter()
                    .zip(possible)
                    .map(|(predicate, &count)| {
                        (ir.texts[predicate.name.name as usize].to_string(), count)
                    })
                    .collect()
            })
            .unwrap_or_default(),
        stats: Stats {
            queue: counts(statistics.queued),
            distinct: counts(statistics.distinct),
            initial: counts(initial_generated),
            generated: counts(statistics.generated),
            diameter: counts(statistics.depth),
            duration: counts(start.elapsed().as_secs()),
        },
    }
}

/// TLC's report of the first postcondition that doesn't hold, named with where its definition's
/// body is written (`findPostconditionViolation`).
pub(crate) fn print_postcondition_failure(
    printer: &mut Printer,
    ir: &tla_ir::Ir,
    postconditions: Option<&Postconditions>,
) {
    let Some((index, verdict)) = postconditions.and_then(|checked| checked.failure.as_ref()) else {
        return;
    };
    let postcondition = &ir.model.postconditions[*index];
    let name = &ir.texts[postcondition.name as usize];
    let location = postcondition
        .definition
        .and_then(|definition| {
            let node = ir.definitions[definition as usize];
            match &ir.nodes.arena[node as usize].kind {
                tla_ir::NodeKind::Definition(definition) => {
                    ir.nodes.arena[definition.body as usize].range
                }
                _ => None,
            }
        })
        .map(|range| {
            format!(
                " at line {}, col {} to line {}, col {} of module {}",
                range.start_line,
                range.start_column,
                range.end_line,
                range.end_column,
                ir.texts[range.module as usize]
            )
        })
        .unwrap_or_default();
    let (code, text) = match verdict {
        PostconditionVerdict::Failed { text, tool_text } => (
            code::POSTCONDITION_FAILED,
            format!(
                "Evaluating postcondition {name}{location} failed.\n{}",
                if printer.is_tool { tool_text } else { text }
            ),
        ),
        _ => (
            code::POSTCONDITION_FALSE,
            format!("Postcondition {name}{location} is false."),
        ),
    };
    printer.report(code, &text);
}

/// A spec TLC stops at before it searches: SANY's report, framed by SANY's start and finish under
/// -tool, then Starting..., then SANY's rejection of the spec or the error TLC reports.
// What TLC prints from SANY's report to `Starting...`: SANY's report, framed under -tool.
fn print_sany(printer: &mut Printer, sany: &str) {
    if printer.is_tool {
        printer.print(code::STARTING_SANY, Level::None, "Starting SANY...");
    }
    printer.raw(sany.as_bytes());
    if printer.is_tool {
        printer.print(code::SANY_FINISHED, Level::None, "SANY finished.");
    }
    printer.print(
        code::STARTING,
        Level::None,
        &format!("Starting... ({})", printer.date()),
    );
}

// `isTraceRecorded`: whether TLC writes the trace exploration spec, which it parses with the spec.
// Whether TLC writes a trace exploration spec after an error trace: unless -noGenerateSpecTE, -tool
// or -continue says not to, or the spec is one it wrote (`TraceExplorationSpec.isTESpecFile`), or
// where -generateSpecTE says to.
fn is_trace_spec_written(args: &Parsed, spec_path: &str) -> bool {
    let name = spec_path.rsplit('/').next().unwrap_or(spec_path);
    args.has("-generateSpecTE")
        || (!args.has("-noGenerateSpecTE")
            && !args.has("-tool")
            && !args.has("-continue")
            && !name.contains("_TTrace"))
}

// Whether TLC records the trace in a file for its trace exploration spec too, with `_TLCTrace`'s
// postcondition.
fn is_trace_recorded(args: &Parsed, spec_path: &str) -> bool {
    is_trace_spec_written(args, spec_path) && !args.has("-noGenerateSpecTEBin")
}

// A message TLC prints itself as it starts, as tla-front writes it.
pub(crate) fn print_startup_message(printer: &mut Printer, message: &StartupMessage) {
    let level = if message.is_warning {
        Level::Warning
    } else {
        Level::None
    };
    printer.print(message.code, level, &message.text);
}

// `TLC_SYMMETRY_SET_TOO_SMALL`, as `symmetry.ts` words it.
pub(crate) fn print_small_sets(printer: &mut Printer, names: &[String]) {
    let is_plural = names.len() > 1;
    printer.print(
        code::SYMMETRY_SET_TOO_SMALL,
        Level::Warning,
        &format!(
            "The set{} {} {} been defined to be a symmetry set but contain{} less than two elements.",
            if is_plural { "s" } else { "" },
            names.join(", and "),
            if is_plural { "have" } else { "has" },
            if is_plural { "" } else { "s" },
        ),
    );
}

fn print_failed_front(printer: &mut Printer, failure: &Failure, start: Instant) -> i32 {
    // SpecProcessor reports an exception of SANY's with `Assert.fail(EC.TLC_PARSING_FAILED2, e)`,
    // whose message TLC words with the code again (`MP.getMessage`), before SANY finishes.
    if let Some(exception) = &failure.exception {
        if printer.is_tool {
            printer.print(code::STARTING_SANY, Level::None, "Starting SANY...");
        }
        printer.raw(failure.sany.as_bytes());
        let message = format!("Parsing or semantic analysis failed.{exception}");
        let cause = if printer.is_tool {
            format!(
                "@!@!@STARTMSG {code}:0 @!@!@\n{message}\n@!@!@ENDMSG {code} @!@!@",
                code = code::PARSING_FAILED_EXCEPTION
            )
        } else {
            message
        };
        printer.print(
            code::PARSING_FAILED_EXCEPTION,
            Level::Error,
            &format!("Parsing or semantic analysis failed.{cause}"),
        );
        print_finished(printer, start);
        return SPEC_PARSE_ERROR;
    }
    print_sany(printer, &failure.sany);
    for warning in &failure.warnings {
        print_startup_message(printer, warning);
    }
    match &failure.error {
        Some(coded) => print_coded_failure(printer, coded, start),
        None => {
            printer.print(
                code::PARSING_FAILED,
                Level::Error,
                "Parsing or semantic analysis failed.",
            );
            print_finished(printer, start);
            SPEC_PARSE_ERROR
        }
    }
}

/// An error TLC reports with its code, then how long it ran (`printFailure`).
pub(crate) fn print_coded_failure(
    printer: &mut Printer,
    coded: &CodedError,
    start: Instant,
) -> i32 {
    printer.print(coded.code, Level::Error, &coded.text);
    print_finished(printer, start);
    coded.exit_code
}

/// Without -tool, TLC prints how long it ran for a person to read.
pub(crate) fn print_finished(printer: &mut Printer, start: Instant) {
    let runtime = start.elapsed().as_millis();
    let duration = if printer.is_tool {
        format!("{runtime}ms")
    } else {
        format_duration(runtime)
    };
    printer.print(
        code::FINISHED,
        Level::None,
        &format!("Finished in {duration} at ({})", printer.date()),
    );
    te_spec::write_after_finish(printer);
}

pub(crate) fn report_not_native(printer: &mut Printer, what: &str) -> i32 {
    printer.note(&format!("prove-it: not native yet: {what}"));
    NOT_NATIVE
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn knows_the_package_version() {
        assert!(package_version().split('.').count() == 3);
    }

    struct Quiet;

    impl Reporter for Quiet {
        fn initial_states_started(&mut self) {}
        fn initial_states_progress(&mut self, _count: u64) {}
        fn initial_states(&mut self, _generated: u64, _distinct: u64) {}
        fn progress(&mut self, _generated: u64, _distinct: u64, _queued: u64, _depth: u64) {}
        fn print(&mut self, _store: &tla_values::Store, _prints: &tla_engine::Prints) {}
    }

    // The engine IR of a model of the module, which is named `name`, and the configuration.
    fn lower(name: &str, module: &str, config: &str) -> tla_ir::Ir {
        let directory =
            std::env::temp_dir().join(format!("prove-it-{name}-{}", std::process::id()));
        std::fs::create_dir_all(&directory).expect("a directory");
        let spec = directory.join(format!("{name}.tla"));
        std::fs::write(&spec, module).expect("a spec");
        let options = tla_front::model::ModelOptions {
            libraries: &[],
            version: None,
            is_warning_enabled: true,
            is_spec_described: true,
            random_seed: 0,
            root_extendees: &[],
        };
        let bytes = tla_front::model::lower_model(&spec, config, &options).expect("a model");
        std::fs::remove_dir_all(&directory).expect("removed");
        tla_ir::decode(&bytes).expect("an IR")
    }

    #[test]
    fn answers_atoms_that_cache_on_the_machine_that_searched() {
        // TLC keeps one TLCCache for the run, filled as it first evaluates the expression: the
        // key 0 caches x of the initial state, 0, so the atom is FALSE where x is 1, and the
        // lasso that stutters there violates Prop, on any number of threads.
        let ir = lower(
            "Cached",
            "---- MODULE Cached ----\nEXTENDS Integers, TLC, TLCExt\nVARIABLE x\nInit == x = 0\nNext == x' = 1\nSpec == Init /\\ [][Next]_x\nProp == <>[](\\E i \\in {x} : TLCCache(i, 0) = x)\n====\n",
            "SPECIFICATION Spec\nPROPERTY Prop\n",
        );
        for threads in [1, 2, 4] {
            let settings = Settings {
                is_violation_reported: true,
                threads,
                ..Settings::default()
            };
            let outcome = tla_engine::on_nesting_stack(|| search(&ir, &settings, &mut Quiet));
            assert!(
                matches!(
                    &outcome,
                    SearchOutcome::Complete {
                        liveness: Some(tla_live::Liveness {
                            verdict: tla_live::Verdict::Lasso { .. },
                            ..
                        }),
                        ..
                    }
                ),
                "{threads} threads"
            );
        }
    }

    // IsSimpleCycle as the ewd998 example's Utils.tla defines it, with Range from the community
    // modules' Functions.tla, which reads F[i-1] twice: without its memo table, a call over n
    // nodes evaluates F's body 2^n - 1 times.
    const SIMPLE_CYCLE: &str = r"EXTENDS Integers, Sequences, FiniteSets, TLC
Range(f) == { f[x] : x \in DOMAIN f }
IsSimpleCycle(S, r) ==
  LET
   F[ i \in 1..Cardinality(S) ] ==
         IF i = 1 THEN << CHOOSE s \in S : TRUE >>
         ELSE LET seq == F[i-1]
                  head == Head(seq)
              IN << r[head] >> \o F[i-1]
  IN Range(F[Cardinality(S)]) = S
";

    // What a search found, from its counts and the fingerprints of its states in order, and on
    // how many threads it shared a level.
    fn get_found(ir: &tla_ir::Ir, settings: &Settings) -> (String, usize) {
        let outcome = tla_engine::on_nesting_stack(|| search(ir, settings, &mut Quiet));
        match outcome {
            SearchOutcome::Complete {
                counts,
                fingerprints,
                threads,
                ..
            } => (format!("{counts:?} {fingerprints:?}"), threads),
            SearchOutcome::Declined(reason) | SearchOutcome::Stopped { reason, .. } => {
                panic!("{reason}")
            }
            _ => panic!("a search that didn't complete"),
        }
    }

    // The workers read the ring the search's machine chose as the initial states were computed,
    // as TLC's do the value it computed at startup (SpecProcessor.processConstantDefns), rather
    // than choose it again each: within a budget of twice what one thread evaluates, they find
    // what one thread finds.
    #[test]
    fn shares_the_constants_the_search_computed_with_the_threads() {
        let ir = lower(
            "Ring",
            &format!(
                "---- MODULE Ring ----\n{SIMPLE_CYCLE}Node == 1..5\nRingOfNodes ==\n  CHOOSE r \\in [ Node -> Node ]: IsSimpleCycle(Node, r)\nVARIABLES x, n\nInit == x = RingOfNodes[1] /\\ n = 0\nNext == \\E k \\in 1..20 : n' = (n + k) % 400 /\\ x' = RingOfNodes[x]\nSpec == Init /\\ [][Next]_<<x, n>>\n====\n"
            ),
            "SPECIFICATION Spec\n",
        );
        let settings = |threads| Settings {
            threads,
            minimum_shared_level: 1,
            test_evaluations: Some(RING_EVALUATIONS),
            ..Settings::default()
        };
        let (one, _) = get_found(&ir, &settings(1));
        let (four, threads) = get_found(&ir, &settings(4));
        assert_eq!(four, one);
        assert!(threads > 1);
    }

    // Twice the 9,710 bodies of F that the search evaluates on one thread, choosing RingOfNodes
    // over 1..5, where each of four threads choosing it again would take about five times that.
    const RING_EVALUATIONS: u64 = 2 * 9_710;

    // A constant the threads read first is computed at most once on each, rather than again at
    // each level, by those that read it before the search's machine has it: within a budget of
    // four times the 4,855 bodies of F that choosing RingOfNodes over 1..5 evaluates, and a
    // fifth for room, they find what one thread finds.
    #[test]
    fn computes_a_constant_the_threads_read_first_at_most_once_on_each() {
        let ir = lower(
            "LateRing",
            &format!(
                "---- MODULE LateRing ----\n{SIMPLE_CYCLE}Node == 1..5\nRingOfNodes ==\n  CHOOSE r \\in [ Node -> Node ]: IsSimpleCycle(Node, r)\nVARIABLES x, n\nInit == x = 1 /\\ n = 0\nNext == \\E k \\in 1..20 : n' = (n + k) % 400 /\\ x' = IF n >= 50 THEN RingOfNodes[x] ELSE x\nSpec == Init /\\ [][Next]_<<x, n>>\n====\n"
            ),
            "SPECIFICATION Spec\n",
        );
        let settings = |threads, evaluations| Settings {
            threads,
            minimum_shared_level: 1,
            test_evaluations: Some(evaluations),
            ..Settings::default()
        };
        let (one, _) = get_found(&ir, &settings(1, 4_855));
        let (four, threads) = get_found(&ir, &settings(4, 5 * 4_855));
        assert_eq!(four, one);
        assert!(threads > 1);
    }

    // A full memo table of a recursive function forgets what it holds rather than take no more or
    // turn off, so each state's call over 20 nodes evaluates F's body 20 times rather than
    // 2^20 - 1, with a room that fills in a few states, on any number of threads.
    #[test]
    fn keeps_memoizing_a_recursive_function_once_its_table_is_full() {
        let ir = lower(
            "Shifted",
            &format!(
                "---- MODULE Shifted ----\n{SIMPLE_CYCLE}Node == 1..20\nShift(n) == [ i \\in Node |-> ((i + n) % 20) + 1 ]\nVARIABLE n\nInit == n = 0\nNext == \\E k \\in 1..10 : n' = (n + k) % 200\nSpec == Init /\\ [][Next]_n\nInv == IsSimpleCycle(Node, Shift(n)) \\in BOOLEAN\n====\n"
            ),
            "SPECIFICATION Spec\nINVARIANT Inv\n",
        );
        let settings = |threads| Settings {
            threads,
            minimum_shared_level: 1,
            test_memo_entries: Some(256),
            test_evaluations: Some(200 * 100),
            ..Settings::default()
        };
        let (one, _) = get_found(&ir, &settings(1));
        let (four, threads) = get_found(&ir, &settings(4));
        assert_eq!(four, one);
        assert!(threads > 1);
    }

    // A constant TLC computed at startup that draws keeps the search on one thread, which reads
    // the value drawn.
    #[test]
    fn keeps_a_search_that_draws_on_one_thread() {
        let ir = lower(
            "Drawn",
            "---- MODULE Drawn ----\nEXTENDS Integers, TLC\nDrawn == RandomElement(1..1000000)\nVARIABLES n, d\nInit == n = 0 /\\ d = Drawn\nNext == \\E k \\in 1..10 : n' = (n + k) % 200 /\\ d' = Drawn\nSpec == Init /\\ [][Next]_<<n, d>>\n====\n",
            "SPECIFICATION Spec\n",
        );
        let settings = |threads| Settings {
            threads,
            minimum_shared_level: 1,
            ..Settings::default()
        };
        let (one, _) = get_found(&ir, &settings(1));
        let (four, threads) = get_found(&ir, &settings(4));
        assert_eq!(four, one);
        assert_eq!(threads, 1);
    }

    // The progress a search reported: states generated, distinct and left on the queue.
    struct Progressed(Vec<[u64; 3]>);

    impl Reporter for Progressed {
        fn initial_states_started(&mut self) {}
        fn initial_states_progress(&mut self, _count: u64) {}
        fn initial_states(&mut self, _generated: u64, _distinct: u64) {}
        fn progress(&mut self, generated: u64, distinct: u64, queued: u64, _depth: u64) {
            self.0.push([generated, distinct, queued]);
        }
        fn print(&mut self, _store: &tla_values::Store, _prints: &tla_engine::Prints) {}
    }

    // TLC reports its progress while its workers expand a level, so a search that shares a level
    // reports it there too: once a thread claims the state PROVE_IT_TEST_PROGRESS_AT names, with
    // more than the 4,001 states generated before the level and fewer than the 8,001 after it.
    #[test]
    fn reports_its_progress_inside_a_shared_level() {
        let ir = lower(
            "Wide",
            "---- MODULE Wide ----\nEXTENDS Integers\nVARIABLE n\nInit == n = 0\nNext == \\/ n = 0 /\\ n' \\in 1..4000\n        \\/ n \\in 1..4000 /\\ n' = n + 4000\nSpec == Init /\\ [][Next]_n\n====\n",
            "SPECIFICATION Spec\nCHECK_DEADLOCK FALSE\n",
        );
        let settings = Settings {
            threads: 4,
            minimum_shared_level: 1,
            test_progress_at: Some(2000),
            ..Settings::default()
        };
        let mut progressed = Progressed(Vec::new());
        let outcome = tla_engine::on_nesting_stack(|| search(&ir, &settings, &mut progressed));
        let SearchOutcome::Complete { counts, .. } = outcome else {
            panic!("a search that didn't complete");
        };
        assert_eq!((counts.generated, counts.distinct), (8001, 8001));
        assert!(
            progressed
                .0
                .iter()
                .any(|&[generated, distinct, queued]| generated > 4001
                    && generated < 8001
                    && distinct > 4001
                    && distinct <= 8001
                    && distinct - queued > 1),
            "{:?}",
            progressed.0
        );
    }
}
