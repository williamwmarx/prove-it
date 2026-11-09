//! `prove-it <Spec>...`: `checkSpecs` and `checkSpec` in `src/cli/tlc.ts`. Each spec is checked as
//! TLC would in a process of its own; the exit code is the first that is not success.

use std::path::Path;
use std::sync::mpsc;
use std::time::{Instant, SystemTime};

use tla_engine::search::{Reporter, SearchOutcome, Settings, Violation, ViolationKind, search};
use tla_values::print::{is_printable, write_value};
use tla_values::{Id, Store};

use crate::args::{Java, Parsed, USAGE, get_java_launch};
use crate::front::read_front;
use crate::messages::{self as code, Level, Printer};
use crate::pretty::pretty_print;
use crate::summary::{
    actual_probability, fingerprint_distance, format_count, format_probability,
    optimistic_probability, out_degree_summary,
};
use crate::time::{format_date, format_duration};
use crate::trace::format_state;
use tla_front::TlcVersion;
use tla_front::config::{ModelConfig, parse_config};

// TLC's exit statuses, from EC.ExitStatus.
const SUCCESS: i32 = 0;
const DEADLOCK: i32 = 11;
const SAFETY_VIOLATION: i32 = 12;
const CONFIG_PARSE_ERROR: i32 = 151;

/// The exit code of a run that needs something the binary doesn't do natively yet.
const NOT_NATIVE: i32 = 1;

const GLOB_CHARACTERS: [char; 4] = ['*', '?', '[', '{'];

/// How deep the search thread's stack may grow: compiled closures recurse with the expressions
/// and the values they evaluate. It is reserved, not committed.
const SEARCH_STACK_BYTES: usize = 256 * 1024 * 1024;

pub fn run(args: &[String]) -> i32 {
    if args.first().is_some_and(|arg| arg == "tlapm") {
        return not_native("tlapm");
    }
    let Some(launch) = get_java_launch(args) else {
        return check_specs(args, &Java::default());
    };
    if launch.java.class_path.is_some() {
        return not_native("reading the version of a tla2tools.jar");
    }
    match launch.main_class.as_str() {
        "tlc2.TLC" => check_specs(&launch.args, &launch.java),
        "tla2sany.xml.XMLExporter" => not_native("tla2sany.xml.XMLExporter"),
        other => {
            eprintln!(
                "Error: tla-ts runs the Java classes tlc2.TLC and tla2sany.xml.XMLExporter, not {other}."
            );
            1
        }
    }
}

fn not_native(what: &str) -> i32 {
    eprintln!("prove-it: not native yet: {what}");
    NOT_NATIVE
}

fn exists(path: &str) -> bool {
    Path::new(path).exists()
}

fn file_name(path: &str) -> String {
    Path::new(path).file_name().map_or_else(
        || path.to_string(),
        |name| name.to_string_lossy().into_owned(),
    )
}

fn check_specs(args: &[String], java: &Java) -> i32 {
    let parsed = Parsed::parse(args);
    if java.is_174 {
        return not_native("TLC 1.7.4");
    }
    if parsed
        .positionals
        .iter()
        .any(|path| path.contains(GLOB_CHARACTERS))
    {
        return not_native("globs");
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
        eprintln!("{USAGE}");
        return 1;
    }
    if is_configured && spec_paths.len() > 1 {
        eprintln!("Error: -config applies to one specification, but several were given.");
        return 1;
    }
    // TLC also looks for the spec itself in the library directories.
    let mut paths: Vec<String> = Vec::new();
    for path in spec_paths {
        let found = if exists(&path) || Path::new(&path).is_absolute() {
            path
        } else {
            java.libraries
                .iter()
                .map(|directory| Path::new(directory).join(&path))
                .find(|candidate| candidate.exists())
                .map(|candidate| candidate.to_string_lossy().into_owned())
                .unwrap_or(path)
        };
        if !paths.contains(&found) {
            paths.push(found);
        }
    }
    let mut exit_codes = Vec::new();
    for (index, path) in paths.iter().enumerate() {
        let mut printer = Printer::new(parsed.has("-tool"), !parsed.has("-nowarning"));
        if index > 0 {
            printer.line("");
        }
        // TLC checks one spec, so Prove It names each of several it checks.
        if paths.len() > 1 {
            let name = file_name(path);
            let stem = name.strip_suffix(".tla").unwrap_or(&name);
            printer.line(&format!("Checking {name} with {stem}.cfg"));
        }
        exit_codes.push(check_spec(path, &parsed, &mut printer));
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

fn read_trimmed(path: &str) -> Option<String> {
    std::fs::read_to_string(path)
        .ok()
        .map(|text| text.trim().to_string())
}

/// The memory the banner reports as the heap: the machine's, since the native search has no limit
/// of its own.
fn memory_megabytes() -> u64 {
    std::fs::read_to_string("/proc/meminfo")
        .ok()
        .and_then(|info| {
            let line = info.lines().find(|line| line.starts_with("MemTotal:"))?;
            line.split_whitespace().nth(1)?.parse::<u64>().ok()
        })
        .map_or(0, |kilobytes| kilobytes / 1024)
}

fn cores() -> usize {
    std::thread::available_parallelism().map_or(1, usize::from)
}

/// TLC.printStartupBanner, with what runs Prove It in place of the JVM.
fn print_startup_banner(printer: &mut Printer, seed: i64, workers: usize) {
    // Node's os.type(): the kernel's name.
    let system = read_trimmed("/proc/sys/kernel/ostype").unwrap_or_else(|| {
        match std::env::consts::OS {
            "macos" => "Darwin",
            "windows" => "Windows_NT",
            "linux" => "Linux",
            other => other,
        }
        .into()
    });
    let release = read_trimmed("/proc/sys/kernel/osrelease").unwrap_or_default();
    let arch = match std::env::consts::ARCH {
        "x86_64" => "x64",
        "aarch64" => "arm64",
        other => other,
    };
    printer.print(
        code::MODEL_CHECKING,
        Level::None,
        &format!(
            "Running breadth-first search Model-Checking with fp 0 and seed {seed} with {workers} worker{} on {} cores with {}MB heap and 0MB offheap memory [pid: {}] ({system} {release} {arch}, prove-it native {}bit, MemFPSet, MemStateQueue).",
            if workers == 1 { "" } else { "s" },
            cores(),
            memory_megabytes(),
            std::process::id(),
            usize::BITS,
        ),
    );
}

/// JavaScript's `Math.max(1, Number.parseInt(value, 10) || 1)`.
fn parse_workers(values: Option<&[String]>) -> usize {
    let Some(value) = values.and_then(|values| values.first()) else {
        return 1;
    };
    if value == "auto" {
        return cores();
    }
    let text = value.trim_start();
    let (sign, digits) = match text.strip_prefix('-') {
        Some(rest) => (-1, rest),
        None => (1, text.strip_prefix('+').unwrap_or(text)),
    };
    let end = digits
        .find(|character: char| !character.is_ascii_digit())
        .unwrap_or(digits.len());
    let count = digits[..end].parse::<i64>().unwrap_or(0) * sign;
    if count == 0 { 1 } else { count.max(1) as usize }
}

/// JavaScript's `Number(text) !== 0` for the index -fp names.
fn is_nonzero(text: &str) -> bool {
    let trimmed = text.trim();
    !trimmed.is_empty() && !trimmed.parse::<f64>().is_ok_and(|value| value == 0.0)
}

/// What the search reports as it runs, relayed from its thread.
enum Event {
    InitialStatesStarted,
    InitialStatesProgress(u64),
    InitialStates(u64, u64),
    Progress(u64, u64, u64, u64),
    /// What Print or PrintT printed, or nothing when TLC's text isn't known.
    Print(Option<String>),
}

struct Relay(mpsc::Sender<Event>);

impl Reporter for Relay {
    fn initial_states_started(&mut self) {
        let _ = self.0.send(Event::InitialStatesStarted);
    }

    fn initial_states_progress(&mut self, count: u64) {
        let _ = self.0.send(Event::InitialStatesProgress(count));
    }

    fn initial_states(&mut self, generated: u64, distinct: u64) {
        let _ = self.0.send(Event::InitialStates(generated, distinct));
    }

    fn progress(&mut self, generated: u64, distinct: u64, queued: u64, depth: u64) {
        let _ = self
            .0
            .send(Event::Progress(generated, distinct, queued, depth));
    }

    // Print and PrintT print each value as TLC's normalized text, pretty printed, two spaces
    // apart, unless the store has forgotten how TLC built one.
    fn print(&mut self, store: &Store, values: &[Id]) {
        let printed = values.iter().all(|&id| is_printable(store, id)).then(|| {
            values
                .iter()
                .map(|&id| {
                    let mut text = Vec::new();
                    write_value(store, id, &mut text);
                    pretty_print(&text)
                })
                .collect::<Vec<_>>()
                .join("  ")
        });
        let _ = self.0.send(Event::Print(printed));
    }
}

/// The counts a Progress line reports.
struct Statistics {
    generated: u64,
    distinct: u64,
    queued: u64,
    depth: u64,
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
            format_date(SystemTime::now()),
            format_count(statistics.generated),
            rate(statistics.generated, "s"),
            format_count(statistics.distinct),
            rate(statistics.distinct, "ds"),
            format_count(statistics.queued),
        ),
    );
}

fn print_initial_states(printer: &mut Printer, generated: u64, distinct: u64) {
    let date = format_date(SystemTime::now());
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

fn check_spec(spec_path: &str, args: &Parsed, printer: &mut Printer) -> i32 {
    // TLC.handleParameters: TLC reads its options before it says which version it is.
    let seed = if args.has("-seed") {
        args.first("-seed")
    } else {
        Some("0")
    };
    let Some(seed) = seed else {
        return print_command_line_error(printer, "Error: seed required.");
    };
    let Ok(seed) = seed.parse::<i64>() else {
        return print_command_line_error(
            printer,
            &format!("Error: An integer for seed required. But encountered {seed}"),
        );
    };
    if args.has("-lncheck") && args.first("-lncheck").is_none() {
        return print_command_line_error(
            printer,
            "Error: expect a strategy such as final for -lncheck option.",
        );
    }
    let dump = args.get("-dump");
    if dump.is_some_and(<[String]>::is_empty) {
        return print_command_line_error(
            printer,
            "Error: A file name for dumping states required.",
        );
    }
    if let Some([format, _]) = dump {
        let format = format.to_lowercase();
        if let Some(unsupported) = ["constrained", "stuttering", "strict"]
            .into_iter()
            .find(|unsupported| format.contains(unsupported))
        {
            eprintln!("Error: tla-ts does not support the -dump format {unsupported}.");
            return 1;
        }
    }
    if let Some(index) = args.first("-fp").filter(|index| is_nonzero(index)) {
        eprintln!("Error: tla-ts fingerprints states as TLC does with -fp 0, not -fp {index}.");
        return 1;
    }
    let workers = parse_workers(args.get("-workers"));
    print_welcome(printer);
    print_startup_banner(printer, seed, workers);
    let config_path = match args.get("-config") {
        Some(values) => values.first().cloned(),
        None => Some(match spec_path.strip_suffix(".tla") {
            Some(stem) => format!("{stem}.cfg"),
            None => spec_path.to_string(),
        }),
    };
    if !config_path.as_deref().is_some_and(exists) {
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
    // The front end reports a configuration it can't read; the binary reads what it prints by.
    let Some(config) = config_path
        .and_then(|path| std::fs::read_to_string(path).ok())
        .and_then(|text| parse_config(&text, TlcVersion::Master).ok())
    else {
        return report_not_native(printer, "a configuration file the front end rejects");
    };
    if dump.is_some() {
        return report_not_native(printer, "-dump");
    }
    if args.has("-continue") {
        return report_not_native(printer, "-continue");
    }
    let front = match read_front(spec_path) {
        Ok(front) => front,
        Err(reason) => return report_not_native(printer, &reason),
    };
    printer.raw(&front.output);
    let mut ir = match tla_ir::decode(&front.ir) {
        Ok(ir) => ir,
        Err(error) => {
            return report_not_native(printer, &format!("the engine IR doesn't decode: {error}"));
        }
    };
    if args.has("-deadlock") {
        ir.model.check_deadlock = false;
    }
    if ir.model.is_recording_graph {
        return report_not_native(printer, "checking temporal properties");
    }
    let (sender, receiver) = mpsc::channel();
    let outcome = std::thread::scope(|scope| {
        let ir = &ir;
        let searching = std::thread::Builder::new()
            .stack_size(SEARCH_STACK_BYTES)
            .spawn_scoped(scope, move || {
                search(
                    ir,
                    &Settings {
                        is_violation_reported: true,
                        ..Settings::default()
                    },
                    &mut Relay(sender),
                )
            })
            .expect("a thread for the search");
        for event in receiver {
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
                Event::Print(Some(text)) => printer.line(&text),
                // Nothing more this run prints can be right, so it ends here rather than search
                // on, the search thread with it.
                Event::Print(None) => std::process::exit(report_not_native(
                    printer,
                    "printing a value whose text depends on how TLC built it",
                )),
            }
        }
        searching
            .join()
            .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
    });
    let (counts, fingerprints) = match outcome {
        SearchOutcome::Complete {
            counts,
            checkpoint: None,
            fingerprints,
            ..
        } => (counts, fingerprints),
        SearchOutcome::Complete { .. } => {
            return report_not_native(printer, "checking temporal properties");
        }
        SearchOutcome::Declined(reason) => {
            return report_not_native(printer, &format!("the engine declined: {reason}"));
        }
        SearchOutcome::Stopped {
            violation: Some(violation),
            reason,
            ..
        } => {
            return print_violation(printer, &ir, &config, &violation, start).unwrap_or_else(
                || report_not_native(printer, &format!("the engine stopped: {reason}")),
            );
        }
        SearchOutcome::Stopped { reason, .. } => {
            return report_not_native(printer, &format!("the engine stopped: {reason}"));
        }
        SearchOutcome::Invariant(reason) => {
            return report_not_native(printer, &format!("an engine invariant failed: {reason}"));
        }
    };
    let optimistic = optimistic_probability(counts.distinct, counts.generated);
    let actual = fingerprint_distance(counts.distinct, counts.generated, &fingerprints)
        .map(|distance| {
            format!(
                "\n  based on the actual fingerprints:  val = {}",
                format_probability(actual_probability(distance))
            )
        })
        .unwrap_or_default();
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
        queued: 0,
        depth: counts.depth,
    };
    print_statistics(printer, &statistics, start);
    if let Some(summary) = out_degree_summary(&counts.out_degrees) {
        printer.print(code::STATE_GRAPH_OUTDEGREE, Level::None, &summary);
    }
    print_finished(printer, start);
    SUCCESS
}

/// After a search, TLC prints how many states it found and how deep it went, after the progress
/// with -tool.
fn print_statistics(printer: &mut Printer, statistics: &Statistics, start: Instant) {
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

/// Prints a violation the engine stopped at, as `printViolation` in `src/cli/tlc.ts` does, and
/// returns the exit code, or nothing when it can't print it yet.
fn print_violation(
    printer: &mut Printer,
    ir: &tla_ir::Ir,
    config: &ModelConfig,
    violation: &Violation,
    start: Instant,
) -> Option<i32> {
    // TLC prints a state through the ALIAS when there is one, which the IR doesn't carry yet, and
    // checks the postconditions on the trace after it prints it.
    if config.alias.is_some() || !config.postconditions.is_empty() || !config.possible.is_empty() {
        return None;
    }
    let invariant_name = |owner: usize| {
        ir.model
            .invariants
            .get(owner)
            .map(|invariant| &ir.texts[invariant.root.name as usize])
    };
    let (code, text, exit_code) = match violation.kind {
        // TLC prints the initial state that violates an invariant in the same message, and no
        // statistics, since it checks the initial states before it searches.
        ViolationKind::InitialInvariant(owner) => {
            let name = invariant_name(owner)?;
            let state = match rebuild(ir, violation)? {
                Some(rebuilt) => rebuilt[0].clone(),
                None => format_state(ir, &violation.store, violation.states.first()?)?,
            };
            printer.print(
                code::INVARIANT_VIOLATED_INITIAL,
                Level::Error,
                &format!("Invariant {name} is violated by the initial state:\n{state}"),
            );
            print_finished(printer, start);
            return Some(SAFETY_VIOLATION);
        }
        ViolationKind::Invariant(owner) => (
            code::INVARIANT_VIOLATED_BEHAVIOR,
            format!("Invariant {} is violated.", invariant_name(owner)?),
            SAFETY_VIOLATION,
        ),
        ViolationKind::Deadlock => (code::DEADLOCK_REACHED, "Deadlock reached.".into(), DEADLOCK),
    };
    let rebuilt = rebuild(ir, violation)?;
    // TLC prints nothing of the trace until it has rebuilt all of it.
    let mut steps = Vec::with_capacity(violation.states.len());
    for (position, state) in violation.states.iter().enumerate() {
        let label = match position.checked_sub(1) {
            None => "Initial predicate",
            Some(step) => {
                let action = ir
                    .model
                    .actions
                    .get(*violation.labels.get(step)? as usize)?;
                &ir.texts[action.label as usize]
            }
        };
        let state = match &rebuilt {
            Some(rebuilt) => rebuilt[position].clone(),
            None => format_state(ir, &violation.store, state)?,
        };
        steps.push(format!("{}: <{label}>\n{state}", position + 1));
    }
    printer.print(code, Level::Error, &text);
    printer.print(
        code::BEHAVIOR_UP_TO_THIS_POINT,
        Level::Error,
        "The behavior up to this point is:",
    );
    for step in &steps {
        printer.print(code::STATE_PRINT_2, Level::State, step);
    }
    let counts = &violation.counts;
    let statistics = Statistics {
        generated: counts.generated,
        distinct: counts.distinct,
        queued: counts.queued,
        depth: counts.depth,
    };
    print_statistics(printer, &statistics, start);
    print_finished(printer, start);
    Some(exit_code)
}

// Under PROVE_IT_TRACE_EVALUATOR=1, the trace's states as tla-trace rebuilds them.
fn rebuild(ir: &tla_ir::Ir, violation: &Violation) -> Option<Option<Vec<String>>> {
    if std::env::var("PROVE_IT_TRACE_EVALUATOR").as_deref() != Ok("1") {
        return Some(None);
    }
    let result = tla_trace::Rebuilder::new(ir).and_then(|mut rebuilder| {
        let states: Vec<&[tla_values::Id]> = violation.states.iter().map(Vec::as_slice).collect();
        let labels: Vec<Option<u32>> = violation.labels.iter().copied().map(Some).collect();
        rebuilder
            .rebuild(&violation.store, &states, &labels)
            .map(|trace| {
                trace
                    .states
                    .iter()
                    .map(|state| crate::trace::format_values(ir, &state.values))
                    .collect()
            })
    });
    match result {
        Ok(states) => Some(Some(states)),
        Err(tla_trace::Unsupported(reason)) => {
            eprintln!("prove-it: not native yet: {reason}");
            None
        }
    }
}

/// Without -tool, TLC prints how long it ran for a person to read.
fn print_finished(printer: &mut Printer, start: Instant) {
    let runtime = start.elapsed().as_millis();
    let duration = if printer.is_tool {
        format!("{runtime}ms")
    } else {
        format_duration(runtime)
    };
    printer.print(
        code::FINISHED,
        Level::None,
        &format!(
            "Finished in {duration} at ({})",
            format_date(SystemTime::now())
        ),
    );
}

fn report_not_native(printer: &mut Printer, what: &str) -> i32 {
    printer.flush();
    not_native(what)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reads_workers_as_parse_int() {
        let workers = |text: &str| parse_workers(Some(&[text.to_string()]));
        assert_eq!(parse_workers(None), 1);
        assert_eq!(workers("4"), 4);
        assert_eq!(workers(" 3x"), 3);
        assert_eq!(workers("0"), 1);
        assert_eq!(workers("-2"), 1);
        assert_eq!(workers("x"), 1);
        assert_eq!(workers("auto"), cores());
    }

    #[test]
    fn reads_the_fingerprint_index_as_number() {
        assert!(!is_nonzero("0"));
        assert!(!is_nonzero(""));
        assert!(!is_nonzero(" 0.0 "));
        assert!(is_nonzero("1"));
        assert!(is_nonzero("x"));
    }

    #[test]
    fn knows_the_package_version() {
        assert!(package_version().split('.').count() == 3);
    }
}
