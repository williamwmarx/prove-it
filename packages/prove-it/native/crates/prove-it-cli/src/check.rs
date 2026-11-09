//! `prove-it <Spec>...`: `checkSpecs` and `checkSpec` in `src/cli/tlc.ts`. Each spec is checked as
//! TLC would in a process of its own; the exit code is the first that is not success.

use std::path::Path;
use std::sync::mpsc;
use std::time::{Instant, SystemTime};

use tla_engine::search::{
    ErrorSite, Reporter, SearchOutcome, Settings, Violation, ViolationKind, search,
};
use tla_live::{Liveness, Verdict};
use tla_values::print::{is_printable, write_value};
use tla_values::{Id, Store};

use crate::args::{Java, Parsed, USAGE, get_java_launch};
use crate::failure::{ErrorStop, print_failure};
use crate::files::FileDescriber;
use crate::front::read_front;
use crate::messages::{self as code, Level, Printer};
use crate::summary::{
    actual_probability, fingerprint_distance, format_count, format_probability,
    optimistic_probability, out_degree_summary,
};
use crate::time::{format_date, format_duration};
use crate::trace::{PostconditionRun, Postconditions, check_postconditions, rebuild_trace};
use tla_front::TlcVersion;
use tla_front::config::{ModelConfig, parse_config};
use tla_trace::{Site, pretty_print};
use tla_trace::{Stats, Verdict as PostconditionVerdict};

// TLC's exit statuses, from EC.ExitStatus.
const SUCCESS: i32 = 0;
const DEADLOCK: i32 = 11;
const ASSUMPTION_VIOLATION: i32 = 10;
const SAFETY_VIOLATION: i32 = 12;
const LIVENESS_VIOLATION: i32 = 13;
const CONFIG_PARSE_ERROR: i32 = 151;

/// The exit code of a run that needs something the binary doesn't do natively yet.
const NOT_NATIVE: i32 = 1;

const GLOB_CHARACTERS: [char; 4] = ['*', '?', '[', '{'];

/// How deep the search thread's stack may grow: compiled closures recurse with the expressions
/// and the values they evaluate. It is reserved, not committed.
pub(crate) const SEARCH_STACK_BYTES: usize = 256 * 1024 * 1024;

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
        exit_codes.push(check_spec(path, &parsed, java, &mut printer));
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
    /// TLC checks the temporal properties part way through the search: of how many branches, on
    /// the graph of how many states.
    LivenessStarted(u64, u64),
    LivenessFinished,
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

    fn liveness_started(&mut self, branches: u64, expanded: u64, _counts: [u64; 3]) {
        let _ = self.0.send(Event::LivenessStarted(branches, expanded));
    }

    fn liveness_finished(&mut self) {
        let _ = self.0.send(Event::LivenessFinished);
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
#[derive(Clone, Copy)]
pub(crate) struct Statistics {
    pub generated: u64,
    pub distinct: u64,
    pub queued: u64,
    pub depth: u64,
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

fn check_spec(spec_path: &str, args: &Parsed, java: &Java, printer: &mut Printer) -> i32 {
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
    let config_text = config_path.and_then(|path| std::fs::read_to_string(path).ok());
    let Some(config) = config_text
        .as_deref()
        .and_then(|text| parse_config(text, TlcVersion::Master).ok())
    else {
        return report_not_native(printer, "a configuration file the front end rejects");
    };
    if dump.is_some() {
        return report_not_native(printer, "-dump");
    }
    if args.has("-continue") {
        return report_not_native(printer, "-continue");
    }
    let front = match read_front(
        spec_path,
        config_text.as_deref().unwrap_or_default(),
        !args.has("-nowarning"),
        &FileDescriber::new(
            Path::new(spec_path),
            &java.libraries,
            java.temporary_directory.as_deref(),
            args.first("-metadir"),
            false,
        ),
        &java.libraries,
    ) {
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
    // The front end evaluates nothing, so the IR it lowers has none of TLC's actions, which the
    // trace evaluator finds as check.ts does. A model it can't split keeps none, and its traces
    // name no actions natively. The evaluator recurses, so it runs with the search's stack.
    if ir.model.actions.is_empty() {
        let split = std::thread::scope(|scope| {
            std::thread::Builder::new()
                .stack_size(SEARCH_STACK_BYTES)
                .spawn_scoped(scope, || tla_trace::add_actions(&ir).ok())
                .expect("a thread to split the next-state relation")
                .join()
                .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
        });
        if let Some(split) = split {
            ir = split;
        }
    }
    // TLC checks the temporal properties as the search goes, unless -lncheck asks for one check at
    // the end.
    let is_liveness_periodic = !args
        .first("-lncheck")
        .is_some_and(|check| ["final", "seqfinal", "off"].contains(&check.to_lowercase().as_str()));
    let settings = Settings {
        is_violation_reported: true,
        is_liveness_periodic,
        test_live_check_at: std::env::var("PROVE_IT_TEST_LIVE_CHECK_AT")
            .ok()
            .and_then(|at| at.parse().ok()),
        ..Settings::default()
    };
    let (sender, receiver) = mpsc::channel();
    // How many initial states TLC generated, which TLCGet("stats") reports.
    let mut initial_generated = 0;
    let outcome = std::thread::scope(|scope| {
        let ir = &ir;
        let searching = std::thread::Builder::new()
            .stack_size(SEARCH_STACK_BYTES)
            .spawn_scoped(scope, move || search(ir, &settings, &mut Relay(sender)))
            .expect("a thread for the search");
        let mut checking = None;
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
                Event::LivenessStarted(branches, expanded) => {
                    checking = Some(print_liveness_check(printer, branches, expanded, "current"));
                }
                Event::LivenessFinished => {
                    if let Some(checking) = checking.take() {
                        print_liveness_finished(printer, checking);
                    }
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
            fingerprints,
            liveness,
            violation,
            possible,
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
                            queued: 0,
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
                        is_lasso.then_some(&liveness),
                        Some(&run),
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
                    queued: 0,
                    depth: counts.depth,
                };
                let checking = print_liveness_started(printer, &statistics, liveness.branches);
                print_liveness_finished(printer, checking);
            }
            if !ir.model.postconditions.is_empty() {
                if has_constant_postcondition(&ir) {
                    return report_not_native(printer, "a POSTCONDITION TLC computes as it starts");
                }
                let statistics = Statistics {
                    generated: counts.generated,
                    distinct: counts.distinct,
                    queued: 0,
                    depth: counts.depth,
                };
                let run = postcondition_run(
                    &ir,
                    Some(&possible),
                    &statistics,
                    counts.initial_generated,
                    start,
                );
                let checked = match check_postconditions(&ir, &run) {
                    Ok(checked) => checked,
                    Err(reason) => return report_not_native(printer, &reason),
                };
                // What the postconditions print comes as TLC evaluates them; TLC reports one that
                // doesn't hold in place of the success, with the statistics.
                for line in &checked.printed {
                    printer.line(line);
                }
                if checked.failure.is_some() {
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
        // TLC reports a false assumption with no statistics, since it hasn't searched.
        SearchOutcome::AssumptionViolated { name } => {
            printer.print(
                code::ASSUMPTION_FALSE,
                Level::Error,
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
                // TLC's report of a failure evaluating the model, which it replays.
                // TLC prints the trace through the ALIAS and checks the postconditions after it,
                // which the printing doesn't follow yet.
                ViolationKind::Error { .. }
                    if config.alias.is_some()
                        || !config.postconditions.is_empty()
                        || !config.possible.is_empty() =>
                {
                    Err("a failure with an ALIAS, POSTCONDITION or _POSSIBLE".to_string())
                }
                ViolationKind::Error {
                    site: ErrorSite::InitialConstraint(_) | ErrorSite::InitialInvariant(_),
                } => Err(
                    "a failure on an initial state, which the printing doesn't follow yet"
                        .to_string(),
                ),
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
                            ErrorSite::InitialConstraint(_) | ErrorSite::InitialInvariant(_) => {
                                unreachable!(
                                    "a failure on an initial state, which the arm above leaves"
                                )
                            }
                        },
                        statistics: Statistics {
                            generated: counts.generated,
                            distinct: counts.distinct,
                            queued: counts.queued,
                            depth: counts.depth,
                        },
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
                    let run = postcondition_run(&ir, None, &statistics, initial_generated, start);
                    print_violation(printer, &ir, &config, &violation, None, Some(&run), start)
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

/// Once the search is complete, TLC reports how far it got, then checks the temporal properties
/// on the complete state graph (`liveness-started`): returns when it started.
fn print_liveness_started(
    printer: &mut Printer,
    statistics: &Statistics,
    branches: Option<usize>,
) -> Instant {
    print_progress(printer, statistics, None);
    let branches = branches.unwrap_or(1) as u64;
    print_liveness_check(printer, branches, statistics.distinct, "complete")
}

/// TLC checks the temporal properties of its branches on the graph of `states` states, of the
/// complete or the current state space: returns when it started.
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
            "Checking {branch_text}temporal properties for the {space} state space with {} total distinct states at ({})",
            branches * states,
            format_date(SystemTime::now())
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
            format_date(SystemTime::now())
        ),
    );
}

/// After a search, TLC prints how many states it found and how deep it went, after the progress
/// with -tool.
pub(crate) fn print_statistics(printer: &mut Printer, statistics: &Statistics, start: Instant) {
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

const NO_SPECIFICATION_WARNING: &str = "The stuttering counterexample above may be caused by the absence of a behavior specification (SPECIFICATION). Only INIT and NEXT have been provided, so TLC permits infinite stuttering. To rule out such counterexamples, use SPECIFICATION Spec, with Spec asserting a suitable fairness constraint (compare Chapter 8, page 87ff of Specifying Systems at https://lamport.azurewebsites.net/tla/book.html).";

/// Why `print_violation` can't print a violation yet, where the IR doesn't name what it reports.
const NOT_IN_IR: &str = "a name the IR doesn't carry";

/// Prints a violation the engine stopped at, or the lasso the liveness checker found, as
/// `printViolation` in `src/cli/tlc.ts` does, and returns the exit code, or why it can't print
/// it yet.
fn print_violation(
    printer: &mut Printer,
    ir: &tla_ir::Ir,
    config: &ModelConfig,
    violation: &Violation,
    liveness: Option<&Liveness>,
    postconditions: Option<&PostconditionRun>,
    start: Instant,
) -> Result<i32, &'static str> {
    // TLC reports a _POSSIBLE predicate the search never witnessed, which a search that stopped
    // doesn't count yet, before it checks the postconditions on the trace.
    let possible = postconditions.map_or(&[][..], |run| &run.possible[..]);
    if possible.len() != ir.model.possible.len() || possible.iter().any(|(_, count)| *count <= 0) {
        return Err("a _POSSIBLE predicate");
    }
    // An owner past the configuration's invariants is a property checked as one.
    let model = &ir.model;
    let invariant_name = |owner: usize| {
        let name = match owner.checked_sub(model.invariants.len()) {
            None => model.invariants[owner].root.name,
            Some(property) => *model
                .property_invariant_names
                .get(property)
                .ok_or(NOT_IN_IR)?,
        };
        Ok(&ir.texts[name as usize])
    };
    let action_label = |action: u32| {
        let action = model.actions.get(action as usize).ok_or(NOT_IN_IR)?;
        Ok(ir.texts[action.label as usize].as_ref())
    };
    let (code, text, exit_code) = match violation.kind {
        ViolationKind::InitialInvariant(owner) => (
            code::INVARIANT_VIOLATED_INITIAL,
            format!(
                "Invariant {} is violated by the initial state:",
                invariant_name(owner)?
            ),
            SAFETY_VIOLATION,
        ),
        ViolationKind::Invariant(owner) => (
            code::INVARIANT_VIOLATED_BEHAVIOR,
            format!("Invariant {} is violated.", invariant_name(owner)?),
            SAFETY_VIOLATION,
        ),
        ViolationKind::Deadlock => (code::DEADLOCK_REACHED, "Deadlock reached.".into(), DEADLOCK),
        ViolationKind::Error { .. } => return Err(NOT_IN_IR),
        ViolationKind::Lasso { .. } => (
            code::TEMPORAL_PROPERTY_VIOLATED,
            temporal_headline(ir, liveness.ok_or(NOT_IN_IR)?).ok_or(NOT_IN_IR)?,
            LIVENESS_VIOLATION,
        ),
        // A tableau node that accepts every behavior: TLC reports it as it does a safety
        // violation.
        ViolationKind::Accepted { ref violated } => (
            code::TEMPORAL_PROPERTY_VIOLATED,
            properties_headline(ir, violated).ok_or(NOT_IN_IR)?,
            SAFETY_VIOLATION,
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
        } => {
            let is_stuttering = loop_start + 1 == violation.states.len();
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
            // Without a SPECIFICATION the warning names none; with one, it names where it's
            // defined, which the IR doesn't carry yet.
            let is_warned = is_stuttering && is_cycle_constrained;
            if is_warned && config.specification.is_some() {
                return Err("a stuttering counterexample TLC warns of");
            }
            if !is_stuttering && is_printing {
                return Err("a step back into the cycle of a spec that prints");
            }
            let label = match loop_label {
                Some(action) => Some(action_label(action)?),
                None => None,
            };
            Some((loop_start, is_stuttering, label, is_warned))
        }
        _ => None,
    };
    // TLC prints a trace once it has rebuilt all of it, and a state that the evaluator can't
    // rebuild as TLC built it keeps the run not native.
    // After a violation, TLC checks no postcondition where one is a value it computes as it
    // starts.
    let checked = postconditions
        .filter(|_| !ir.model.postconditions.is_empty() && !has_constant_postcondition(ir));
    let trace = match rebuild_trace(ir, violation, checked) {
        Ok(trace) => trace,
        Err(reason) => return Ok(report_not_native(printer, &reason)),
    };
    // TLC labels each step with the action it finds taking it as it rebuilds the trace.
    let mut labels = vec!["Initial predicate"];
    for state in trace.states.iter().skip(1) {
        let action = state
            .action
            .ok_or("a step whose action the rebuilt trace lacks")?;
        labels.push(action_label(action)?);
    }
    let counts = &violation.counts;
    let statistics = Statistics {
        generated: counts.generated,
        distinct: counts.distinct,
        queued: counts.queued,
        depth: counts.depth,
    };
    // TLC prints the initial state that violates an invariant in the same message, and no
    // statistics, since it checks the initial states before it searches.
    if let ViolationKind::InitialInvariant(_) = violation.kind {
        let state = &trace.states.first().ok_or(NOT_IN_IR)?.text;
        printer.print(code, Level::Error, &format!("{text}\n{state}"));
        print_postcondition_failure(printer, ir, trace.postconditions.as_ref());
        print_finished(printer, start);
        return Ok(exit_code);
    }
    let checking =
        liveness.map(|liveness| print_liveness_started(printer, &statistics, liveness.branches));
    // What the spec printed as TLC rebuilt the trace: the first state's after the headline, each
    // later state's before it, and the rebuild after the trace. TLC rebuilds a counterexample
    // before it reports it, all of it as it recovers the first state (`printViolation`).
    let first_output = trace.states[0].output.iter();
    let (heading_code, heading) = if is_counterexample {
        for line in first_output.clone().chain(&trace.trace_output) {
            printer.line(line);
        }
        printer.print(code, Level::Error, &text);
        (
            code::COUNTER_EXAMPLE,
            "The following behavior constitutes a counter-example:\n",
        )
    } else {
        printer.print(code, Level::Error, &text);
        for line in first_output {
            printer.line(line);
        }
        (
            code::BEHAVIOR_UP_TO_THIS_POINT,
            "The behavior up to this point is:",
        )
    };
    printer.print(heading_code, Level::Error, heading);
    for (position, (state, label)) in trace.states.iter().zip(labels).enumerate() {
        if position > 0 {
            for line in &state.output {
                printer.line(line);
            }
        }
        printer.print(
            code::STATE_PRINT_2,
            Level::State,
            &format!("{}: <{label}>\n{}", position + 1, state.text),
        );
    }
    // What the postconditions printed follows the trace (`traceOutput`).
    for line in trace
        .postconditions
        .iter()
        .flat_map(|checked| &checked.printed)
    {
        printer.line(line);
    }
    match lasso {
        None if is_counterexample => {}
        None => {
            for line in &trace.trace_output {
                printer.line(line);
            }
        }
        Some((loop_start, true, _, _)) => printer.print(
            code::STATE_PRINT_3,
            Level::State,
            &format!("{}: Stuttering", loop_start + 2),
        ),
        Some((loop_start, false, label, _)) => {
            let label = label
                .map(|label| format!(": <{label}>\n"))
                .unwrap_or_default();
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
    // TLC's Liveness#printStutteringCounterExampleWarning.
    if lasso.is_some_and(|lasso| lasso.3) {
        printer.print(
            code::NO_SPECIFICATION_BUT_PROPERTY,
            Level::Warning,
            NO_SPECIFICATION_WARNING,
        );
    }
    print_postcondition_failure(printer, ir, trace.postconditions.as_ref());
    if let Some(checking) = checking {
        print_liveness_finished(printer, checking);
    }
    print_statistics(printer, &statistics, start);
    print_finished(printer, start);
    Ok(exit_code)
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

/// Whether a postcondition is a definition TLC computes as it starts, which it rejects.
fn has_constant_postcondition(ir: &tla_ir::Ir) -> bool {
    ir.model.postconditions.iter().any(|postcondition| {
        postcondition
            .definition
            .is_some_and(|definition| ir.model.startup.definitions.contains(&definition))
    })
}

/// TLC's report of the first postcondition that doesn't hold, named with where its definition's
/// body is written (`findPostconditionViolation`).
fn print_postcondition_failure(
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
        PostconditionVerdict::Failed(message) => (
            code::POSTCONDITION_FAILED,
            format!("Evaluating postcondition {name}{location} failed.\n{message}"),
        ),
        _ => (
            code::POSTCONDITION_FALSE,
            format!("Postcondition {name}{location} is false."),
        ),
    };
    printer.print(code, Level::Error, &text);
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
