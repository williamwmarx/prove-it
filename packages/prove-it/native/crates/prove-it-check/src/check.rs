//! `prove-it <Spec>...`: `checkSpecs` and `checkSpec` in `src/cli/tlc.ts`. Each spec is checked as
//! TLC would in a process of its own; the exit code is the first that is not success.

use std::path::Path;

use crate::host_path::Platform;
use std::sync::{Arc, mpsc};
use std::time::Duration;
use tla_engine::Prints;
use tla_engine::clock::Instant;

use tla_engine::search::{
    Continued, ContinuedTrace, Delegated, ErrorSite, HostFiles, JsonFiles, LeftStartup,
    MINIMUM_SHARED_LEVEL, Reporter, SearchOutcome, Settings, Violation, ViolationKind, search,
};
use tla_live::{Liveness, Verdict};
use tla_values::print::{is_printable, is_printable_normalized, write_value};
use tla_values::{Id, Store};

use crate::args::{Java, Parsed, Stop, USAGE, get_java_launch, is_auto};
use crate::coverage;
use crate::dot::DotOptions;
use crate::dump_trace::{TraceDumps, write};
use crate::failure::{
    ErrorStop, deadlock_atom_stack, print_assumption_failure, print_call_stack, print_failure,
};
use crate::front::{Failure, Read, read_front};
use crate::host::{Files, Host};
use crate::jar::{get_tools_jar, is_174};
use crate::messages::{self as code, Level, Output, Printer};
use crate::outcome::{Counts, Reported, ReportedState, Thrown};
use crate::resolve::{Config, find_config, find_spec, get_module_directories};
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
    check_postconditions, format_texts, format_variables, get_diff_text, print_possible_counts,
    rebuild_accepted, rebuild_continued, rebuild_trace,
};
use crate::xml_exporter::run_xml_exporter;
use tla_front::TlcVersion;
use tla_front::config::{ModelConfig, parse_config};
use tla_front::errors::{FrontError, UNEXPECTED_EXCEPTION};
use tla_front::model::StartupMessage;
use tla_front::tlc_messages::CodedError;
use tla_front::tlc_messages::STACK_OVERFLOW_MESSAGE;
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

/// The most levels of DFID stacks the binary answers for: about 15 MB of TLC's heap, which any
/// JVM it runs on has.
const DFID_STACKS_MODELLED: u64 = 100_000;

/// The exit code of a run that needs something the binary doesn't do natively yet.
const NOT_NATIVE: i32 = 1;
// The engine's reason for an initial state some variable lacks a value in.
const INCOMPLETE_INITIAL_STATE: &str = "an initial state that isn't complete";
// How much of the -dump file's text the relay holds before it sends it to be written.
const DUMP_PART_BYTES: usize = 1 << 20;

const GLOB_CHARACTERS: [char; 4] = ['*', '?', '[', '{'];

/// The system properties that change what SANY's XMLExporter prints: SemanticNode's plain
/// formulae and SANY's errors on stderr. XMLExporter reads no other property of TLC's.
const XML_EXPORTER_PROPERTIES: [&str; 2] = [
    "tla2sany.semantic.SemanticNode.showPlainFormulae",
    "tla2sany.drivers.SANY.errors2stderr",
];

/// Runs the command line `args` as TLC (or SANY's XMLExporter) would, writing to `output`, and
/// returns the exit code.
pub fn run(args: &[String], output: &mut Output<'_>) -> i32 {
    crate::transaction::run(output, |staged| run_in_place(args, staged))
}

fn run_in_place(args: &[String], output: &mut Output<'_>) -> i32 {
    if args.first().is_some_and(|arg| arg == "tlapm") {
        return crate::tlapm::run(&args[1..], output);
    }
    let Some(mut launch) = get_java_launch(args, output.host.platform()) else {
        return check_specs(args, &Java::default(), false, output);
    };
    // The JVM takes more options from these variables. A system property set there is one TLC
    // reads as it would from the command line, which the binary models only there.
    for variable in crate::front::JVM_OPTION_VARIABLES {
        let Some(options) = output.host.get_variable(variable) else {
            continue;
        };
        for option in options.split_whitespace() {
            let Some(property) = option.strip_prefix("-D") else {
                continue;
            };
            let name = property.split_once('=').map_or(property, |(name, _)| name);
            if crate::args::MODELLED_PROPERTIES.contains(&name) {
                return not_native(
                    output,
                    &format!("the system property {name} {variable} sets"),
                );
            }
            if crate::args::is_unmodelled_property(name) {
                launch
                    .java
                    .unmodelled_property
                    .get_or_insert_with(|| name.into());
            }
            launch.java.properties.push(name.into());
        }
    }
    // Without -Dtla-ts.tlc, the jar on the class path picks the TLC to reproduce.
    let jar = launch
        .java
        .class_path
        .as_deref()
        .and_then(|class_path| get_tools_jar(class_path, output.host.platform()));
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
        "tla2sany.xml.XMLExporter" => match launch
            .java
            .properties
            .iter()
            .find(|name| XML_EXPORTER_PROPERTIES.contains(&name.as_str()))
        {
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

/// What TLC prints for -help and -h (`TLC.printUsage`), as the jar of the TLC Prove It reproduces
/// prints it.
const TLC_USAGE: &str = include_str!("tlc_usage.txt");

/// Whether the spec may build a value TLC keeps lazy, which prints otherwise under -terse
/// (`TLCGlobals.expand`): a power set, a set of functions, of records or of tuples, a recursive
/// function or one defined as `f[x \in S] == e`, a function a constant definition builds, which
/// TLC may hold as written, or a set TLC
/// doesn't enumerate, which keeps a union, an intersection, a difference, a filter or a function
/// over it lazy (`Tool.evalAppl`, whose operations are eager only on a Reducible set).
fn may_build_lazy_value(ir: &tla_ir::Ir) -> bool {
    use tla_ir::{NodeKind, Resolution};
    const UNENUMERATED: [&str; 8] = [
        "SUBSET", "Nat", "Int", "Real", "STRING", "Seq", "kSubset", "Any",
    ];
    let is_set_enumeration = |node: tla_ir::NodeId| {
        matches!(
            ir.nodes.arena[node as usize].kind,
            NodeKind::SetEnumeration(_)
        )
    };
    let is_lazy_builtin = |name: &tla_ir::Name| match name.resolution {
        Resolution::Builtin(index) => {
            let builtin = &ir.builtins[index as usize];
            builtin.flags & tla_ir::Builtin::LAZY != 0
                || UNENUMERATED.contains(&&*ir.texts[builtin.name as usize])
        }
        _ => false,
    };
    let is_lazy_node = ir.nodes.arena.iter().any(|node| match &node.kind {
        NodeKind::FunctionSet { .. } | NodeKind::RecordSet(_) | NodeKind::Product(_) => true,
        NodeKind::FunctionConstruction { is_recursive, .. } => *is_recursive,
        NodeKind::Identifier(name) | NodeKind::OperatorReference(name) => is_lazy_builtin(name),
        // UNION is a set enumeration only of a set enumeration of set enumerations
        // (`UnionValue.union`).
        NodeKind::Apply { name, args } if &*ir.texts[name.text as usize] == "UNION" => {
            !matches!(args[..], [set] if matches!(&ir.nodes.arena[set as usize].kind,
                NodeKind::SetEnumeration(sets) if sets.iter().all(|&set| is_set_enumeration(set))))
        }
        NodeKind::Apply { name, .. } => is_lazy_builtin(name),
        _ => false,
    });
    is_lazy_node
        || ir.definitions.iter().any(|&definition| {
            matches!(&ir.nodes.arena[definition as usize].kind,
            NodeKind::Definition(definition)
                if match &definition.form {
                    tla_ir::DefinitionForm::Function(_) => true,
                    tla_ir::DefinitionForm::Operator(params) => params.is_empty()
                        && matches!(ir.nodes.arena[definition.body as usize].kind,
                            NodeKind::FunctionConstruction { .. }),
                })
        })
}

/// Whether the command line gives -userFile, whose file TLC creates as it reads the option.
fn is_before_user_file(args: &[String]) -> bool {
    args.iter().any(|arg| arg == "-userFile")
}

pub(crate) fn not_native(output: &mut Output<'_>, what: &str) -> i32 {
    crate::transaction::mark_declined(what);
    let _ = writeln!(output.err, "prove-it: not native yet: {what}");
    NOT_NATIVE
}

// With `is_tlc` the command line is `tlc2.TLC`'s, which names one module.
fn check_specs(args: &[String], java: &Java, is_tlc: bool, output: &mut Output<'_>) -> i32 {
    if java.tlc_version == Some(TlcVersion::V1_7_4) {
        return not_native(output, "TLC 1.7.4");
    }
    let parsed = match Parsed::parse(args, is_tlc) {
        Ok(parsed) => parsed,
        Err(Stop::NotNative(what)) => return not_native(output, &what),
        // TLC creates the file of a -userFile as it reads the option, before it reads a later
        // one it rejects, which the binary doesn't follow.
        Err(Stop::Error { .. } | Stop::Usage) if is_before_user_file(args) => {
            return not_native(output, "-userFile before an option TLC stops at");
        }
        // A class path beyond the jar may hold the -dump class's writer.
        Err(Stop::Error { message, .. })
            if message.starts_with("Trying to instantiate a custom IStateWriter")
                && java.origin_profile(
                    java.class_path
                        .as_deref()
                        .and_then(|path| get_tools_jar(path, output.host.platform())),
                ) == tla_front::model::JavaProfile::Opaque =>
        {
            return not_native(output, "-dump class, with a class path beyond the jar");
        }
        Err(Stop::Error { message, is_tool }) => {
            return print_command_line_error(&mut Printer::new(is_tool, true, output), &message);
        }
        // TLC prints the usage text alone, with no message code even under -tool.
        Err(Stop::Usage) => {
            let _ = output.out.write_all(TLC_USAGE.as_bytes());
            return 1;
        }
    };
    // `new FileWriter(file)`, which creates the file or empties it; TLC reports one it can't
    // create as it reads the option, before the other options' checks after the last
    // (`handleParameters`), which the binary has made.
    for (option, values) in &parsed.options {
        if option != "-userFile" {
            continue;
        }
        let path = Path::new(&values[0]);
        if output.host.write_file(path, b"", false) {
            continue;
        }
        if !crate::host::is_directory_there(output.host, path) {
            let is_tool = parsed.has("-tool");
            return print_command_line_error(
                &mut Printer::new(is_tool, true, output),
                "Error: Failed to create user output log file.",
            );
        }
        return not_native(output, "-userFile into a file it can't create");
    }
    // With -cleanup TLC deletes the `states` directory where it runs (TLC.java:1274), which the
    // binary doesn't.
    if parsed.has("-cleanup")
        && output.host.kind(&output.host.current_dir().join("states"))
            != crate::host::FileKind::Absent
    {
        return not_native(output, "-cleanup with a states directory to delete");
    }
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
    // TLC also looks for the spec itself in the library directories. Each spec keeps the path it
    // was given, which names where TLC writes its trace exploration spec.
    let mut paths: Vec<(String, &str)> = Vec::new();
    for given in &spec_paths {
        let found = find_spec(output.host, given, &java.libraries);
        if !paths.iter().any(|(path, _)| *path == found) {
            paths.push((found, given));
        }
    }
    if paths.len() > 1 && parsed.is_fpmem_absolute() {
        return not_native(output, "-fpmem's notice with several specifications");
    }
    if paths.len() > 1 && !output.host.is_checking_several() {
        return not_native(
            output,
            "several specifications in one check of a host's sources",
        );
    }
    let platform = output.host.platform();
    let mut exit_codes = Vec::new();
    let mut printed = false;
    for (path, given) in &paths {
        let (code, _, is_printed) = crate::transaction::run_scoped(output, |staged| {
            let _tokens = tla_front::lexer::SharedTokens::start();
            let mut printer = Printer::new(parsed.has("-tool"), !parsed.has("-nowarning"), staged);
            printer.suppressed = parsed.get_codes("-suppressMessages");
            printer.as_errors = parsed.get_codes("-messagesAsErrors");
            printer.is_diff_trace = parsed.has("-difftrace");
            printer.user_file = parsed.get("-userFile").map(|file| file[0].clone().into());
            if printed {
                printer.line("");
            }
            for _ in 0..parsed.count_fpmem_absolute() {
                printer.line(
                    "Using -fpmem with an abolute memory value has been deprecated. Please \
                     allocate memory for the TLC process via the JVM mechanisms and use -fpmem \
                     to set the fraction to be used for fingerprint storage.",
                );
            }
            // TLC checks one spec, so Prove It names each of several it checks.
            if paths.len() > 1 {
                let name = platform.file_name(path).to_string();
                let stem = name.strip_suffix(".tla").unwrap_or(&name);
                printer.line(&format!("Checking {name} with {stem}.cfg"));
            }
            let main_file = given.strip_suffix(".tla").unwrap_or(given);
            let exit_code = check_spec(path, main_file, &parsed, java, is_tlc, &mut printer);
            // A run with an error TLC may have checked `_TLCTrace`'s postcondition on, which fails
            // to write its file, other than the report of a safety violation's trace.
            if exit_code != SUCCESS && printer.unplaced_trace_file.take().is_some() {
                printer.trace_spec_decline.get_or_insert_with(|| {
                    "-teSpecOutDir into a directory that isn't there".into()
                });
            }
            // TLC evaluates the ALIAS as it prints a state (`Tool.evalAlias`): of a trace, as it
            // simulates or as it dumps, never in a run that finds no error.
            let alias_decline = printer
                .alias_decline
                .take()
                .filter(|_| exit_code != SUCCESS || parsed.has("-simulate") || parsed.has("-dump"));
            match printer.trace_spec_decline.take().or(alias_decline) {
                Some(reason) => report_not_native(&mut printer, &reason),
                None => exit_code,
            }
        });
        printed |= is_printed;
        exit_codes.push(code);
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
    is_dfid: bool,
) {
    let machine = printer.host.machine();
    let (system, release, arch) = (&machine.system, &machine.release, &machine.arch);
    printer.print(
        if is_dfid { 2271 } else { code::MODEL_CHECKING },
        Level::None,
        &format!(
            "Running {} search Model-Checking with fp {fingerprint_index} and seed {seed} with {workers} worker{} on {} cores with {}MB heap and 0MB offheap memory [pid: {}] ({system} {release} {arch}, prove-it native {}bit, MemFPSet, MemStateQueue).",
            if is_dfid { "depth-first" } else { "breadth-first" },
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
    DfidLevel(u32, u64, u64),
    DfidContinued(Box<DfidContinuedReport>),
    InitialStatesStarted,
    InitialStatesProgress(u64),
    InitialStates(u64, u64),
    Progress(u64, u64, u64, u64),
    /// TLC checks the temporal properties part way through the search: of how many branches, on
    /// behavior graphs of how many states in all, and the search's counts then.
    LivenessStarted(u64, u64, Statistics),
    LivenessFinished,
    /// What Print or PrintT printed, or nothing when TLC's text isn't known.
    Print(Option<String>),
    Warning(tla_engine::RuntimeWarning),
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
pub(crate) struct DfidContinuedReport {
    code: u32,
    headline: String,
    states: Vec<Vec<crate::plain::Variable>>,
    is_initial: bool,
}

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
    /// The -dfid bound, past which the relay declines a search as its level 2 starts.
    dfid: Option<u32>,
    /// Whether `-dump` writes each state the search found, as TLC's `StateWriter` does: the relay
    /// sends the text in parts (`Event::Dumped`) for the host to write.
    is_dumped: bool,
    /// Whether the dump holds every state, or why it doesn't, once the search handed them over.
    dumped: Option<Result<(), &'static str>>,
    /// Under `-dump dot`, its options, and the graph once the search handed it over, or why the
    /// binary doesn't write it as TLC does.
    dot: Option<DotOptions>,
    dotted: Option<Result<(String, bool), &'static str>>,
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
    /// Whether the search found each startup definition failing as TLC started.
    failed_startup: Vec<bool>,
    /// What the run printed of the assumptions, from `startup_done` on.
    pub(crate) assumed_printed: Vec<crate::trace::PrintedOutput>,
    /// Why the trace evaluator mustn't check an assumption the engine leaves to it, as where it
    /// would read the model checker's TLCGet in a simulation.
    pub(crate) undelegated: Option<&'static str>,
    /// What the trace evaluator finds the assumptions print, in order, where the store forgot how
    /// TLC built a value one prints.
    assumed_texts: Option<Option<Vec<String>>>,
    /// What the trace evaluator finds they print, as TLC built the values, where the store
    /// forgot how TLC built one.
    startup_texts: Option<Option<Vec<String>>>,
    /// Whether the configuration substitutes for a name in one module (`<-[M]`), where the frames
    /// of a predicate TLC fails to compute at startup, and checks in the search, aren't followed.
    pub(crate) is_scoped_substituted: bool,
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
            dfid: None,
            is_dumped: false,
            dumped: None,
            dot: None,
            dotted: None,
            ir,
            is_tool,
            is_plain,
            workers,
            startup_messages,
            startup_worded: Some(Vec::new()),
            assumed_worded: Vec::new(),
            failed_startup: Vec::new(),
            assumed_printed: Vec::new(),
            assumed_texts: None,
            startup_texts: None,
            undelegated: None,
            is_scoped_substituted: false,
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
        let failed_startup = &self.failed_startup;
        let texts = self.assumed_texts.get_or_insert_with(|| {
            // Each assumption's prints in turn, up to one the evaluator doesn't follow, as TLC
            // stops at an assumption that doesn't hold.
            let mut texts = Vec::new();
            for position in 0..ir.model.startup.assumptions.len() as u32 {
                let checked = Rebuilder::new(ir).and_then(|mut rebuilder| {
                    rebuilder.set_workers(workers);
                    rebuilder.set_searched_failing(failed_startup);
                    rebuilder.check_assumption(position, is_tool)
                });
                let Ok(checked) = checked else {
                    break;
                };
                texts.extend(checked.printed.iter().filter_map(|output| {
                    match crate::trace::format_output(output) {
                        crate::trace::PrintedOutput::Print(text) => Some(text),
                        _ => None,
                    }
                }));
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
        if continued.is_dfid {
            let report = headline.map_err(String::from).and_then(|headline| {
                if continued.holds_collapsed {
                    return Err("a value whose printed shape is not retained".into());
                }
                let states = continued
                    .states
                    .iter()
                    .map(|state| {
                        state
                            .iter()
                            .map(|&id| tla_trace::from_store(continued.store, id))
                            .collect::<Result<Vec<_>, _>>()
                            .map(|values| {
                                crate::trace::get_state_variables(ir, &values, self.is_plain)
                            })
                    })
                    .collect::<Result<Vec<_>, _>>()
                    .map_err(|_| "a state value that cannot be rendered")?;
                Ok(DfidContinuedReport {
                    code,
                    headline,
                    states,
                    is_initial,
                })
            });
            match report {
                Ok(report) => {
                    let _ = self.sender.send(Event::DfidContinued(Box::new(report)));
                }
                Err(reason) => {
                    self.is_declined = true;
                    let _ = self.sender.send(Event::Declined(format!(
                        "a DFID trace under -continue: {reason}"
                    )));
                }
            }
            return;
        }
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

    fn dfid_level(&mut self, level: u32, generated: u64, distinct: u64) {
        let _ = self
            .sender
            .send(Event::DfidLevel(level, generated, distinct));
        // As each level from 2 on starts, TLC's DFIDWorker allocates its stacks for every level
        // up to -dfid (`DFIDModelChecker.runTLC`): four arrays of that length, and a StateVec(1)
        // and a LongVec(1) for each level, over a hundred bytes a level, which deep enough runs
        // out of the JVM's heap. The search stops there, since past that point TLC prints nothing
        // the binary can follow, and an unbounded spec would never end.
        if self
            .dfid
            .is_some_and(|limit| u64::from(limit) > DFID_STACKS_MODELLED)
            && !self.is_declined
        {
            self.is_declined = true;
            let _ = self.sender.send(Event::Declined(
                "-dfid with stacks TLC may not have the memory for".to_owned(),
            ));
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

    fn liveness_started(&mut self, branches: u64, expanded: u64, states: u64, counts: [u64; 3]) {
        let [generated, distinct, depth] = counts;
        let statistics = Statistics {
            generated,
            distinct,
            queued: distinct.saturating_sub(expanded),
            depth,
        };
        let _ = self
            .sender
            .send(Event::LivenessStarted(branches, states, statistics));
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
        // TLC waits for a byte of its standard input after the prompt TLCSet("pause", TRUE)
        // prints (`System.in.read`), and goes on at its end.
        if prints.is_pause_prompt {
            let _ = std::io::Read::read(&mut std::io::stdin(), &mut [0u8; 1]);
        }
    }

    fn warning(&mut self, warning: &tla_engine::RuntimeWarning) {
        if self.startup_worded.is_none() {
            self.assumed_printed
                .push(crate::trace::PrintedOutput::Warning(warning.clone()));
        }
        let _ = self.sender.send(Event::Warning(warning.clone()));
    }

    // What the substitutes and constant definitions print, which the trace evaluator prints as
    // TLC built it where the store forgot, as long as it prints the same: each print the store
    // words alike, and as many.
    fn startup_print(&mut self, store: &Store, prints: &Prints) {
        let worded = format_printed(store, prints);
        let Some(worded_prints) = self.startup_worded.as_mut() else {
            let printed = self.word_assumed(worded);
            self.assumed_printed
                .extend(printed.clone().map(crate::trace::PrintedOutput::Print));
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
            let texts: Vec<String> = texts
                .iter()
                .filter_map(|output| match crate::trace::format_output(output) {
                    crate::trace::PrintedOutput::Print(text) => Some(text),
                    _ => None,
                })
                .collect();
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

    // TLC warns about each invariant whose value at startup is TRUE as it reads the
    // configuration, in its order, until it rejects a value (`processConfigInvariants`). It warns
    // about the state-level properties among the properties, which a rejected value past them
    // would follow.
    fn startup_predicates(&mut self, holding: &[bool]) {
        let ir = self.ir;
        // TLC reports an invariant it failed to compute as it starts in the search, with the
        // frames of the substitute.
        let is_invariant_failed = holding.iter().enumerate().any(|(position, holds)| {
            !holds
                && ir
                    .model
                    .startup
                    .predicates
                    .get(position)
                    .is_some_and(|predicate| &*ir.texts[predicate.kind as usize] == "invariant")
        });
        if self.is_scoped_substituted && is_invariant_failed {
            self.is_declined = true;
            let _ = self.sender.send(Event::Declined(
                "a predicate that fails at startup in a model the configuration substitutes for \
                 in a module"
                    .to_owned(),
            ));
            return;
        }
        let is_past_properties =
            ir.model
                .startup
                .predicates
                .get(holding.len())
                .is_some_and(|rejected| {
                    matches!(
                        &*ir.texts[rejected.kind as usize],
                        "property" | "constraint" | "action constraint" | "possible"
                    )
                });
        if is_past_properties
            && self
                .startup_messages
                .iter()
                .any(|message| message.code == code::STATE_LEVEL_PROPERTY)
        {
            self.is_declined = true;
            let _ = self.sender.send(Event::Declined(
                "a configuration error after the warnings about the state-level properties"
                    .to_owned(),
            ));
            return;
        }
        // What the symmetry's definition prints as TLC builds its `Tool`, after it printed its
        // warnings about the configuration, the engine reports with the constant definitions'
        // prints, before them.
        let is_symmetry_printing =
            self.ir
                .model
                .startup
                .symmetry
                .as_ref()
                .is_some_and(|symmetry| {
                    may_print(self.ir, self.ir.definitions[symmetry.definition as usize])
                });
        if is_symmetry_printing
            && self
                .startup_messages
                .iter()
                .any(|message| !matches!(message.code, 2212 | 2279))
        {
            self.is_declined = true;
            let _ = self.sender.send(Event::Declined(
                "warnings about the configuration before a symmetry that may print".to_owned(),
            ));
            return;
        }
        let (invariants, rest): (Vec<_>, Vec<_>) = self
            .startup_messages
            .drain(..)
            .partition(|message| message.code == code::CONSTANT_INVARIANT);
        self.startup_messages = rest;
        for message in invariants {
            let is_warned = match message.predicate {
                None => true,
                Some(position) => match holding.get(position) {
                    Some(holds) => *holds,
                    None => break,
                },
            };
            if is_warned {
                let _ = self.sender.send(Event::StartupMessage(message));
            }
        }
        // Where the configuration's predicates all hold, TLC has processed its configuration
        // (`SpecProcessor.processConfig`), and printed its warnings, before it builds its `Tool`:
        // the symmetry's warnings and exceptions, and `getActions`'s, follow them. The liveness
        // checker's messages come once the model checker is built.
        if holding.len() >= self.ir.model.startup.predicates.len() {
            let (configured, rest): (Vec<_>, Vec<_>) = self
                .startup_messages
                .drain(..)
                .partition(|message| !matches!(message.code, 2212 | 2279));
            self.startup_messages = rest;
            for message in configured {
                let _ = self.sender.send(Event::StartupMessage(message));
            }
        }
    }

    // The trace evaluator computes a startup print as TLC does, apart from the startup around it,
    // which the confirmation evaluates again (`confirm_startup`).
    fn computes_startup_print(&mut self, position: usize) -> Option<Vec<tla_ir::RuntimeWarning>> {
        if self.ir.model.startup.symmetry.is_some() {
            return None;
        }
        let mut rebuilder = Rebuilder::new(self.ir).ok()?;
        rebuilder.set_workers(self.workers);
        rebuilder.computes_startup_print(position)
    }

    // The trace evaluator computes a register probe the engine stopped at a limit of its own on as
    // TLC does as it starts, after the startup's definitions, and confirms it fails there before
    // any effect, with TLC's own error.
    fn fails_register_probe(&mut self, position: usize) -> bool {
        Rebuilder::new(self.ir).is_ok_and(|mut rebuilder| {
            rebuilder.set_workers(self.workers);
            rebuilder
                .confirm_failing_probe(position, self.is_tool)
                .is_ok()
        })
    }

    // The trace evaluator computes the startup as TLC does up to the definition the engine left to
    // it, and again past it: where it made as many prints before it as the engine did, from the
    // same generator's state, and computes it without a warning or a register's write, its prints
    // are TLC's there, which `startup_print` words, and its draws leave TLC's generator as the
    // evaluator's.
    fn computes_left_startup(
        &mut self,
        position: usize,
        printed: usize,
        random: u64,
    ) -> Option<LeftStartup> {
        if self.ir.model.startup.symmetry.is_some() {
            return None;
        }
        let compute = |count| {
            let mut rebuilder = Rebuilder::new(self.ir).ok()?;
            rebuilder.set_workers(self.workers);
            rebuilder.compute_startup_until(count).ok()
        };
        let before = compute(position)?;
        let after = compute(position + 1)?;
        (before.prints == printed
            && before.random == random
            && after.is_last_computed
            && after.warnings == before.warnings
            && after.writes == before.writes)
            .then(|| LeftStartup {
                prints: after.prints - before.prints,
                random: after.random,
            })
    }

    // The search swallowed each startup definition it found failing, as TLC does, which the trace
    // evaluator confirms TLC fails on too, whether or not anything reads the definition.
    // It confirms too that the trace evaluator computes each print the search couldn't compute.
    // A warning-only definition the search failed at a limit of its own the evaluator confirms
    // TLC computes, or fails on, as it starts without a warning or a print (`set_searched_limited`),
    // and one it failed on otherwise before any warning, where the evaluator words what TLC does
    // there (`set_searched_unwarned`).
    // Each failure it confirms it confirms after as many prints, and draws, as the search made
    // before it (`set_searched_effects`).
    fn confirm_startup(
        &mut self,
        failed: &[bool],
        unworded: &[bool],
        limited: &[bool],
        unwarned: &[bool],
        effects: &[(usize, bool)],
    ) -> Result<(), String> {
        self.failed_startup = failed.to_vec();
        if !failed.contains(&true)
            && !unworded.contains(&true)
            && !limited.contains(&true)
            && !unwarned.contains(&true)
        {
            return Ok(());
        }
        Rebuilder::new(self.ir)
            .and_then(|mut rebuilder| {
                rebuilder.set_workers(self.workers);
                rebuilder.set_searched_failing(failed);
                rebuilder.set_searched_effects(effects);
                rebuilder.set_searched_limited(limited);
                rebuilder.set_searched_unwarned(unwarned);
                rebuilder.set_searched_printed(
                    &effects
                        .iter()
                        .map(|&(printed, _)| printed)
                        .collect::<Vec<_>>(),
                );
                rebuilder.set_searched_unworded(unworded);
                rebuilder.confirm_startup()
            })
            .map_err(|Unsupported(reason)| format!("a startup definition that fails: {reason}"))
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
                rebuilder.set_searched_failing(&self.failed_startup);
                rebuilder.check_assumption(position, self.is_tool)
            })
            .map_err(|Unsupported(reason)| format!("checking an assumption again: {reason}"))?;
        // What the run printed of the assumption before it left it to the trace evaluator must be
        // what TLC prints first, after what the assumptions before it print.
        let expected: Vec<crate::trace::PrintedOutput> = checked
            .printed_before
            .iter()
            .chain(&checked.printed)
            .map(crate::trace::format_output)
            .collect();
        if !expected.starts_with(&self.assumed_printed) {
            self.send_print(None);
            return Err("printing other than TLC prints".into());
        }
        for text in &expected[self.assumed_printed.len()..] {
            self.assumed_printed.push(text.clone());
            match text {
                crate::trace::PrintedOutput::Print(text) => {
                    self.assumed_worded.push(Some(text.clone()));
                    self.send_print(Some(text.clone()));
                }
                crate::trace::PrintedOutput::Warning(warning) => {
                    let _ = self.sender.send(Event::Warning(warning.clone()));
                }
            }
        }
        Ok(Delegated {
            holds: checked.holds,
            random: checked.random,
        })
    }

    // The trace evaluator words TLC's messages, which AssertError compares, here of one whose
    // value is the same wherever TLC evaluates it.
    fn check_constant(&mut self, node: u32) -> Result<bool, String> {
        if let Some(reason) = self.undelegated {
            return Err(reason.into());
        }
        Rebuilder::new(self.ir)
            .and_then(|mut rebuilder| {
                rebuilder.set_workers(self.workers);
                rebuilder.set_searched_failing(&self.failed_startup);
                rebuilder.check_constant(node, self.is_tool)
            })
            .map_err(|Unsupported(reason)| format!("computing an AssertError: {reason}"))
    }

    fn symmetry_sets_too_small(&mut self, names: &[String]) {
        let _ = self
            .sender
            .send(Event::SymmetrySetsTooSmall(names.to_vec()));
    }

    fn undumped(&mut self, reason: &'static str) {
        if self.is_dumped {
            self.dumped = Some(Err(reason));
        }
    }

    fn undotted(&mut self, reason: &'static str) {
        if self.dot.is_some() {
            self.dotted = Some(Err(reason));
        }
    }

    fn dotted(&mut self, store: &Store, log: &tla_engine::search::DotLog) {
        let Some(options) = self.dot else {
            return;
        };
        let ir = self.ir;
        let names: Vec<String> = ir
            .model
            .actions
            .iter()
            .map(|action| ir.texts[action.name as usize].to_string())
            .collect();
        let mut state_text = |state: &[Id]| -> Result<String, &'static str> {
            if state.len() != ir.variables.len() {
                return Err("-dump dot of states other than the variables' values");
            }
            let texts = state
                .iter()
                .map(|&id| get_dumped_text(store, id))
                .collect::<Option<Vec<_>>>()
                .ok_or("dumping a value whose text depends on how TLC built it")?;
            Ok(format_texts(ir, &texts))
        };
        let dotted = crate::dot::format(log, &options, &names, &mut state_text);
        if let Ok(text) = &dotted {
            let _ = self.sender.send(Event::Dumped(text.clone()));
        }
        self.dotted = Some(dotted.map(|text| (text, !log.writes.is_empty())));
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
                    .map(|&id| get_dumped_text(store, id))
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

// TLC's text of a value of a state it dumps, which it fingerprinted first, normalizing it, where
// the store words it as TLC does.
fn get_dumped_text(store: &Store, id: Id) -> Option<String> {
    let mut text = Vec::new();
    is_printable_normalized(store, id)
        .then(|| write_value(store, id, &mut text).ok())
        .flatten()
        .and_then(|()| String::from_utf16(&text).ok())
}

// Why the binary doesn't write the graph `-dump dot` asks for as TLC does, if it doesn't.
fn decline_dot(ir: &tla_ir::Ir, dot: &DotOptions) -> Option<&'static str> {
    let model = &ir.model;
    if !model.live_formula.is_empty() {
        // TLC writes the behavior graphs too (`DotLivenessStateWriter`).
        return Some("-dump dot with temporal properties");
    }
    if model.alias.is_some() {
        return Some("-dump dot with an ALIAS");
    }
    if ir.variables.is_empty() {
        return Some("-dump dot of a spec without variables");
    }
    if dot.constrained {
        // TLC writes a step to each state a constraint leaves out, and to each it finds a
        // conjunct false of once every variable is assigned (`Tool.processUnsatisfied`).
        let is_free = model.constraints.is_empty()
            && model.action_constraints.is_empty()
            && model
                .next
                .is_some_and(|next| crate::dot::is_free_of_guards(ir, next));
        if !is_free {
            return Some("-dump dot,constrained of steps to states TLC leaves out");
        }
    }
    if dot.is_labelled() && model.actions.is_empty() {
        return Some("-dump dot labels of steps of no action of TLC's");
    }
    // `Action.getInvocationSignature` writes the values of the action's parameters too.
    let is_parameterized = model.actions.iter().any(|action| {
        action.scope.is_some()
            || action.definition.is_some_and(|definition| {
                let node = ir.definitions[definition as usize];
                matches!(&ir.nodes.arena[node as usize].kind,
                    tla_ir::NodeKind::Definition(definition)
                        if !matches!(&definition.form,
                            tla_ir::DefinitionForm::Operator(params) if params.is_empty()))
            })
    });
    if dot.action_labels && is_parameterized {
        return Some("-dump dot,actionlabels of an action with parameters");
    }
    None
}

// The trace evaluator's computation of a constant definition TLC computes as it starts, which the
// engine failed on (`Settings::adopter`): TLC keeps its value, a boolean it computes without an
// effect or a warning, and every use reads it. The evaluator recurses, so it runs with the
// search's stack.
fn get_adopter(ir: &Arc<tla_ir::Ir>, workers: usize, is_tool: bool) -> tla_engine::search::Adopter {
    let ir = Arc::clone(ir);
    tla_engine::search::Adopter(Arc::new(move |index| {
        on_search_stack(|| {
            let mut rebuilder = Rebuilder::new(&ir).ok()?;
            rebuilder.set_workers(workers);
            rebuilder.compute_constant_definition(index, is_tool).ok()
        })
    }))
}

// What Print or PrintT prints of the values: TLC's text of each that the engine knew, or that the
// store words, unless the store has forgotten how TLC built one.
fn format_printed(store: &Store, prints: &Prints) -> Option<String> {
    // Only the trace evaluator words a print the search couldn't compute.
    if prints.is_unworded() {
        return None;
    }
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

// What TLC prints as it adds the state it stopped at to the behavior graphs, where the search
// placed it.
fn format_added(violation: &Violation) -> Result<Vec<String>, &'static str> {
    violation
        .added
        .iter()
        .flatten()
        .map(|prints| format_printed(&violation.store, prints))
        .collect::<Option<Vec<_>>>()
        .ok_or("printing a value whose text depends on how TLC built it")
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
    main_file: &str,
    args: &Parsed,
    java: &Java,
    is_java_launch: bool,
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
    let dfid = args
        .first("-dfid")
        .and_then(|value| value.parse::<u32>().ok());
    if dfid.is_some() && args.has("-coverage") {
        return report_not_native(printer, "DFID with coverage");
    }
    let simulation = get_simulation(args);
    if dfid.is_some() && simulation.is_some() {
        return report_not_native(printer, "DFID with simulation");
    }
    // TLC's simulator also prints a coverage report, which the coverage pass, a replay of the
    // model checker's search, doesn't count.
    if args.has("-coverage") && simulation.is_some() {
        return report_not_native(printer, "coverage of a simulation");
    }
    // -difftrace changes how TLC prints a trace, which the binary follows for the model
    // checker's traces alone: the simulator also leaves out stuttering steps, DFID diffs the
    // last state too, and -dump dot labels its edges with the diffs.
    if args.has("-difftrace") {
        let why = if simulation.is_some() {
            Some("-difftrace in a simulation")
        } else if dfid.is_some() {
            Some("-difftrace with DFID")
        } else if dump.is_some_and(|dump| dump.len() > 1) {
            Some("-difftrace with -dump dot")
        } else {
            None
        };
        if let Some(why) = why {
            return report_not_native(printer, why);
        }
    }
    // TLC opens the file once it has read its options, before it says which version it is and
    // recovers, and names it with a suffix of .dump, or .dot for a graph, unless it has one.
    // It reports one it can't open (`FileUtil.newBFOS`), with its name after `${metadir}` is
    // replaced, a path the binary doesn't make.
    let recover = args.first("-recover");
    if recover.is_some() && dump.is_some() {
        return report_not_native(printer, "-recover with -dump");
    }
    // `-dump dot,...` writes the state graph (`DotStateWriter`), with the options its word holds.
    let dot = match dump {
        Some([word, _]) => Some(DotOptions::parse(word)),
        _ => None,
    };
    let dump = match dump {
        None => None,
        Some([.., file]) if file.starts_with("${metadir}") => {
            return report_not_native(printer, "-dump into the meta directory");
        }
        Some(values) => {
            let (file, suffix) = match values {
                [file] => (file, ".dump"),
                [_, file] => (file, ".dot"),
                _ => return report_not_native(printer, "-dump"),
            };
            let path = if file.ends_with(suffix) {
                file.clone()
            } else {
                format!("{file}{suffix}")
            };
            // The library's host answers for files alone, and has no directory to tell.
            let is_unopenable = !printer.host.is_plain()
                && (!crate::host::is_directory_there(printer.host, Path::new(&path))
                    || printer.host.kind(Path::new(&path)) == crate::host::FileKind::Directory);
            if is_unopenable {
                printer.line(&format!("Error: Unable to write to file {path}"));
                return print_command_line_error(
                    printer,
                    &format!("Error: Given file name {path} for dumping states invalid."),
                );
            }
            if let [word, _] = values {
                // TLC's workers, its depth-first search and its simulator write the graph in
                // orders of their own.
                let why = if workers > 1 {
                    Some("-dump dot with several workers")
                } else if dfid.is_some() {
                    Some("-dump dot with -dfid")
                } else if simulation.is_some() {
                    Some("-dump dot in a simulation")
                } else if DotOptions::parse(word).snapshot && path.matches(".dot").count() > 1 {
                    // TLC names the snapshot by replacing every ".dot" of the path.
                    Some("-dump dot,snapshot into a path with .dot before its suffix")
                } else {
                    None
                };
                if let Some(why) = why {
                    return report_not_native(printer, why);
                }
            }
            // A run that declines later, as a search can, puts the file back as it found it
            // (`tla_values::written::restore`). The journal keeps a file it can read whole, of
            // at most `KEPT_DUMP_BYTES`; another it truncates as TLC does and leaves so on a
            // decline, as main did, but under -dfid, which main declined before it opened any
            // file, where it declines first.
            const KEPT_DUMP_BYTES: u64 = 64 << 20;
            if printer.host.is_file_system() {
                let is_keepable = std::fs::metadata(&path)
                    .map_or(true, |metadata| metadata.len() <= KEPT_DUMP_BYTES);
                let is_kept =
                    is_keepable && tla_values::written::keep_file(Path::new(&path)).is_ok();
                if !is_kept && dfid.is_some() {
                    return report_not_native(
                        printer,
                        "-dfid with -dump into a file it can't keep",
                    );
                }
            }
            if !printer.host.write_file(Path::new(&path), b"", false) {
                return report_not_native(printer, "-dump into a file it can't create");
            }
            Some(path)
        }
    };
    print_welcome(printer);
    // TLC reads the checkpoint's intern table first, before its banner
    // (`UniqueString.internTbl.recover`), from `<directory>/vars.chkpt`, a path java.io.File
    // normalizes; the binary recovers from none, and reports why it can't read the file.
    // The exception escapes into `TLC.process`'s catch, whose finally block still prints
    // EC.TLC_FINISHED.
    if let Some(directory) = recover {
        let start = Instant::now();
        let path = tla_values::java_file_path(&format!("{directory}//vars.chkpt"));
        let reason = match printer.host.platform() {
            Platform::Unix => printer.host.open_failure(Path::new(&path), false),
            Platform::Windows => None,
        };
        let Some(reason) = reason else {
            return report_not_native(printer, "-recover from a checkpoint");
        };
        printer.report(
            code::GENERAL,
            &format!(
                "{}java.io.FileNotFoundException\n: {path} ({reason})",
                tla_front::errors::UNEXPECTED_HEAD
            ),
        );
        print_finished(printer, start);
        return crate::failure::ERROR;
    }
    match &simulation {
        Some(simulation) => print_banner(printer, simulation.seed, workers),
        None => print_startup_banner(printer, fingerprint_index, seed, workers, dfid.is_some()),
    }
    let directories = get_module_directories(printer.host.platform(), main_file, &java.libraries);
    let config_path = match find_config(
        printer.host,
        args.first("-config"),
        main_file,
        &directories,
        TlcVersion::Master,
    ) {
        Config::Found(path) => path,
        Config::NotNative(what) => return report_not_native(printer, what),
        Config::Missing(name) => {
            printer.print(
                code::CONFIG_FILE_ERROR,
                Level::Error,
                &format!(
                    "TLC encountered the following error when trying to read the configuration file {name}:\nFile not found."
                ),
            );
            return CONFIG_PARSE_ERROR;
        }
    };
    let embedded_name =
        crate::resolve::config_name(printer.host.platform(), args.first("-config"), main_file);
    if embedded_name.ends_with(".tla") && workers > 1 {
        return report_not_native(
            printer,
            "a configuration in a module's CONFIG section, which TLC reads from a -config ending in .tla",
        );
    }
    let start = Instant::now();
    // TLC reads the configuration file before it parses the spec, and reports one it can't parse
    // as it reports a TlaConfigError (`printFailure`).
    let config_text = printer.host.read_text(&config_path).map(|text| {
        if embedded_name.ends_with(".tla") {
            embedded_config(&text, &embedded_name.replace(".tla", ""))
        } else {
            text
        }
    });
    // The command line's postconditions, `module!operator`: TLC adds each module to the root
    // module's EXTENDS (`ParameterizedSpecObj`) and checks each operator before the
    // configuration's POSTCONDITIONs, along with -dumpTrace's and the trace exploration spec's
    // in their order (`Spec.getPostConditionSpecs`). The binary checks them as POSTCONDITIONs
    // where they are the only ones.
    let post_conditions: Vec<(&str, &str)> = args
        .options
        .iter()
        .filter(|(option, _)| option == crate::args::POST_CONDITION)
        .map(|(_, values)| (values[0].as_str(), values[1].as_str()))
        .collect();
    let mut config_text = config_text;
    if !post_conditions.is_empty() {
        let is_name = |text: &str| {
            text.bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
                && text.bytes().any(|byte| byte.is_ascii_alphabetic())
        };
        let why = if dfid.is_some() || simulation.is_some() {
            Some("-postCondition in DFID or a simulation")
        } else if args.has(crate::args::DUMP_TRACE)
            || is_trace_recorded(args, spec_path, printer.host.platform())
        {
            Some("-postCondition beside the trace modules' postconditions")
        } else if post_conditions
            .iter()
            .any(|(module, def)| !is_name(module) || !is_name(def) || module.starts_with('_'))
        {
            Some("-postCondition of a name the configuration doesn't spell")
        } else if post_conditions
            .iter()
            .enumerate()
            .any(|(index, (module, _))| {
                post_conditions[..index]
                    .iter()
                    .any(|(other, _)| other == module)
            })
        {
            Some("-postCondition of a module twice")
        } else {
            match config_text
                .as_deref()
                .map(|text| parse_config(text, TlcVersion::Master))
            {
                Some(Ok(config)) if config.postconditions.is_empty() => None,
                Some(Ok(_)) => Some("-postCondition beside a POSTCONDITION"),
                _ => None,
            }
        };
        if let Some(why) = why {
            return report_not_native(printer, why);
        }
        if let Some(Ok(_)) = config_text
            .as_deref()
            .map(|text| parse_config(text, TlcVersion::Master))
        {
            let text = config_text.take().unwrap_or_default();
            config_text = Some(post_conditions.iter().fold(text, |text, (_, def)| {
                format!("{text}\nPOSTCONDITION {def}\n")
            }));
        }
    }
    // The command line's invariants (`-inv`, `-invlevel`): TLC parses each expression as
    // `__DebuggerExpr__<millis> == expr` on the fourth line of a module
    // `__DebuggerModule__<millis>` that extends the root module (`TLCDebuggerExpression.process`),
    // and checks it after the configuration's invariants. The binary lowers each definition at
    // the end of the root module, where it reads what the module of TLC's would, unless the root
    // module has a LOCAL definition, and moves it to TLC's module and line once it is lowered.
    let invariants: Vec<&[String]> = args
        .options
        .iter()
        .filter(|(option, _)| option == crate::args::INVARIANT)
        .map(|(_, values)| values.as_slice())
        .collect();
    let mut appended = String::new();
    let mut debugger_modules = Vec::new();
    let mut invariant_extendees: Vec<&str> = Vec::new();
    let mut invariant_syntax_error = None;
    let mut original_config_text = None;
    if !invariants.is_empty() {
        let source = printer
            .host
            .read_text(Path::new(spec_path))
            .unwrap_or_default();
        let is_identifier = |text: &str| {
            text.bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
        };
        let why = if dfid.is_some() || simulation.is_some() {
            Some("-inv in DFID or a simulation")
        } else if args.has(crate::args::DUMP_TRACE)
            || is_trace_spec_written(args, spec_path, printer.host.platform())
            || args.has("-coverage")
        {
            Some("-inv with -dumpTrace, -coverage or the trace exploration spec")
        } else if source.contains("LOCAL") || source.contains("__Debugger") {
            Some("-inv of a root module with LOCAL definitions")
        } else if invariants.iter().any(|values| {
            values[0].contains(['\n', '\r'])
                || is_identifier(values[0].trim())
                || values[0].trim().is_empty()
                || values.len() > 2 && values[1] != "TLC"
        }) {
            Some("-inv of a definition's name, of several lines or of several modules")
        } else {
            None
        };
        if let Some(why) = why {
            return report_not_native(printer, why);
        }
        let millis = printer
            .host
            .now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_or(0, |since| since.as_millis());
        for (position, values) in invariants.iter().enumerate() {
            let stamp = millis + position as u128;
            let name = format!("__DebuggerExpr__{stamp}");
            let module = format!("__DebuggerModule__{stamp}");
            let expression = &values[0];
            let root = main_file.rsplit('/').next().unwrap_or(main_file);
            let text = format!(
                "---- MODULE {module} ----\nEXTENDS {root}\n\n{name} == {expression}\n===="
            );
            let is_parsed = tla_front::lexer::tokenize(&text).is_ok_and(|tokens| {
                tla_front::parser::parse_module_tokens(&text, &tokens, TlcVersion::Master).is_ok()
            });
            if !is_parsed {
                invariant_syntax_error.get_or_insert_with(|| {
                    format!("Syntax error while parsing breakpoint expression \"{expression}\"")
                });
            }
            appended.push_str(&format!("{name} == {expression}\n"));
            debugger_modules.push((name, module));
            for module in &values[1..] {
                if !invariant_extendees.contains(&module.as_str()) {
                    invariant_extendees.push(module);
                }
            }
        }
        original_config_text = config_text.clone();
        if invariant_syntax_error.is_some() {
            appended.clear();
        } else if let Some(text) = config_text.take() {
            config_text = Some(debugger_modules.iter().fold(text, |text, (name, _)| {
                format!("{text}\nINVARIANT {name}\n")
            }));
        }
    }
    // A root module that extends one of TLC's trace modules and names its postcondition in the
    // configuration, with the module's two constants (`EXTENDS _JsonTrace`, `POSTCONDITION
    // _JsonTrace`, `CONSTANT _JsonTraceFile = "trace.json"`), checks the postcondition -dumpTrace
    // adds: the binary writes the counterexample to the file as it does for -dumpTrace, and links
    // the module's constants into the root module's scope.
    let mut extended_dump = None;
    let root_source = printer
        .host
        .read_text(Path::new(spec_path))
        .unwrap_or_default();
    let extended_traces: Vec<String> = tla_front::model::get_root_extends(&root_source)
        .into_iter()
        .filter(|name| name == "_JsonTrace" || name == tla_front::model::TRACE_MODULE)
        .collect();
    if let Some(module) = extended_traces.first() {
        if extended_traces.len() > 1
            || args.has(crate::args::DUMP_TRACE)
            || !post_conditions.is_empty()
            || !invariants.is_empty()
            || dfid.is_some()
            || simulation.is_some()
            || is_trace_spec_written(args, spec_path, printer.host.platform())
        {
            return report_not_native(
                printer,
                "a spec that extends a trace module, beside -dumpTrace, -postCondition, -inv, \
                 -dfid, -simulate or the trace exploration spec",
            );
        }
        let file = config_text
            .as_deref()
            .and_then(|text| parse_config(text, TlcVersion::Master).ok())
            .filter(|config| config.postconditions == [module.clone()])
            .and_then(|config| {
                let assigned = |suffix: &str| {
                    let name = format!("{module}{suffix}");
                    config
                        .constants
                        .iter()
                        .find(|assignment| assignment.name == name && assignment.module.is_none())
                        .filter(|assignment| assignment.args.is_none())
                        .map(|assignment| assignment.value.clone())
                };
                assigned("InputFile")?;
                match assigned("File")? {
                    tla_front::config::ConfigValue::String(file) => Some(file),
                    _ => None,
                }
            });
        let line = format!("POSTCONDITION {module}");
        let lines: Vec<&str> = config_text.as_deref().unwrap_or_default().lines().collect();
        let positions: Vec<usize> = (lines.iter().enumerate())
            .filter(|(_, text)| text.trim() == line)
            .map(|(position, _)| position)
            .collect();
        let (Some(file), [position]) = (file, positions.as_slice()) else {
            return report_not_native(
                printer,
                "a spec that extends a trace module whose postcondition and constants the \
                 configuration doesn't name as -dumpTrace does",
            );
        };
        let mut kept = lines.clone();
        kept.remove(*position);
        config_text = Some(kept.join("\n") + "\n");
        extended_dump = Some((module == "_JsonTrace", file));
    }
    let parsed = config_text
        .as_deref()
        .map(|text| parse_config(text, TlcVersion::Master));
    let config = match parsed {
        Some(Ok(config)) => config,
        Some(Err(error)) => {
            if let Some(reason) = error.unworded {
                return report_not_native(printer, reason);
            }
            let message = error.message;
            let Some(coded) = FrontError::Config(message.clone()).get_coded(printer.is_tool) else {
                return report_not_native(printer, "a configuration file the front end rejects");
            };
            // An exception TLC didn't expect, such as the NumberFormatException of a number past
            // its integers, is no TlaConfigError, so the library has no error of TLC's to throw.
            if !message.starts_with(tla_front::errors::UNEXPECTED_HEAD) {
                printer.set_thrown(Some(Thrown::Config(message)));
            }
            return print_coded_failure(printer, &coded, start);
        }
        None => return report_not_native(printer, "a configuration file the front end rejects"),
    };
    // -view prints a state as the value of the VIEW (`TLCStateMut.toString`), which changes
    // nothing without one.
    if args.has("-view") && config.view.is_some() {
        return report_not_native(printer, "-view with a VIEW");
    }
    let te_spec_out = args.first("-teSpecOutDir");
    // TLC makes the directory -teSpecOutDir names as it writes the spec, after `_TLCTrace` failed
    // to write the trace's file into it.
    if let Some(out) = te_spec_out
        && is_trace_spec_written(args, spec_path, printer.host.platform())
    {
        let (directory, _, name) = te_spec::get_files_place(main_file, started, Some(out));
        if !te_spec::is_modelled_out(out) {
            return report_not_native(printer, "-teSpecOutDir of a path the binary doesn't model");
        }
        if printer.host.kind(Path::new(&directory)) != crate::host::FileKind::Directory
            && is_trace_recorded(args, spec_path, printer.host.platform())
        {
            printer.unplaced_trace_file =
                Some(te_spec::join_place(&directory, &format!("{name}.bin")));
        }
    }
    let mut dumps = TraceDumps::new(
        args,
        &config,
        is_trace_recorded(args, spec_path, printer.host.platform()),
        Some({
            let (directory, _, name) = te_spec::get_files_place(main_file, started, te_spec_out);
            te_spec::join_place(&directory, &format!("{name}.bin"))
        }),
    );
    if let Some((is_json, file)) = extended_dump {
        dumps.add_extended(is_json, file);
    }
    // The files the run may write after the search: the trace exploration spec and each dump.
    if is_trace_spec_written(args, spec_path, printer.host.platform()) {
        let (directory, _, name) = te_spec::get_files_place(main_file, started, te_spec_out);
        let path = te_spec::join_place(&directory, &format!("{name}.tla"));
        printer.host.prepare_write(Path::new(&path));
        // Where -teSpecOutDir names the directory, whether it is there, asked before the search
        // as the files it writes are (the spec's own directory is).
        if te_spec_out.is_some()
            && let Some((directory, _)) = path.rsplit_once('/')
            && !directory.is_empty()
            && printer.host.kind(Path::new(directory)) == crate::host::FileKind::Absent
        {
            printer.absent_trace_spec_directory = Some(directory.to_string());
        }
    }
    for path in dumps.get_paths() {
        printer.host.prepare_write(Path::new(path));
    }
    let read = |config_text: &str, appended: &str| {
        read_front(
            spec_path,
            config_text,
            !args.has("-nowarning"),
            &Files {
                parent_runtime: printer.host.modeled_parent_runtime(is_java_launch),
                java_profile: java.origin_profile(
                    java.class_path
                        .as_deref()
                        .and_then(|path| get_tools_jar(path, printer.host.platform())),
                ),
                spec: Path::new(spec_path),
                main_file,
                directories: &directories,
                temporary: java.temporary_directory.as_deref(),
                metadir: args.first("-metadir"),
                jar: java
                    .class_path
                    .as_deref()
                    .and_then(|class_path| get_tools_jar(class_path, printer.host.platform())),
                is_174: false,
                root_extendees: &post_conditions
                    .iter()
                    .map(|(module, _)| *module)
                    .chain(dumps.get_root_extendees())
                    .chain(invariant_extendees.iter().copied())
                    .collect::<Vec<_>>(),
                appended,
                lint_codes: tla_front::report::LintCodes {
                    is_suppressed: args
                        .get_sany_codes("-suppressMessages")
                        .contains(&tla_front::report::RECORD_FIELD_NAME_CLASH),
                    is_elevated: args
                        .get_sany_codes("-messagesAsErrors")
                        .contains(&tla_front::report::RECORD_FIELD_NAME_CLASH),
                },
            },
            printer.host,
            printer.is_tool,
            seed,
        )
    };
    let mut read_result = read(config_text.as_deref().unwrap_or_default(), &appended);
    // A command-line invariant SANY's generator rejects, which TLC reports as it processes the
    // configuration, as it does one that fails to parse: the run goes on reading the spec without
    // the invariants for what TLC computed before.
    if let Ok(Read::UnknownInInvariant(position)) = &read_result {
        if invariants.len() != 1 {
            return report_not_native(
                printer,
                "-inv of several expressions, one of which SANY rejects",
            );
        }
        invariant_syntax_error = Some(format!(
            "Unknown location\n\nSemantic error while parsing breakpoint expression \"{}\"",
            invariants[*position][0]
        ));
        appended.clear();
        read_result = read(original_config_text.as_deref().unwrap_or_default(), "");
    }
    // TLC fails the command-line invariants in `processConfig` before it processes the
    // constraints, the RL reward and periodic operators and the possible predicates, and before
    // it reads the SYMMETRY and VIEW (`getInvariants`, then `processModelConstraints`,
    // `processActionConstraints`, `processRLReward`, `processPeriodic`, `processConfigPossible`).
    // The front end doesn't say which of its checks failed, so with any of them named, a failure
    // past SANY's declines but for those TLC reports as it reads the configuration's constants or
    // processes its specification and properties (`processConstants`, `processConfigInitAndNext`,
    // `processConfigSpec`, `processConfig`).
    let is_before_invariants = |coded: &CodedError| {
        coded.code == 2222
            || coded
                .text
                .starts_with("The configuration file did not specify the ")
            || coded.code == 2229
                && [
                    "The initial predicate ",
                    "The next state action ",
                    "The name ",
                    "The property ",
                    "The invariant ",
                ]
                .iter()
                .any(|kind| coded.text.starts_with(kind))
            // The specification's or a property's arity, which TLC words without the kind it
            // words a constraint's with.
            || coded.code == 2228 && !coded.text.contains(", but one was given: ")
    };
    if invariant_syntax_error.is_some()
        && matches!(&read_result, Ok(Read::Failed(failure))
            if failure.error.as_ref().is_some_and(|coded| !is_before_invariants(coded)))
        && original_config_text
            .as_deref()
            .and_then(|text| parse_config(text, TlcVersion::Master).ok())
            .is_some_and(|config| {
                !config.constraints.is_empty()
                    || !config.action_constraints.is_empty()
                    || !config.possible.is_empty()
                    || config.rl_reward.is_some()
                    || config.periodic.is_some()
                    || config.symmetry.is_some()
                    || config.view.is_some()
            })
    {
        return report_not_native(
            printer,
            "-inv of an expression that fails to parse, with a configuration failure TLC may report after it",
        );
    }
    let front = match read_result {
        Ok(Read::Model(front)) => front,
        // Where the root module SANY accepted fails with the invariants' definitions, they fail
        // as TLC parses them in their own module, which the binary doesn't word.
        Ok(Read::UnknownInInvariant(_)) => {
            return report_not_native(printer, "-inv of an expression that fails to parse");
        }
        Ok(Read::Failed(_)) if !appended.is_empty() => {
            return report_not_native(printer, "-inv of an expression that fails to parse");
        }
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
        Ok(Read::Failed(failure))
            if dfid.is_some()
                && failure
                    .error
                    .as_ref()
                    .is_some_and(|coded| coded.code == 2253) =>
        {
            return report_not_native(
                printer,
                "DFID liveness constructor error before a tautology",
            );
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
    // TLC reports again each Java override it loaded as it processes each invariant of the
    // command line: `TLCDebuggerExpression.process` runs `processModuleOverrides` over every
    // module once more for the module it makes, after the constant definitions, which the
    // binary doesn't follow.
    if !invariants.is_empty() && !front.override_messages.is_empty() {
        return report_not_native(printer, "-inv beside a Java override TLC loads");
    }
    // TLC reports an invariant of the command line that doesn't parse as it processes the
    // configuration, after SANY and after it computed the constant definitions
    // (`SpecProcessor.processSpec`, `Assert.fail(EC.TLC_PARSING_FAILED2, e)`).
    if let Some(error) = &invariant_syntax_error {
        let Some(sany) = &front.sany else {
            return report_not_native(printer, "-inv of an expression that fails to parse");
        };
        if !front.startup_messages.is_empty()
            || !front.override_messages.is_empty()
            || !ir.model.startup.definitions.is_empty()
        {
            return report_not_native(
                printer,
                "-inv of an expression that fails to parse, after the constant definitions",
            );
        }
        print_sany(printer, sany);
        let message = format!("Parsing or semantic analysis failed.{error}");
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
    // Each invariant's definition, at the root module's end, moves to the fourth line of TLC's
    // module of its own.
    if !debugger_modules.is_empty() {
        let source = printer
            .host
            .read_text(Path::new(spec_path))
            .unwrap_or_default();
        let normalized = tla_front::report::end_lines_at_carriage_returns(&source);
        let Some((_, first_line)) = crate::front::insert_before_module_end(&normalized, &appended)
        else {
            return report_not_native(
                printer,
                "-inv in a module whose end the binary doesn't place",
            );
        };
        let root = ir
            .texts
            .iter()
            .position(|text| **text == *main_file.rsplit('/').next().unwrap_or(main_file));
        let modules: Vec<u32> = debugger_modules
            .iter()
            .map(|(_, module)| {
                ir.texts.push(module.as_str().into());
                (ir.texts.len() - 1) as u32
            })
            .collect();
        for node in &mut ir.nodes.arena {
            let Some(range) = node.range.as_mut() else {
                continue;
            };
            let offset = range.start_line - first_line as i32;
            if Some(range.module as usize) != root || offset < 0 || offset as usize >= modules.len()
            {
                continue;
            }
            if range.end_line != range.start_line {
                return report_not_native(printer, "-inv of an expression the IR spreads");
            }
            range.module = modules[offset as usize];
            range.start_line = 4;
            range.end_line = 4;
            node.line = 4;
        }
    }
    // The front end gives a spec without variables FALSE for Init and Next, whether or not the
    // configuration names a next-state relation, but DFIDModelChecker reports success right after
    // the initial states only where TLC has no action (`getActions().length == 0`).
    if dfid.is_some() && ir.variables.is_empty() {
        return report_not_native(printer, "DFID of a spec without variables");
    }
    // DFIDModelChecker keeps no worker of its own in `workers` before it searches, which
    // TLCGetOrDefault, as _Track applies it, then fails to read.
    if dfid.is_some()
        && ir
            .builtins
            .iter()
            .any(|builtin| &*ir.texts[builtin.name as usize] == "_Track")
    {
        return report_not_native(printer, "DFID of a spec that applies _Track");
    }
    // -terse keeps TLC from expanding a value it keeps lazy as it prints it (`TLCGlobals.expand`),
    // which changes nothing where the spec builds no such value.
    if args.has("-terse") && may_build_lazy_value(&ir) {
        return report_not_native(printer, "-terse with a value TLC may keep lazy");
    }
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
    // assigns it as a constant or it names a builtin, such as an operator a Java override
    // implements, which TLC holds as a value, or one of the others.
    let is_alias_undefined_unsure = ir.model.alias.as_ref().is_some_and(|alias| {
        let name = &*ir.texts[alias.name as usize];
        alias.definition.is_none()
            && (front.sany.is_none()
                || front.defined_names.iter().any(|defined| **defined == *name)
                || ["TRUE", "FALSE", "BOOLEAN", "STRING"].contains(&name)
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
        let Some(definition) = postcondition.definition else {
            // One TLC doesn't find is rejected below, but not under DFID.
            return dfid.is_some();
        };
        match &ir.nodes.arena[ir.definitions[definition as usize] as usize].kind {
            tla_ir::NodeKind::Definition(definition) => {
                ir.nodes.arena[definition.body as usize].range.is_none()
            }
            _ => true,
        }
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
    // TLC finds a command line's postcondition among its module's definitions
    // (`moduleNode.getOpDef`), and evaluates its body with no arguments bound: the binary
    // follows one the root module's scope finds there, without parameters.
    let is_post_condition_unfound =
        post_conditions
            .iter()
            .zip(&ir.model.postconditions)
            .any(|((module, _), postcondition)| {
                postcondition.definition.is_none_or(|definition| {
                    let node = &ir.nodes.arena[ir.definitions[definition as usize] as usize];
                    takes_arguments(definition)
                        || node
                            .range
                            .is_none_or(|range| &*ir.texts[range.module as usize] != *module)
                })
            });
    if is_post_condition_unfound || ir.model.postconditions.len() < post_conditions.len() {
        return report_not_native(printer, "a -postCondition operator TLC may find otherwise");
    }
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
    for (position, postcondition) in ir
        .model
        .postconditions
        .iter()
        .enumerate()
        .filter(|_| dfid.is_none())
    {
        let name = &ir.texts[postcondition.name as usize];
        // TLC evaluates a command line's postcondition's body even where it computed the
        // definition as it started (`ParameterizedSpecObj.getPostConditionSpecs`).
        let is_command_line = position < post_conditions.len();
        // TLC looks a POSTCONDITION up among the definitions, the constants and TRUE, FALSE,
        // BOOLEAN and STRING (`Spec.getPostConditionSpecs`), as it does an ALIAS. Where the IR
        // has no definition of it, the binary reports it as one TLC doesn't find but where it
        // names a variable, a constant, a substitution, a builtin such as an operator a Java
        // override implements, or one of the others.
        let Some(definition) = postcondition.definition else {
            let is_unsure = front.sany.is_none()
                || front
                    .defined_names
                    .iter()
                    .any(|defined| **defined == **name)
                || ["TRUE", "FALSE", "BOOLEAN", "STRING"].contains(&&**name)
                || config
                    .constants
                    .iter()
                    .any(|constant| *constant.name == **name)
                || config
                    .substitutions
                    .iter()
                    .any(|substitution| *substitution.name == **name)
                || ir
                    .variables
                    .iter()
                    .any(|&variable| ir.texts[variable as usize] == *name);
            if is_unsure {
                return report_not_native(printer, "a POSTCONDITION TLC may not find");
            }
            rejected_postcondition = Some((
                format!(
                    "The post condition {name} specified in the configuration file\nis not defined in the specification."
                ),
                code::CONFIG_SPECIFIED_NOT_DEFINED,
            ));
            break;
        };
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
            Ok(true) if is_command_line => {}
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
    let is_sany_warned = front.is_sany_warned;
    let is_tlcext_declined = front.is_tlcext_declined;
    printer.alias_decline = front.alias_decline.clone();
    printer.made_paths = get_made_paths(args, spec_path, &dumps, printer.host);
    if let Some(sany) = &front.sany {
        print_sany(printer, sany);
        printer.is_trace_recorded = is_trace_recorded(args, spec_path, printer.host.platform());
        if is_trace_spec_written(args, spec_path, printer.host.platform()) {
            printer.trace_spec = Some(TraceSpec::new(
                main_file,
                te_spec::get_files_place(main_file, started, te_spec_out),
                &ir,
                &config,
                &front.defined_names,
                fingerprint_index,
                is_trace_recorded(args, spec_path, printer.host.platform()),
            ));
        }
    } else {
        dumps.leave_out_trace_file();
    }
    // TLC loads the classes of the modules before it computes the constant definitions.
    if printer.host.is_plain() {
        printer.outcome.sany_warnings = front.sany_warnings.clone();
    }
    for message in &front.override_messages {
        print_startup_message(printer, message);
    }
    // TLC seeds its generator with -seed, which an IR tla-front lowers doesn't hold.
    ir.model.random_seed = seed as u64;
    ir.model.fingerprint_index = fingerprint_index;
    // The root module's name is the spec file's, as SANY requires.
    ir.model.root_module_name = Path::new(spec_path)
        .file_stem()
        .and_then(|stem| stem.to_str())
        .and_then(|stem| {
            ir.texts[..(ir.ranked_count as usize).min(ir.texts.len())]
                .iter()
                .position(|text| &**text == stem)
        })
        .map(|position| position as tla_ir::TextId);
    if args.has("-deadlock") {
        ir.model.check_deadlock = false;
    }
    // The front end evaluates nothing, so the IR it lowers has none of TLC's actions, which the
    // trace evaluator finds as check.ts does. A model it can't split keeps none, and its traces
    // name no actions natively. The evaluator recurses, so it runs with the search's stack.
    if ir.model.actions.is_empty() {
        match on_search_stack(|| tla_trace::add_actions(&ir)) {
            Ok(split) => ir = split,
            // TLC evaluates an \E's bound in its split of the next-state relation once, as it
            // starts (`Tool.getActions`), with its prints, draws and registers, which the engine,
            // taking the relation whole, would have at each state instead.
            Err(tla_trace::Unsupported(reason)) if reason == tla_trace::SPLIT_BOUND_EFFECTS => {
                return report_not_native(printer, &reason);
            }
            Err(_) => {}
        }
    }
    if let Some(dot) = &dot {
        if let Some(why) = decline_dot(&ir, dot) {
            return report_not_native(printer, why);
        }
        // An edge that names or colors its action is a step the search takes through TLC's
        // actions, in their order, as TLC's `getNextStates` takes them.
        ir.model.is_labelled |= dot.is_labelled();
    }
    // Shared with the engine's computation of a constant definition it fails on
    // (`Settings::adopter`).
    let ir = Arc::new(ir);
    if let Some(mut simulation) = simulation {
        simulation.initial_action =
            crate::simulation::get_initial_action(&ir, front.initial_action.as_ref());
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
    let lncheck = args.first("-lncheck").map(|check| check.to_lowercase());
    let is_liveness_periodic = !lncheck
        .as_deref()
        .is_some_and(|check| ["final", "seqfinal", "off"].contains(&check));
    // With off, TLC skips the check on the complete state graph too (`LiveCheck.finalCheck`): it
    // still adds each state to the behavior graphs and stops at a tableau node that accepts every
    // behavior as it searches.
    let is_liveness_off = lncheck.as_deref() == Some("off");
    // Where TLC's workers stop at an accepting node depends on how they interleave.
    if is_liveness_off && workers > 1 && !ir.model.live_formula.is_empty() {
        return report_not_native(printer, "-lncheck off with several workers");
    }
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
    if dfid.is_some() && is_continued && !args.has("-noGenerateSpecTE") {
        return report_not_native(printer, "DFID continuation with trace files");
    }
    if is_continued {
        let model = &ir.model;
        let is_built_in = |names: &[&str]| {
            ir.builtins
                .iter()
                .any(|builtin| names.contains(&&*ir.texts[builtin.name as usize]))
        };
        let unfollowed = if dfid.is_some() && model.alias.is_some() {
            Some("DFID continuation with an ALIAS")
        } else if !model.live_formula.is_empty() {
            Some("-continue with temporal properties")
        } else if model.view.is_some() || model.startup.symmetry.is_some() {
            Some("-continue under SYMMETRY or a VIEW")
        } else if !model.postconditions.is_empty() {
            Some("-continue with a POSTCONDITION")
        } else if dumps.has_command_line_dumps() {
            Some("-continue with -dumpTrace")
        } else if is_built_in(&[
            "Print",
            "PrintT",
            "AssertEq",
            "TLCSet",
            "TLCGetAndSet",
            "_Track",
        ]) {
            // TLC prints what the spec prints as it evaluates, before the violation it then
            // reports, and sets its registers again as it rebuilds each trace (`printTrace`),
            // which the search goes on reading.
            Some("-continue with a spec that prints or sets TLC's registers")
        } else if is_built_in(&[
            "RandomElement",
            "RandomSubset",
            "RandomSetOfSubsets",
            "RandomSubsetSet",
            "TestRandomSetOfSubsets",
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
    let json_files = if printer.host.is_file_system() {
        JsonFiles::System
    } else {
        JsonFiles::Host(Arc::new(HostFiles::new(printer.host.spec_files_read())))
    };
    let settings = Settings {
        dfid,
        is_violation_reported: true,
        // The front end leaves out a substitute or a value the configuration scopes to a module
        // (`<- [M]`, `= [M]`), which TLC applies, so what a model whose startup failed reads past
        // it may differ.
        is_failed_startup_retried: config
            .substitutions
            .iter()
            .all(|substitution| substitution.module.is_none())
            && config
                .constants
                .iter()
                .all(|assignment| assignment.module.is_none()),
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
        is_dumped: is_dumped && dot.is_none(),
        is_dot_dumped: dot.is_some(),
        is_continued,
        large_region_advice: printer.host.large_region_advice(),
        json_files: json_files.clone(),
        adopter: Some(get_adopter(&ir, workers, printer.is_tool)),
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
    let mut is_continued_past = false;
    let mut is_coverage_reached = false;
    let mut is_dump_unwritten = false;
    let mut declined = None;
    let is_periodic = config.periodic.is_some();
    let is_scoped_substituted = config
        .substitutions
        .iter()
        .any(|substitution| substitution.module.is_some());
    let ir_ref: &tla_ir::Ir = &ir;
    let (outcome, assumed_printed, (dumped, dotted)) = alongside(
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
            relay.is_dumped = is_dumped && dot.is_none();
            relay.dot = dot;
            relay.is_scoped_substituted = is_scoped_substituted;
            relay.dfid = settings.dfid;
            relay.coverage_countdown = coverage::get_countdown(args);
            let outcome = search(ir, &settings, &mut relay);
            // Under -dump dot the graph stands for the dump.
            let (dumped, dotted) = match relay.dotted {
                Some(Ok(graph)) => (Some(Ok(())), Some(graph)),
                Some(Err(reason)) => (Some(Err(reason)), None),
                None if dot.is_some() => (None, None),
                None => (relay.dumped, None),
            };
            (outcome, relay.assumed_printed, (dumped, dotted))
        },
        || {
            loop {
                // TLC prints each line as it goes, so what waits in the buffer goes out whenever
                // the search has nothing more to say yet.
                // While the run's output is held, the wait ends with the hold, so that what was
                // printed streams from then on.
                let event = match receiver.try_recv() {
                    Ok(event) => event,
                    Err(_) => {
                        printer.flush();
                        let received = match crate::transaction::get_hold_left() {
                            Some(left) => match receiver.recv_timeout(left) {
                                Err(mpsc::RecvTimeoutError::Timeout) => continue,
                                received => received.map_err(|_| ()),
                            },
                            None => receiver.recv().map_err(|_| ()),
                        };
                        let Ok(event) = received else {
                            break;
                        };
                        event
                    }
                };
                match event {
                    Event::DfidLevel(level, generated, distinct) => {
                        printer.print(2205, Level::None, &format!("Starting level {level}: {generated} states generated, {distinct} distinct states found."));
                    }
                    Event::InitialStatesStarted if dfid.is_some() => {}
                    Event::InitialStatesStarted => printer.print(
                        code::COMPUTING_INIT,
                        Level::None,
                        "Computing initial states...",
                    ),
                    Event::InitialStatesProgress(_) if dfid.is_some() => {}
                    Event::InitialStatesProgress(count) => printer.print(
                        code::COMPUTING_INIT_PROGRESS,
                        Level::None,
                        &format!("Computed {count} initial states..."),
                    ),
                    Event::InitialStates(generated, distinct) => {
                        initial_generated = generated;
                        if dfid.is_some() {
                            printer.print(2208, Level::None, &format!("Finished computing initial states: {generated} states generated, with {distinct} of them distinct."));
                        } else {
                            print_initial_states(printer, generated, distinct);
                        }
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
                    Event::LivenessStarted(branches, states, statistics) => {
                        checking = Some(print_liveness_check(printer, branches, states, "current"));
                        printer.count_message(statistics.counts());
                    }
                    Event::LivenessFinished => {
                        if let Some(checking) = checking.take() {
                            print_liveness_finished(printer, checking);
                        }
                    }
                    Event::Print(Some(text)) => printer.printed(&text),
                    Event::Warning(warning) => {
                        if let Err(reason) = printer.runtime_warning(ir_ref, &warning) {
                            declined = Some(reason.to_owned());
                        }
                    }
                    Event::StartupMessage(message) => print_startup_message(printer, &message),
                    Event::SymmetrySetsTooSmall(names) => {
                        if !print_small_sets(printer, &names) {
                            declined = Some(SMALL_SET_UNNAMED.to_owned());
                            break;
                        }
                    }
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
                    Event::DfidContinued(report) => {
                        is_continued_past = true;
                        print_dfid_continued(printer, &report);
                    }
                    Event::Continued(report) => {
                        is_continued_past = true;
                        if let Err(reason) = print_continued(printer, ir_ref, &report) {
                            declined = Some(reason.to_owned());
                        }
                    }
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
    // The host reads the files the Json module's operators would have read, and writes those they
    // wrote.
    if let JsonFiles::Host(files) = &json_files {
        for path in files.take_unread() {
            printer.host.read_spec_file(&path);
        }
        for (path, bytes) in files.take_written() {
            printer.host.write_file(Path::new(&path), &bytes, false);
        }
    }
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
            | SearchOutcome::StartupException { .. }
            | SearchOutcome::AssumptionFailed { .. }
    );
    // Under -continue TLC reports an error or a deadlock otherwise than it does without it, with
    // other traces and exit codes, which the binary doesn't follow.
    // WebAssembly's recursion bound stops the search as it would without -continue.
    if is_continued
        && !(dfid.is_some()
            && matches!(
                &outcome,
                SearchOutcome::DfidLimited { .. } | SearchOutcome::DfidUnsupported { .. }
            ))
        && !matches!(
            &outcome,
            SearchOutcome::Complete { .. } | SearchOutcome::Declined(_)
        )
        && !matches!(&outcome, SearchOutcome::Stopped { reason, .. } if reason == tla_engine::machine::WEBASSEMBLY_TOO_DEEP)
        // A deadlock and an initial state that violates a property's state predicate stop TLC
        // under -continue too, as they do without it, where it went on past nothing before
        // (`doNextSetErr` keeps no error state, `DoInitFunctor` throws).
        && !(!is_continued_past
            && matches!(
                &outcome,
                SearchOutcome::Stopped { violation: Some(violation), .. }
                    if matches!(
                        violation.kind,
                        tla_engine::search::ViolationKind::Deadlock {
                            accepted: None,
                            atom: None
                        } | tla_engine::search::ViolationKind::InitialPredicate(_)
                    )
            ))
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
    // `DotStateWriter.snapshot` copies the graph after each state it writes, closed as it closes
    // it, so the last copy is the graph, beside it under the path with ".dot" replaced.
    if let (Some(dot), Some((text, true)), Some(path)) = (&dot, &dotted, &dump)
        && dot.snapshot
    {
        let snapshot = path.replace(".dot", "_snapshot.dot");
        if printer.host.is_file_system()
            && tla_values::written::keep_file(Path::new(&snapshot)).is_err()
        {
            return report_not_native(printer, "-dump dot,snapshot into a file it can't keep");
        }
        if !printer
            .host
            .write_file(Path::new(&snapshot), text.as_bytes(), false)
        {
            return report_not_native(printer, "-dump dot,snapshot into a file it can't create");
        }
    }
    // TLC counts into its cost model as it rebuilds the trace of each violation -continue carries
    // it past, which the coverage pass doesn't count.
    if args.has("-coverage") && is_continued_past {
        return report_not_native(
            printer,
            "coverage of a run -continue carried past a violation",
        );
    }
    if args.has("-coverage") {
        let directories: Vec<&Path> = directories.iter().map(Path::new).collect();
        match coverage::compute(
            &ir,
            &outcome,
            printer.host,
            &directories,
            args.has("-fp").then_some(fingerprint_index),
        ) {
            Ok(messages) => printer.coverage = Some(messages),
            Err(why) => return report_not_native(printer, &why),
        }
        // TLC reports part way through a run past its first report's time, and ends a report of a
        // run of more than 5 minutes with 2777 rather than 2202, by its own clock, which a native
        // run past the cut can't rule out (design/cli.md, "-coverage").
        let cut = printer
            .host
            .get_variable("PROVE_IT_TEST_COVERAGE_CUT")
            .and_then(|seconds| seconds.parse().ok())
            .map_or(coverage::CUT, Duration::from_secs)
            .min(coverage::get_first_report(args));
        if printer
            .coverage
            .as_ref()
            .is_some_and(|messages| !messages.is_empty())
            && start.elapsed() > cut
        {
            return report_not_native(
                printer,
                "coverage of a run TLC may report on part way or take more than 5 minutes over",
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
            // Once the search completes, TLC checks one `_CheckName` for each _POSSIBLE
            // predicate, which reports the first the search never witnessed, and then the
            // postconditions (`Tool.checkPostConditionWithContext`): the pinned Jar checks
            // neither those nor what they print after it. Where it checks temporal properties
            // first, or with DFID or -continue, the binary doesn't follow.
            let unwitnessed = possible.iter().position(|&count| count <= 0);
            if unwitnessed.is_some()
                && (liveness.is_some()
                    || dfid.is_some()
                    || is_continued
                    || rejected_postcondition.is_some())
            {
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
                let is_lasso =
                    matches!(liveness.verdict, Verdict::Lasso { .. }) && !is_liveness_off;
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
                            workers: Some(workers),
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
                    Verdict::Lasso { .. } if is_liveness_off => None,
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
                if is_liveness_off {
                    // `ModelChecker.modelCheck` reports its progress before `finalCheck`.
                    print_progress(printer, &statistics, None);
                } else {
                    let checking = print_liveness_started(printer, &statistics, branches);
                    print_liveness_finished(printer, checking);
                }
            }
            if let Some(position) = unwitnessed {
                let statistics = Statistics {
                    generated: counts.generated,
                    distinct: counts.distinct,
                    queued: counts.queued,
                    depth: counts.depth,
                };
                return print_unwitnessed(
                    printer,
                    &ir,
                    &config,
                    position,
                    &postcondition_run(
                        &ir,
                        Some(&possible),
                        &statistics,
                        counts.initial_generated,
                        start,
                    ),
                    &statistics,
                    start,
                )
                .unwrap_or_else(|why| {
                    report_not_native(
                        printer,
                        &format!("a _POSSIBLE predicate the search didn't witness: {why}"),
                    )
                });
            }
            // TLC finishes a spec without a next-state relation before it checks the
            // postconditions (`ModelChecker.modelCheck`, `getActions().length == 0`); the front
            // end gives a spec without variables no actions, which the binary follows where the
            // configuration names no next-state relation either.
            let has_no_actions = ir.variables.is_empty();
            if has_no_actions
                && (config.next.is_some() || config.specification.is_some())
                && !ir.model.postconditions.is_empty()
            {
                return report_not_native(
                    printer,
                    "a POSTCONDITION of a spec without variables that names a next-state relation",
                );
            }
            if dfid.is_none() && !ir.model.postconditions.is_empty() && !has_no_actions {
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
                    if let Err(reason) = printer.replayed(&ir, line) {
                        return report_not_native(printer, reason);
                    }
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
        SearchOutcome::AssumptionFailed {
            position,
            failed_startup,
        } => {
            return print_assumption_failure(
                printer,
                &ir,
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
        // TLC rejects the value of a constant definition the configuration names as it reads
        // the configuration.
        SearchOutcome::ConfigError { message } => {
            // The engine's startup reports the value of a predicate it computed, which TLC holds
            // as the definition the configuration substitutes for it, and checks as an operator.
            let is_substituted = config.substitutions.iter().any(|substitution| {
                let name = &substitution.name;
                [
                    format!(" of {name} is equal to "),
                    format!("The operator {name}, which equals "),
                    format!("because {name} is false."),
                    format!(" {name} cannot be a constant."),
                    format!("The value of {name} is equal to "),
                ]
                .iter()
                .any(|subject| message.contains(subject.as_str()))
            });
            if is_substituted {
                return report_not_native(
                    printer,
                    "a value of a predicate the configuration substitutes a definition for",
                );
            }
            set_startup_thrown(
                printer,
                Thrown::Config(message.clone()),
                is_sany_warned,
                is_tlcext_declined,
            );
            return match FrontError::Config(message).get_coded(printer.is_tool) {
                Some(coded) => print_coded_failure(printer, &coded, start),
                None => report_not_native(printer, "a configuration error without TLC's code"),
            };
        }
        SearchOutcome::StartupException { message } => {
            let message = format!("{}{message}", tla_front::errors::UNEXPECTED_HEAD);
            set_startup_thrown(
                printer,
                Thrown::Evaluation(message.clone()),
                is_sany_warned,
                is_tlcext_declined,
            );
            return match FrontError::Evaluation(message).get_coded(printer.is_tool) {
                Some(coded) => print_coded_failure(printer, &coded, start),
                None => report_not_native(printer, "an exception without TLC's code"),
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
            violation: Some(mut violation),
            reason,
            ..
        } => {
            // TLC's worker fails on a POSTCONDITION it rejects as it reports a deadlock, before it
            // adds the deadlocked state to the behavior graphs (`Worker.run`): no atom fails and
            // no node accepts there, and nothing prints.
            if rejected_postcondition.is_some()
                && let ViolationKind::Deadlock { accepted, atom } = &mut violation.kind
            {
                *accepted = None;
                *atom = None;
                violation.added = None;
            }
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
                    let message =
                        "No next state actions defined to generate successor states from.";
                    printer.print(code::NO_NEXT_ACTION, Level::Error, message);
                    set_startup_thrown(
                        printer,
                        Thrown::Evaluation(message.to_owned()),
                        is_sany_warned,
                        is_tlcext_declined,
                    );
                    print_finished(printer, start);
                    Ok(NO_NEXT_ACTION)
                }
                // With several workers, TLC's others take the states left on its queue and expand
                // them as they race to the stop, and whichever worker adds a state two of a
                // level step to is its parent in the trace: its trace and counts then differ
                // from one worker's, and vary from run to run.
                _ if workers > 1 && violation.counts.is_raced => {
                    Err("a stop several workers race to".to_string())
                }
                // TLC's report of a failure evaluating the model, which it replays. It prints the
                // trace through the ALIAS, which the printing follows for a failure in the
                // next-state relation or an invariant.
                ViolationKind::Error { .. } if !config.possible.is_empty() => {
                    Err("a failure with a _POSSIBLE predicate".to_string())
                }
                // With several workers, TLC's others expand the states the worker enqueued before
                // a successor's constraint, action constraint or action property failed to
                // evaluate, as they race to the stop: its trace and counts then differ from one
                // worker's, and may vary from run to run.
                ViolationKind::Error {
                    site:
                        ErrorSite::Constraint(_)
                        | ErrorSite::ActionConstraint(_)
                        | ErrorSite::ActionProperty(_),
                } if workers > 1 && !violation.counts.is_lone_expansion => Err(
                    "a constraint, an action constraint or an action property that fails with \
                     several workers"
                        .to_string(),
                ),
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
                                    ErrorSite::Invariant(_)
                                    | ErrorSite::ActionConstraint(_)
                                    | ErrorSite::Constraint(_) => false,
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
                // TLC holds a name the configuration binds as its value, and drops an action
                // constraint bound to TRUE (`SpecProcessor.processModelConstraints`), where the
                // search evaluated the definition. A binding scoped to a module (`= [M] TRUE`)
                // leaves TLC evaluating the definition.
                ViolationKind::Error {
                    site: ErrorSite::ActionConstraint(position),
                } if config
                    .action_constraints
                    .get(position as usize)
                    .is_some_and(|name| {
                        config
                            .constants
                            .iter()
                            .any(|constant| constant.module.is_none() && &constant.name == name)
                            || config
                                .substitutions
                                .iter()
                                .any(|substitution| &substitution.name == name)
                    }) =>
                {
                    Err("a failing action constraint the configuration binds".to_string())
                }
                ViolationKind::Error {
                    site: ErrorSite::Constraint(position),
                } if config
                    .constraints
                    .get(position as usize)
                    .is_some_and(|name| {
                        config
                            .constants
                            .iter()
                            .any(|constant| constant.module.is_none() && &constant.name == name)
                            || config
                                .substitutions
                                .iter()
                                .any(|substitution| &substitution.name == name)
                    }) =>
                {
                    Err("a failing constraint the configuration binds".to_string())
                }
                // TLC checks the postconditions after an initial state some variable lacks a
                // value in (`ModelChecker.modelCheck`: `doInit` returns the violation
                // `DoInitFunctor` threw), on the CounterExample of the state, and exits with the
                // violation's status whatever they give. The counts of the run, the registers and
                // the CounterExample they may read, _POSSIBLE's counts and the trace files aren't
                // followed.
                ViolationKind::Error {
                    site: ErrorSite::Init,
                } if reason == INCOMPLETE_INITIAL_STATE
                    && (!config.postconditions.is_empty() || !config.possible.is_empty())
                    && (!config.possible.is_empty()
                        || !dumps.is_empty()
                        || ir.builtins.iter().any(|builtin| {
                            builtin.flags & tla_ir::Builtin::EXTERNAL_CLASS != 0
                                || matches!(
                                    &*ir.texts[builtin.name as usize],
                                    "TLCGet"
                                        | "_Counts"
                                        | "_CheckName"
                                        | "_PrintCounts"
                                        | "CounterExample"
                                        | "ToTrace"
                                )
                        })) =>
                {
                    Err(
                        "a POSTCONDITION that reads the run after an incomplete initial state"
                            .to_string(),
                    )
                }
                ViolationKind::Error { site } => 'failure: {
                    let added = match violation.added.as_ref().map(|_| format_added(&violation)) {
                        Some(Err(why)) => break 'failure Err(why.to_string()),
                        Some(Ok(added)) => Some(added),
                        None => None,
                    };
                    let counts = &violation.counts;
                    let stop = ErrorStop {
                        added,
                        workers,
                        reason: &reason,
                        startup: &violation.startup,
                        store: &violation.store,
                        states: violation.states.iter().map(Vec::as_slice).collect(),
                        actions: violation.labels.clone(),
                        site: match site {
                            ErrorSite::Init => Site::Init,
                            ErrorSite::Next => Site::Next,
                            ErrorSite::Invariant(position) => Site::Invariant(position),
                            ErrorSite::ActionConstraint(position) => {
                                Site::ActionConstraint(position)
                            }
                            ErrorSite::Constraint(position) => Site::Constraint(position),
                            ErrorSite::ActionProperty(position) => Site::ActionProperty(position),
                            ErrorSite::InitialConstraint(position) => {
                                Site::InitialConstraint(position)
                            }
                            ErrorSite::InitialView => Site::InitialView,
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
                            && (site == ErrorSite::Next && ir.model.check_deadlock
                                || site == ErrorSite::Init && reason == INCOMPLETE_INITIAL_STATE))
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
                // DFIDModelChecker checks no postcondition after an initial state's violation,
                // which `print_violation` checks as the breadth-first model checker does.
                ViolationKind::InitialInvariant(_) | ViolationKind::InitialPredicate(_)
                    if dfid.is_some() && !config.postconditions.is_empty() =>
                {
                    Err("DFID's initial violation with a POSTCONDITION".to_string())
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
                            workers: Some(workers),
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
        SearchOutcome::DfidInitialIncomplete {
            state,
            store,
            holds_collapsed,
        } => {
            if holds_collapsed || !args.has("-noGenerateSpecTE") {
                return report_not_native(
                    printer,
                    "DFID incomplete initial state with unrenderable values or trace files",
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
                    "DFID incomplete initial state has an unrenderable value",
                );
            };
            let refs: Vec<_> = values.iter().map(Option::as_ref).collect();
            let variables =
                crate::trace::get_partial_variables(&ir, &refs, printer.host.is_plain());
            printer.outcome.status = Some("error");
            printer.report(
                2106,
                &format!(
                    "State is not completely specified by the initial predicate:\n{}",
                    format_variables(&variables)
                ),
            );
            print_finished(printer, start);
            return 255;
        }
        SearchOutcome::DfidIncomplete {
            states,
            store,
            action,
            holds_collapsed,
            generated,
            distinct,
        } => {
            if holds_collapsed {
                return report_not_native(
                    printer,
                    "DFID incomplete trace holds a value whose printed shape is not retained",
                );
            }
            if !args.has("-noGenerateSpecTE") || !dumps.is_empty() {
                return report_not_native(printer, "DFID incomplete trace with trace files");
            }
            return print_dfid_incomplete(
                printer,
                &ir,
                &states,
                &store,
                action,
                (generated, distinct),
                start,
            )
            .unwrap_or_else(|reason| report_not_native(printer, reason));
        }
        SearchOutcome::DfidInitialInvariantFailure(violation) => {
            if !args.has("-noGenerateSpecTE")
                || !dumps.is_empty()
                || ir.builtins.iter().any(|builtin| {
                    matches!(
                        &*ir.texts[builtin.name as usize],
                        "RandomElement"
                            | "RandomSubset"
                            | "RandomSetOfSubsets"
                            | "RandomSubsetSet"
                            | "TestRandomSetOfSubsets"
                            | "TLCSet"
                            | "TLCGetAndSet"
                            | "_Track"
                    )
                })
            {
                return report_not_native(
                    printer,
                    "DFID initial invariant failure with trace files, random draws, or register writes",
                );
            }
            return print_dfid_initial_invariant_failure(printer, &ir, &violation, start)
                .unwrap_or_else(|reason| report_not_native(printer, &reason));
        }
        SearchOutcome::DfidInitialFailure(violation) => {
            if !args.has("-noGenerateSpecTE")
                || !dumps.is_empty()
                || !ir.model.postconditions.is_empty()
                || ir.builtins.iter().any(|builtin| {
                    matches!(
                        &*ir.texts[builtin.name as usize],
                        "RandomElement"
                            | "RandomSubset"
                            | "RandomSetOfSubsets"
                            | "RandomSubsetSet"
                            | "TestRandomSetOfSubsets"
                            | "TLCSet"
                            | "TLCGetAndSet"
                    )
                })
            {
                return report_not_native(
                    printer,
                    "DFID initial failure with trace files, a postcondition, random draws, or register writes",
                );
            }
            return print_dfid_initial_failure(printer, &ir, &violation, start)
                .unwrap_or_else(|reason| report_not_native(printer, &reason));
        }
        SearchOutcome::DfidActionFailure(violation) => {
            if !args.has("-noGenerateSpecTE")
                || !dumps.is_empty()
                || ir.builtins.iter().any(|builtin| {
                    matches!(
                        &*ir.texts[builtin.name as usize],
                        "RandomElement"
                            | "RandomSubset"
                            | "RandomSetOfSubsets"
                            | "RandomSubsetSet"
                            | "TestRandomSetOfSubsets"
                            | "TLCSet"
                            | "TLCGetAndSet"
                            | "_Track"
                    )
                })
            {
                return report_not_native(
                    printer,
                    "DFID action failure with trace files, random draws, or register writes",
                );
            }
            return print_dfid_action_failure(printer, &ir, &violation, start)
                .unwrap_or_else(|reason| report_not_native(printer, &reason));
        }
        SearchOutcome::DfidNextFailure(violation) => {
            if !args.has("-noGenerateSpecTE")
                || !dumps.is_empty()
                || ir.builtins.iter().any(|builtin| {
                    matches!(
                        &*ir.texts[builtin.name as usize],
                        "RandomElement"
                            | "RandomSubset"
                            | "RandomSetOfSubsets"
                            | "RandomSubsetSet"
                            | "TestRandomSetOfSubsets"
                            | "TLCSet"
                            | "TLCGetAndSet"
                            | "_Track"
                    )
                })
            {
                return report_not_native(
                    printer,
                    "DFID next-state failure with trace files, random draws, or register writes",
                );
            }
            return print_dfid_next_failure(printer, &ir, &violation, start)
                .unwrap_or_else(|reason| report_not_native(printer, &reason));
        }
        SearchOutcome::DfidViolation(violation)
        | SearchOutcome::DfidInvariantFailure(violation) => {
            if !args.has("-noGenerateSpecTE")
                || !dumps.is_empty()
                || ir.builtins.iter().any(|builtin| {
                    matches!(
                        &*ir.texts[builtin.name as usize],
                        "RandomElement"
                            | "RandomSubset"
                            | "RandomSetOfSubsets"
                            | "RandomSubsetSet"
                            | "TestRandomSetOfSubsets"
                            | "TLCSet"
                            | "TLCGetAndSet"
                            | "_Track"
                    )
                })
            {
                return report_not_native(
                    printer,
                    "DFID trace with trace files, random draws, or register writes",
                );
            }
            return print_dfid_violation(printer, &ir, &violation, &dumps, start)
                .unwrap_or_else(|reason| report_not_native(printer, reason));
        }
        SearchOutcome::DfidUnsupported { multiple_workers } => {
            let text = if multiple_workers {
                "Depth-First Iterative Deepening mode does not support multiple workers (https://github.com/tlaplus/tlaplus/issues/548).  Please run TLC with a single worker."
            } else {
                "Depth-First Iterative Deepening mode does not support checking liveness properties (https://github.com/tlaplus/tlaplus/issues/548).  Please check liveness properties in Breadth-First-Search mode."
            };
            printer.print(code::GENERAL, Level::Error, text);
            print_finished(printer, start);
            return 255;
        }
        SearchOutcome::DfidLimited {
            generated,
            distinct,
        } => {
            if printer.is_tool {
                let date = printer.date();
                printer.print(2206, Level::None, &format!("Progress(-1) at {date}: {generated} states generated, {distinct} distinct states found, -1 states left on queue."));
            }
            printer.print(
                2204,
                Level::None,
                &format!("{generated} states generated, {distinct} distinct states found."),
            );
            print_finished(printer, start);
            return if dfid.is_some_and(|limit| limit >= 2) {
                SUCCESS
            } else {
                255
            };
        }
    };
    let optimistic = optimistic_probability(counts.distinct, counts.generated);
    let distance = if dfid.is_some() {
        crate::summary::dfid_fingerprint_distance(&fingerprints)
    } else {
        fingerprint_distance(counts.distinct, counts.generated, &fingerprints, threads)
    };
    if dfid.is_some() && distance.is_none() {
        return report_not_native(printer, "DFID fingerprint distance is nonpositive");
    }
    let actual = distance
        .map(|distance| {
            format!(
                "\n  based on the actual fingerprints:  val = {}",
                format_probability(actual_probability(distance))
            )
        })
        .unwrap_or_default();
    let actual = if dfid.is_some() && counts.generated == 0 && counts.distinct == 0 {
        "\n  based on the actual fingerprints:  val = 0.0".to_string()
    } else {
        actual
    };
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
    if dfid.is_some() {
        printer.outcome.counts = statistics.counts();
        if printer.is_tool {
            let date = printer.date();
            printer.print(2206, Level::None, &format!("Progress(-1) at {date}: {} states generated, {} distinct states found, -1 states left on queue.", counts.generated, counts.distinct));
        }
        printer.print(
            2204,
            Level::None,
            &format!(
                "{} states generated, {} distinct states found.",
                counts.generated, counts.distinct
            ),
        );
        print_finished(printer, start);
        return SUCCESS;
    }
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

// `DFIDModelChecker.modelCheckImpl`: where computing the initial states throws before TLC has a
// state (`errState`), TLC reports the exception as one it didn't expect, replays the initial
// states with its call stack and, as that throws again, reports its `Tool` in place of the
// stack, then the summary of the replay, which counted no state.
fn print_dfid_initial_failure(
    printer: &mut Printer,
    ir: &tla_ir::Ir,
    violation: &Violation,
    start: Instant,
) -> Result<i32, String> {
    let failure = crate::failure::dfid_initial_failure(ir, violation)?;
    let message = if printer.is_tool {
        &failure.tool_text
    } else {
        &failure.text
    };
    printer.outcome.status = Some("error");
    printer.report(
        code::GENERAL,
        &format!(
            "TLC threw an unexpected exception.\nThis was probably caused by an error in the spec or model.\nThe error occurred when TLC was computing initial states.\nThe exception was a {}\n: {message}",
            failure.class_name
        ),
    );
    // `Object.toString` of TLC's `Tool`: its class and identity hash.
    let identity = (std::process::id() as u64)
        .wrapping_mul(0x9e37_79b9_7f4a_7c15)
        .rotate_left(17) as u32
        | 0x1000_0000;
    printer.print(
        code::NESTED_EXPRESSION,
        Level::Error,
        &format!(
            "The error occurred when TLC was evaluating the nested\nexpressions at the following positions:\ntlc2.tool.impl.FastTool@{identity:x}"
        ),
    );
    if printer.is_tool {
        let date = printer.date();
        printer.print(
            2206,
            Level::None,
            &format!("Progress(-1) at {date}: 0 states generated, 0 distinct states found, -1 states left on queue."),
        );
    }
    printer.print(
        2204,
        Level::None,
        "0 states generated, 0 distinct states found.",
    );
    print_finished(printer, start);
    Ok(75)
}

fn print_dfid_initial_invariant_failure(
    printer: &mut Printer,
    ir: &tla_ir::Ir,
    violation: &Violation,
    start: Instant,
) -> Result<i32, String> {
    if violation.holds_collapsed {
        return Err("DFID initial failure has an unrenderable value".into());
    }
    let ViolationKind::Error {
        site: ErrorSite::InitialInvariant(position),
    } = violation.kind
    else {
        return Err("DFID initial failure has no invariant".into());
    };
    let failure = crate::failure::dfid_initial_invariant_failure(ir, violation, position)?;
    if failure.code != code::GENERAL
        || failure.state.is_some()
        || failure.fingerprint.is_some()
        || !failure.printed.is_empty()
    {
        return Err("DFID initial invariant exception cannot be reported exactly".into());
    }
    let state = violation
        .states
        .first()
        .ok_or("DFID initial failure state is missing")?;
    let values = state
        .iter()
        .map(|&id| tla_trace::from_store(&violation.store, id))
        .collect::<Result<Vec<_>, _>>()
        .map_err(|_| "DFID initial failure has an unrenderable value")?;
    let variables = crate::trace::get_state_variables(ir, &values, printer.host.is_plain());
    let message = if printer.is_tool {
        &failure.tool_message
    } else {
        &failure.message
    };
    printer.outcome.status = Some("error");
    printer.report(
        2102,
        &format!(
            "{message}\nWhile working on the initial state:\n{}",
            format_variables(&variables)
        ),
    );
    let counts = &violation.counts;
    if printer.is_tool {
        let date = printer.date();
        printer.print(2206, Level::None, &format!("Progress(-1) at {date}: {} states generated, {} distinct states found, -1 states left on queue.", counts.generated, counts.distinct));
    }
    printer.print(
        2204,
        Level::None,
        &format!(
            "{} states generated, {} distinct states found.",
            counts.generated, counts.distinct
        ),
    );
    print_finished(printer, start);
    Ok(0)
}

fn print_dfid_action_failure(
    printer: &mut Printer,
    ir: &tla_ir::Ir,
    violation: &Violation,
    start: Instant,
) -> Result<i32, String> {
    if violation.holds_collapsed {
        return Err("DFID action failure trace has an unrenderable value".into());
    }
    let ViolationKind::ActionProperty(position) = violation.kind else {
        return Err("DFID action failure has no property".into());
    };
    let property = ir
        .model
        .action_properties
        .get(position)
        .ok_or("DFID action property is missing")?;
    if property.scope.is_some() {
        return Err("DFID action failure in an instance scope".into());
    }
    let stack = crate::failure::dfid_action_failure(ir, violation, position)?;
    if stack.is_empty() {
        return Err("DFID action failure has no reproducible call stack".into());
    }
    let states: Vec<_> = violation
        .states
        .iter()
        .map(|state| {
            state
                .iter()
                .map(|&id| tla_trace::from_store(&violation.store, id))
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<_, _>>()
        .map_err(|_| "DFID action failure trace has an unrenderable value")?;
    printer.outcome.status = Some("error");
    printer.report(
        2113,
        &format!(
            "Evaluating action property {} failed.",
            ir.texts[property.name as usize]
        ),
    );
    printer.print(
        code::BEHAVIOR_UP_TO_THIS_POINT,
        Level::Error,
        "The behavior up to this point is:",
    );
    for (position, state) in states.iter().enumerate() {
        let variables = crate::trace::get_state_variables(ir, state, printer.host.is_plain());
        printer.print(
            code::STATE_PRINT_1,
            Level::State,
            &format!("{}:\n{}", position + 1, format_variables(&variables)),
        );
        if let Some(reported) = printer.outcome.violations.last_mut() {
            reported.states.push(ReportedState {
                label: String::new(),
                variables,
            });
        }
    }
    if violation.counts.is_dfid_replayed {
        print_call_stack(printer, ir, &stack);
    }
    let counts = &violation.counts;
    if printer.is_tool {
        let date = printer.date();
        printer.print(2206, Level::None, &format!("Progress(-1) at {date}: {} states generated, {} distinct states found, -1 states left on queue.", counts.generated, counts.distinct));
    }
    printer.print(
        2204,
        Level::None,
        &format!(
            "{} states generated, {} distinct states found.",
            counts.generated, counts.distinct
        ),
    );
    print_finished(printer, start);
    Ok(13)
}

/// TLC's report of an exception in the next-state relation under -dfid (`DFIDModelChecker.doNext`
/// catches it as a `Throwable`): an EvalException is `EC.GENERAL` with its message, and TLC keeps
/// the call stack and replays the expansion on the next level, which prints the nested
/// expressions. A recursion without end overflows TLC's stack, which it reports as
/// `EC.SYSTEM_STACK_OVERFLOW` and keeps no call stack for (`setErrState` with `keepCallStack`
/// false), so `runTLC` returns the error at once and no replay prints nested expressions.
fn print_dfid_next_failure(
    printer: &mut Printer,
    ir: &tla_ir::Ir,
    violation: &Violation,
    start: Instant,
) -> Result<i32, String> {
    if violation.holds_collapsed {
        return Err("DFID failure trace has a value whose printed shape is not retained".into());
    }
    let failure = crate::failure::dfid_next_failure(ir, violation)?;
    match &failure {
        Some(failure)
            if failure.code == code::GENERAL
                || failure.call_stack.is_empty()
                || !failure.printed.is_empty()
                || failure.fingerprint.is_some() =>
        {
            return Err("DFID next-state exception cannot be reported exactly".into());
        }
        Some(_) => {}
        None if printer.host.is_plain() => {
            return Err("a recursion that overflows TLC's stack, in the library".into());
        }
        // What the spec printed before TLC overflowed, which the search doesn't keep.
        None if !ir.model.live_properties.is_empty() || crate::failure::may_print(ir) => {
            return Err(
                "a recursion that overflows TLC's stack in a model that prints or checks more"
                    .into(),
            );
        }
        None => {}
    }
    let states: Vec<_> = violation
        .states
        .iter()
        .map(|state| {
            state
                .iter()
                .map(|&id| tla_trace::from_store(&violation.store, id))
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<_, _>>()
        .map_err(|_| "DFID failure trace has an unrenderable value")?;
    printer.outcome.status = Some("error");
    match &failure {
        Some(failure) => {
            let message = if printer.is_tool {
                format!(
                    "@!@!@STARTMSG {}:0 @!@!@\n{}\n@!@!@ENDMSG {} @!@!@",
                    failure.code, failure.message, failure.code
                )
            } else {
                failure.message.clone()
            };
            printer.report(code::GENERAL, &format!("TLC threw an unexpected exception.\nThis was probably caused by an error in the spec or model.\nThe error occurred when TLC was computing the set of next states.\nThe exception was a tlc2.tool.EvalException\n: {message}"));
        }
        None => printer.report(code::SYSTEM_STACK_OVERFLOW, STACK_OVERFLOW_MESSAGE),
    }
    printer.print(
        code::BEHAVIOR_UP_TO_THIS_POINT,
        Level::Error,
        "The behavior up to this point is:",
    );
    for (position, state) in states.iter().enumerate() {
        let variables = crate::trace::get_state_variables(ir, state, printer.host.is_plain());
        printer.print(
            code::STATE_PRINT_1,
            Level::State,
            &format!("{}:\n{}", position + 1, format_variables(&variables)),
        );
        if let Some(reported) = printer.outcome.violations.last_mut() {
            reported.states.push(ReportedState {
                label: String::new(),
                variables,
            });
        }
    }
    // The nested expressions are what TLC's replay on the next level prints.
    if let Some(failure) = &failure
        && violation.counts.is_dfid_replayed
    {
        print_call_stack(printer, ir, &failure.call_stack);
    }
    let counts = &violation.counts;
    if printer.is_tool {
        let date = printer.date();
        printer.print(2206, Level::None, &format!("Progress(-1) at {date}: {} states generated, {} distinct states found, -1 states left on queue.", counts.generated, counts.distinct));
    }
    printer.print(
        2204,
        Level::None,
        &format!(
            "{} states generated, {} distinct states found.",
            counts.generated, counts.distinct
        ),
    );
    print_finished(printer, start);
    Ok(255)
}

fn print_dfid_incomplete(
    printer: &mut Printer,
    ir: &tla_ir::Ir,
    states: &[Vec<tla_values::Id>],
    store: &tla_values::Store,
    action: u32,
    counts: (u64, u64),
    start: Instant,
) -> Result<i32, &'static str> {
    let (generated, distinct) = counts;
    let last = states.last().ok_or("DFID incomplete trace is empty")?;
    let actions = &ir.model.actions;
    let action = actions
        .get(action as usize)
        .ok_or("DFID incomplete action is unknown")?;
    // `Action.getName`, as `doNextSetErr` names the action.
    let subject = if actions.len() == 1 {
        "the next-state action".to_string()
    } else {
        format!(
            "action {} of the next-state relation",
            ir.texts[action.name as usize]
        )
    };
    let mut names: Vec<&str> = last
        .iter()
        .enumerate()
        .filter(|(_, id)| **id == tla_engine::UNASSIGNED)
        .map(|(index, _)| ir.texts[ir.variables[index] as usize].as_ref())
        .collect();
    if names.is_empty() {
        return Err("DFID incomplete successor has no missing variable");
    }
    names.sort_by(|a, b| a.encode_utf16().cmp(b.encode_utf16()));
    let (noun, verb) = if names.len() > 1 {
        ("variables", "are")
    } else {
        ("variable", "is")
    };
    let states: Vec<_> = states
        .iter()
        .map(|state| {
            state
                .iter()
                .map(|&id| {
                    if id == tla_engine::UNASSIGNED {
                        Ok(None)
                    } else {
                        tla_trace::from_store(store, id).map(Some)
                    }
                })
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<_, _>>()
        .map_err(|_| "DFID incomplete trace holds a value that cannot be rendered")?;
    printer.outcome.status = Some("error");
    printer.report(code::INCOMPLETE_SUCCESSOR, &format!("Successor state is not completely specified by {subject}. The following {noun} {verb} not defined: {}.\n", names.join(", ")));
    printer.print(
        code::BEHAVIOR_UP_TO_THIS_POINT,
        Level::Error,
        "The behavior up to this point is:",
    );
    for (position, state) in states.iter().enumerate() {
        let values: Vec<_> = state.iter().map(Option::as_ref).collect();
        let variables = crate::trace::get_partial_variables(ir, &values, printer.host.is_plain());
        printer.print(
            code::STATE_PRINT_1,
            Level::State,
            &format!("{}:\n{}", position + 1, format_variables(&variables)),
        );
        if let Some(reported) = printer.outcome.violations.last_mut() {
            reported.states.push(ReportedState {
                label: String::new(),
                variables,
            });
        }
    }
    if printer.is_tool {
        let date = printer.date();
        printer.print(2206, Level::None, &format!("Progress(-1) at {date}: {generated} states generated, {distinct} distinct states found, -1 states left on queue."));
    }
    printer.print(
        2204,
        Level::None,
        &format!("{generated} states generated, {distinct} distinct states found."),
    );
    print_finished(printer, start);
    Ok(75)
}

fn print_dfid_violation(
    printer: &mut Printer,
    ir: &tla_ir::Ir,
    violation: &Violation,
    _dumps: &TraceDumps,
    start: Instant,
) -> Result<i32, &'static str> {
    let (code, headline, status, exit, state_code) = match violation.kind {
        ViolationKind::Invariant(owner) => (
            code::INVARIANT_VIOLATED_BEHAVIOR,
            format!("Invariant {} is violated.", invariant_name(ir, owner)?),
            "invariant-violation",
            SAFETY_VIOLATION,
            code::STATE_PRINT_2,
        ),
        ViolationKind::Deadlock { .. } => (
            code::DEADLOCK_REACHED,
            "Deadlock reached.".to_string(),
            "deadlock",
            DEADLOCK,
            code::STATE_PRINT_1,
        ),
        ViolationKind::Error {
            site: ErrorSite::Invariant(owner),
        } => (
            2111,
            format!(
                "Evaluating invariant {} failed.",
                invariant_name(ir, owner as usize)?
            ),
            "error",
            76,
            code::STATE_PRINT_1,
        ),
        ViolationKind::ActionProperty(position) => (
            code::ACTION_PROPERTY_VIOLATED_BEHAVIOR,
            action_property_headline(ir, position)?,
            "liveness-violation",
            LIVENESS_VIOLATION,
            code::STATE_PRINT_1,
        ),
        _ => return Err("unsupported DFID violation"),
    };
    if violation.holds_collapsed {
        return Err("DFID trace holds a value whose printed shape is not retained");
    }
    let states: Vec<_> = violation
        .states
        .iter()
        .map(|state| {
            state
                .iter()
                .map(|&id| tla_trace::from_store(&violation.store, id))
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<_, _>>()
        .map_err(|_| "DFID trace holds a value that cannot be rendered")?;
    printer.outcome.status = Some(status);
    printer.report(code, &headline);
    printer.print(
        code::BEHAVIOR_UP_TO_THIS_POINT,
        Level::Error,
        "The behavior up to this point is:",
    );
    for (position, state) in states.iter().enumerate() {
        let variables = crate::trace::get_state_variables(ir, state, printer.host.is_plain());
        let separator = if state_code == code::STATE_PRINT_2 {
            ": \n"
        } else {
            ":\n"
        };
        printer.print(
            state_code,
            Level::State,
            &format!(
                "{}{separator}{}",
                position + 1,
                format_variables(&variables)
            ),
        );
        if let Some(reported) = printer.outcome.violations.last_mut() {
            reported.states.push(ReportedState {
                label: String::new(),
                variables,
            });
        }
    }
    let counts = &violation.counts;
    if printer.is_tool {
        let date = printer.date();
        printer.print(2206, Level::None, &format!("Progress(-1) at {date}: {} states generated, {} distinct states found, -1 states left on queue.", counts.generated, counts.distinct));
    }
    printer.print(
        2204,
        Level::None,
        &format!(
            "{} states generated, {} distinct states found.",
            counts.generated, counts.distinct
        ),
    );
    print_finished(printer, start);
    Ok(exit)
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
            | ErrorSite::InitialView
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
    // The trace's file of the trace exploration spec, which `_TLCTrace`'s postcondition fails to
    // write where its directory isn't there.
    let unplaced = printer.unplaced_trace_file.clone();
    let is_unplaced = |file: &crate::dump_trace::DumpedFile| {
        !file.is_printed && Some(&file.path) == unplaced.as_ref()
    };
    let placed: Vec<_> = trace
        .dumped
        .iter()
        .filter(|file| !is_unplaced(file))
        .collect();
    if !placed
        .iter()
        .all(|file| printer.host.can_write(Path::new(&file.path)))
    {
        return Err("-dumpTrace into a directory that doesn't exist");
    }
    let dumped_lines: Vec<crate::trace::PrintedOutput> = trace
        .dumped
        .iter()
        .filter(|file| file.is_printed)
        .map(|file| crate::trace::PrintedOutput::Print(file.get_line()))
        .collect();
    // TLC adds a deadlocked state to the behavior graphs after it reports the deadlock, and
    // reports the tableau node that accepts every behavior it reaches next.
    let accepted = match &violation.kind {
        ViolationKind::Deadlock {
            accepted: Some(accepted),
            ..
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
    // TLC adds a deadlocked state to the behavior graphs once it has reported the deadlock and
    // checked the postconditions, and prints the call stack of an atom that fails there.
    let atom_stack = match violation.kind {
        ViolationKind::Deadlock {
            atom: Some(atom), ..
        } => match deadlock_atom_stack(ir, violation, atom) {
            Ok(stack) => stack,
            Err(reason) => return Ok(report_not_native(printer, &reason)),
        },
        _ => Vec::new(),
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
        ViolationKind::NoNextState
        | ViolationKind::Error { .. }
        | ViolationKind::SimulatedLasso { .. } => return Err(NOT_IN_IR),
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
            let is_printing = ir.builtins.iter().any(|builtin| {
                matches!(
                    &*ir.texts[builtin.name as usize],
                    "Print" | "PrintT" | "AssertEq"
                )
            });
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
        // TLC checks the postconditions then, on the CounterExample of the state, and exits with
        // the violation's status whatever they give (`ModelChecker.modelCheck` drops
        // `checkPostConditionWithCounterExample`'s): what they print and the report of one that
        // fails follow the violation's. The counts of the initial states they may read, and the
        // trace files, aren't followed.
        let postconditions = if ir.model.postconditions.is_empty() {
            None
        } else {
            let reads_run = ir.builtins.iter().any(|builtin| {
                builtin.flags & tla_ir::Builtin::EXTERNAL_CLASS != 0
                    || matches!(
                        &*ir.texts[builtin.name as usize],
                        "TLCGet" | "_Counts" | "_CheckName" | "_PrintCounts" | "Trace"
                    )
            });
            if reads_run || !dumped_lines.is_empty() || !trace.dumped.is_empty() {
                return Err(
                    "a POSTCONDITION that reads the run or writes a trace file after an initial state's violation",
                );
            }
            Some(
                trace
                    .postconditions
                    .as_ref()
                    .ok_or("a POSTCONDITION TLC rejects after an initial state's violation")?,
            )
        };
        let state = trace.states.into_iter().next().ok_or(NOT_IN_IR)?;
        // TLC evaluates the ALIAS on the state as it builds the message (`ModelChecker.doInit`).
        for line in &state.alias_output {
            printer.replayed(ir, line)?;
        }
        printer.print(
            code,
            Level::Error,
            &format!("{text}\n{}", format_variables(&state.variables)),
        );
        if unplaced.is_some() {
            return Err("-teSpecOutDir into a directory that isn't there");
        }
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
            printer.replayed(ir, line)?;
        }
        if let Some(checked) = postconditions {
            for line in &checked.printed {
                printer.replayed(ir, line)?;
            }
            print_postcondition_failure(printer, ir, Some(checked));
        }
        print_finished(printer, start);
        return Ok(exit_code);
    }
    let added: Vec<_> = format_added(violation)?
        .into_iter()
        .map(crate::trace::PrintedOutput::Print)
        .collect();
    // TLC reports a postcondition that fails before it adds the state it stopped at to the
    // behavior graphs, which the printing doesn't order.
    if !added.is_empty() && !ir.model.postconditions.is_empty() {
        return Err("a POSTCONDITION before what TLC prints adding the stopped state");
    }
    let lasso_printed = match &violation.kind {
        ViolationKind::Lasso { printed, .. } => printed
            .iter()
            .map(|prints| {
                format_printed(&violation.store, prints).map(crate::trace::PrintedOutput::Print)
            })
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
            printer.replayed(ir, line)?;
        }
        // TLC evaluates the ALIAS of each state once it has rebuilt them, before it finds the
        // properties the counterexample violates.
        let is_interleaved = match lasso {
            Some((_, is_stuttering, ..)) => !is_stuttering,
            None => trace.states.len() > 1,
        };
        for line in counterexample_alias_output(&trace, is_interleaved)? {
            printer.replayed(ir, line)?;
        }
        // What the atoms print as TLC finds the properties the lasso it rebuilt violates, as it
        // checks them rather than as it rebuilds the trace.
        for line in &lasso_printed {
            printer.replayed(ir, line)?;
        }
        printer.report(code, &text);
        (
            code::COUNTER_EXAMPLE,
            "The following behavior constitutes a counter-example:\n",
        )
    } else {
        printer.report(code, &text);
        for line in first_output {
            printer.replayed(ir, line)?;
        }
        (
            code::BEHAVIOR_UP_TO_THIS_POINT,
            "The behavior up to this point is:",
        )
    };
    printer.print(heading_code, Level::Error, heading);
    print_states(printer, ir, &trace.states, &labels, is_counterexample)?;
    // `printTraceAndStop` reports what `printTrace` throws on the successor it didn't find, and
    // the run ends as after the trace.
    if trace.is_successor_lost {
        if !trace.dumped.is_empty() {
            return Ok(report_not_native(
                printer,
                "-dumpTrace of a trace whose successor TLC fails to find again",
            ));
        }
        printer.report(
            code::GENERAL,
            "TLC threw an unexpected exception.\nThis was probably caused by an error in the spec or model.\nSee the User Output or TLC Console for clues to what happened.\nThe exception was a java.lang.NullPointerException\n: Cannot read field \"state\" because \"currentStateInfo\" is null",
        );
    }
    // -dumpTrace's postconditions write their files as TLC checks them, then the trace
    // exploration spec's, before the configuration's (`Spec.getPostConditionSpecs`); TLC stops
    // at the first that fails (`Tool.checkPostConditionWithContext`). The binary follows the
    // trace exploration spec's failure after a safety violation's trace without a POSTCONDITION,
    // whose report then ends with it.
    let mut unwritten = None;
    for file in &trace.dumped {
        if !is_unplaced(file) {
            if !printer
                .host
                .write_file(Path::new(&file.path), &file.bytes, false)
            {
                return Ok(report_not_native(
                    printer,
                    "-dumpTrace into a file it can't write",
                ));
            }
            continue;
        }
        let is_followed = lasso.is_none()
            && !is_counterexample
            && added.is_empty()
            && accepted.is_none()
            && checking.is_none()
            && atom_stack.is_empty()
            && !trace.is_successor_lost
            && ir.model.postconditions.is_empty();
        if !is_followed {
            return Err("-teSpecOutDir into a directory that isn't there");
        }
        let path = Path::new(&file.path);
        if printer.host.write_file(path, &file.bytes, false) {
            continue;
        }
        let Some(reason) = printer.host.open_failure(path, true) else {
            return Ok(report_not_native(
                printer,
                "-dumpTrace into a file it can't write",
            ));
        };
        unwritten = Some(format!("{} ({reason})", file.path));
    }
    printer.unplaced_trace_file = None;
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
            printer.replayed(ir, line)?;
        }
    }
    match lasso {
        None if is_counterexample => {}
        // TLC adds the state it stopped at to the behavior graphs once it has checked the
        // postconditions on the trace (`Worker.run`).
        None => {
            for line in trace
                .trace_output
                .iter()
                .chain(postcondition_output.clone())
                .chain(&added)
            {
                printer.replayed(ir, line)?;
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
            printer.replayed(ir, line)?;
        }
    }
    if let Some((accepted, headline, labels)) = accepted {
        for line in accepted.states[0]
            .output
            .iter()
            .chain(&accepted.trace_output)
        {
            printer.replayed(ir, line)?;
        }
        for line in counterexample_alias_output(&accepted, accepted.states.len() > 1)? {
            printer.replayed(ir, line)?;
        }
        printer.report(code::TEMPORAL_PROPERTY_VIOLATED, &headline);
        printer.print(
            code::COUNTER_EXAMPLE,
            Level::Error,
            "The following behavior constitutes a counter-example:\n",
        );
        print_states(printer, ir, &accepted.states, &labels, true)?;
    }
    print_postcondition_failure(printer, ir, trace.postconditions.as_ref());
    if let Some(error) = unwritten {
        print_trace_file_failure(printer, &error);
    }
    if !atom_stack.is_empty() {
        print_call_stack(printer, ir, &atom_stack);
    }
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
fn print_dfid_continued(printer: &mut Printer, report: &DfidContinuedReport) {
    if report.is_initial {
        let variables = report.states.first().cloned().unwrap_or_default();
        printer.print(
            report.code,
            Level::Error,
            &format!("{}\n{}", report.headline, format_variables(&variables)),
        );
        printer.record(Reported {
            code: report.code,
            headline: report.headline.clone(),
            states: vec![ReportedState {
                label: String::new(),
                variables,
            }],
            loop_start: None,
        });
        return;
    }
    printer.report(report.code, &report.headline);
    printer.print(
        code::BEHAVIOR_UP_TO_THIS_POINT,
        Level::Error,
        "The behavior up to this point is:",
    );
    let state_code = if report.code == code::INVARIANT_VIOLATED_BEHAVIOR {
        code::STATE_PRINT_2
    } else {
        code::STATE_PRINT_1
    };
    for (index, variables) in report.states.iter().enumerate() {
        let separator = if state_code == code::STATE_PRINT_2 {
            ": \n"
        } else {
            ":\n"
        };
        printer.print(
            state_code,
            Level::State,
            &format!("{}{separator}{}", index + 1, format_variables(variables)),
        );
        if let Some(reported) = printer.outcome.violations.last_mut() {
            reported.states.push(ReportedState {
                label: String::new(),
                variables: variables.clone(),
            });
        }
    }
}

fn print_continued(
    printer: &mut Printer,
    ir: &tla_ir::Ir,
    report: &ContinuedReport,
) -> Result<(), &'static str> {
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
        return Ok(());
    }
    printer.report(report.code, &report.headline);
    for line in trace
        .states
        .first()
        .into_iter()
        .flat_map(|state| &state.output)
    {
        printer.replayed(ir, line)?;
    }
    printer.print(
        code::BEHAVIOR_UP_TO_THIS_POINT,
        Level::Error,
        "The behavior up to this point is:",
    );
    let labels: Vec<&str> = report.labels.iter().map(String::as_str).collect();
    print_states(printer, ir, &trace.states, &labels, false)?;
    for line in &trace.trace_output {
        printer.replayed(ir, line)?;
    }
    Ok(())
}

// What the ALIAS prints as TLC evaluates it on a counterexample's states, in their order. TLC
// rebuilds a lasso's path to its cycle before it evaluates the ALIAS on it, but evaluates it on
// each state of a cycle that isn't a stuttering one as it rebuilds the next
// (`LiveWorker.printTrace`), and so on each state of a counterexample `LiveCheck` finds
// (`LiveCheck.printErrorTrace`): where the spec prints too, those prints interleave with the
// ALIAS's, which the rebuilt trace, holding what the spec printed as one, doesn't place.
fn counterexample_alias_output(
    trace: &crate::trace::PrintedTrace,
    is_interleaved: bool,
) -> Result<Vec<&crate::trace::PrintedOutput>, &'static str> {
    let output: Vec<_> = trace
        .states
        .iter()
        .flat_map(|state| &state.alias_output)
        .collect();
    let is_spec_printing =
        !trace.trace_output.is_empty() || trace.states.iter().any(|state| !state.output.is_empty());
    if is_interleaved && is_spec_printing && !output.is_empty() {
        return Err(
            "a counterexample whose states TLC rebuilds between the prints of an ALIAS that prints",
        );
    }
    Ok(output)
}

pub(crate) const DIFF_UNKNOWN: &str =
    "-difftrace of a value TLC may compare otherwise than its text";

fn print_states(
    printer: &mut Printer,
    ir: &tla_ir::Ir,
    states: &[PrintedState],
    labels: &[&str],
    is_counterexample: bool,
) -> Result<(), &'static str> {
    for (position, (state, label)) in states.iter().zip(labels).enumerate() {
        if position > 0 {
            for line in &state.output {
                printer.replayed(ir, line)?;
            }
        }
        // TLC evaluates the ALIAS of a counterexample's states before it reports the violation
        // (`LiveWorker.printTrace`, `LiveCheck.printErrorTrace`), and of a behavior's as it
        // prints each state (`TLCTrace.printTrace`).
        if !is_counterexample {
            for output in &state.alias_output {
                printer.replayed(ir, output)?;
            }
        }
        // Under -difftrace a liveness counterexample diffs every state against the one printed
        // before it (`LiveCheck.printTrace`), while `TLCTrace.printTrace` prints a behavior's
        // first and last states whole.
        let is_diffed = printer.is_diff_trace
            && position > 0
            && (is_counterexample || position + 1 < states.len());
        if is_diffed {
            let previous = &states[position - 1];
            let text = get_diff_text(
                (&state.variables, &state.comparable, state.is_alias_record),
                (
                    &previous.variables,
                    &previous.comparable,
                    previous.is_alias_record,
                ),
            )
            .ok_or(DIFF_UNKNOWN)?;
            printer.state_text(position + 1, label, &text, state.variables.clone());
        } else {
            printer.state(position + 1, label, state.variables.clone());
        }
        printer
            .recorded_trace
            .record_state(position + 1, state.values.clone());
    }
    Ok(())
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
pub(crate) fn properties_headline(ir: &tla_ir::Ir, violated: &[usize]) -> Option<String> {
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

/// TLC's report of the first `_POSSIBLE` predicate the search didn't witness: `_CheckName`
/// prints the counts, and TLC names the predicate with where its definition's body is written
/// (`Tool.checkPostConditionWithContext`, `EC.TLC_POSSIBLE_UNWITNESSED`).
fn print_unwitnessed(
    printer: &mut Printer,
    ir: &tla_ir::Ir,
    config: &ModelConfig,
    position: usize,
    run: &PostconditionRun,
    statistics: &Statistics,
    start: Instant,
) -> Result<i32, String> {
    let predicate = &ir.model.possible[position].name;
    let name = &ir.texts[predicate.name as usize];
    // TLC names the definition the configuration names, which a substitution may replace.
    if config
        .substitutions
        .iter()
        .any(|substitution| *substitution.name == **name)
    {
        return Err("a predicate the configuration substitutes".into());
    }
    let range = predicate
        .definition
        .and_then(|definition| {
            match &ir.nodes.arena[ir.definitions[definition as usize] as usize].kind {
                tla_ir::NodeKind::Definition(definition) => {
                    ir.nodes.arena[definition.body as usize].range
                }
                _ => None,
            }
        })
        .ok_or("a predicate whose definition has no place")?;
    let printed = print_possible_counts(ir, run)?;
    printer.replayed(ir, &printed).map_err(str::to_string)?;
    printer.outcome.status = Some("postcondition-violation");
    printer.report(
        code::POSSIBLE_UNWITNESSED,
        &format!(
            "The _POSSIBLE predicate {name} at line {}, col {} to line {}, col {} of module {} was never witnessed.\nOthers may be unwitnessed too; only witnessed predicates appear with a\nnon-zero count in the record printed above.\nSee https://explain.tlapl.us/possible-conditions for additional details.",
            range.start_line,
            range.start_column,
            range.end_line,
            range.end_column,
            ir.texts[range.module as usize]
        ),
    );
    print_statistics(printer, statistics, start);
    print_finished(printer, start);
    Ok(ASSUMPTION_VIOLATION)
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
    // `pc.getPred().toString()`: SANY names a numeral by its image, as written (`\b101`, `007`),
    // and any other node by where it is written.
    let location = postcondition
        .definition
        .and_then(|definition| {
            let node = ir.definitions[definition as usize];
            match &ir.nodes.arena[node as usize].kind {
                tla_ir::NodeKind::Definition(definition) => {
                    let mut id = definition.body;
                    while let tla_ir::NodeKind::Reference(target) = ir.nodes.arena[id as usize].kind
                    {
                        id = target;
                    }
                    Some(id)
                }
                _ => None,
            }
        })
        .and_then(|id| {
            let body = &ir.nodes.arena[id as usize];
            let range = body.range?;
            let image = match &body.kind {
                tla_ir::NodeKind::Number(_) if let Some(&image) = ir.nodes.numerals.get(&id) => {
                    Some(ir.texts[image as usize].to_string())
                }
                tla_ir::NodeKind::Number(int) => Some(int.to_string()),
                tla_ir::NodeKind::WideNumber(text) => Some(ir.texts[*text as usize].to_string()),
                _ => None,
            };
            Some(match image {
                Some(image)
                    if range.start_line == range.end_line
                        && usize::try_from(range.end_column - range.start_column + 1)
                            .is_ok_and(|width| width == image.len()) =>
                {
                    format!(" at {image}")
                }
                _ => format!(
                    " at line {}, col {} to line {}, col {} of module {}",
                    range.start_line,
                    range.start_column,
                    range.end_line,
                    range.end_column,
                    ir.texts[range.module as usize]
                ),
            })
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

/// `_TLCTrace`'s failure to write the trace's file for the trace exploration spec: the
/// IOException of `ioSerialize`, which TLC reports as a failure of the Java method, within that
/// of the postcondition.
fn print_trace_file_failure(printer: &mut Printer, error: &str) {
    const JAVA_METHOD_FAILED: u32 = 2154;
    let failure = format!(
        "Attempted to apply the operator overridden by the Java method\npublic static final tlc2.value.IValue tlc2.module._TLCTrace.ioSerialize(tlc2.value.IValue,tlc2.value.impl.StringValue) throws java.io.IOException,\nbut it produced the following error:\n{error}"
    );
    let failure = if printer.is_tool {
        format!(
            "@!@!@STARTMSG {JAVA_METHOD_FAILED}:0 @!@!@\n{failure}\n@!@!@ENDMSG {JAVA_METHOD_FAILED} @!@!@"
        )
    } else {
        failure
    };
    printer.report(
        code::POSTCONDITION_FAILED,
        &format!(
            "Evaluating postcondition _TLCTraceSilent at line 28, col 5 to line 28, col 21 of module _TLCTrace failed.\n{failure}"
        ),
    );
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

// Whether evaluating an expression may print: whether it reaches Print or PrintT, itself or
// through the definitions it names.
fn may_print(ir: &tla_ir::Ir, root: tla_ir::NodeId) -> bool {
    let mut seen = std::collections::HashSet::new();
    let mut pending = vec![root];
    while let Some(node) = pending.pop() {
        if !seen.insert(node) {
            continue;
        }
        let kind = &ir.nodes.arena[node as usize].kind;
        match kind {
            tla_ir::NodeKind::Reference(target) => pending.push(*target),
            tla_ir::NodeKind::Definition(definition) => pending.push(definition.body),
            tla_ir::NodeKind::Identifier(name)
            | tla_ir::NodeKind::OperatorReference(name)
            | tla_ir::NodeKind::Apply { name, .. } => match name.resolution {
                tla_ir::Resolution::Definition(index) => {
                    pending.push(ir.definitions[index as usize]);
                }
                tla_ir::Resolution::Builtin(index)
                    if matches!(
                        &*ir.texts[ir.builtins[index as usize].name as usize],
                        "Print" | "PrintT"
                    ) =>
                {
                    return true;
                }
                _ => {}
            },
            _ => {}
        }
        pending.extend(kind.children());
    }
    false
}

// `isTraceRecorded`: whether TLC writes the trace exploration spec, which it parses with the spec.
// Whether TLC writes a trace exploration spec after an error trace: unless -noGenerateSpecTE, -tool
// or -continue says not to, or the spec is one it wrote (`TraceExplorationSpec.isTESpecFile`), or
// where -generateSpecTE says to.
fn is_trace_spec_written(args: &Parsed, spec_path: &str, platform: Platform) -> bool {
    let name = platform.file_name(spec_path);
    args.has("-generateSpecTE")
        || (!args.has("-noGenerateSpecTE")
            && !args.has("-tool")
            && !args.has("-continue")
            && !name.contains("_TTrace"))
}

// Whether TLC records the trace in a file for its trace exploration spec too, with `_TLCTrace`'s
// postcondition.
// The paths TLC makes before it evaluates anything, which the replay doesn't see on the file
// system. `FileUtil.makeMetaDir` makes a directory named for the start time in the -metadir, or in
// `states` in the spec's directory where TLC was given the spec by an absolute path and in the
// working directory otherwise; -recover names the metadir itself. TLC opens its dumps and its
// -userFile as it starts. With -cleanup TLC deletes the working directory's `states` first, which
// leaves none known.
fn get_made_paths(
    args: &Parsed,
    spec_path: &str,
    dumps: &TraceDumps,
    host: &dyn Host,
) -> Option<Vec<std::path::PathBuf>> {
    if args.has("-cleanup") {
        return None;
    }
    let current = host.current_dir();
    let mut made = vec![current.join("states")];
    if let Some(parent) = Path::new(spec_path).parent() {
        made.push(current.join(parent).join("states"));
    }
    for name in ["-metadir", "-recover", "-userFile"] {
        if let Some(path) = args.first(name) {
            made.push(current.join(path));
        }
    }
    made.extend(dumps.get_paths().map(|path| current.join(path)));
    Some(made)
}

fn is_trace_recorded(args: &Parsed, spec_path: &str, platform: Platform) -> bool {
    is_trace_spec_written(args, spec_path, platform) && !args.has("-noGenerateSpecTEBin")
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

pub(crate) const SMALL_SET_UNNAMED: &str =
    "a too-small symmetry set written in a form TLC names by its tokens";

// `TLC_SYMMETRY_SET_TOO_SMALL`, as `symmetry.ts` words it, false where it names a set by an
// image the front end couldn't take from its tokens (`addToSubTwoSizedSymmetrySetList`), which
// it doesn't print.
pub(crate) fn print_small_sets(printer: &mut Printer, names: &[String]) -> bool {
    if names.iter().any(String::is_empty) {
        return false;
    }
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
    true
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
    printer.set_thrown(failure.thrown.clone());
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

/// Keeps the error the library throws where the engine stops as it starts, before it searches,
/// after what the spec printed as it computed the constant definitions and assumptions. The
/// library prints SANY's warnings before it throws, which it doesn't know here; and what the
/// constant definitions the engine leaves out of its startup print as TLC computes them isn't
/// known (fallback.md, "Known wrong outputs").
fn set_startup_thrown(
    printer: &mut Printer,
    thrown: Thrown,
    is_sany_warned: bool,
    is_tlcext_declined: bool,
) {
    if is_sany_warned {
        return;
    }
    printer.set_thrown(Some(if is_tlcext_declined {
        Thrown::NotNative("what the spec prints as TLC computes its constants")
    } else {
        thrown
    }));
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
    crate::transaction::mark_declined(what);
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

    // What one thread and four find in a model whose levels the threads may share, and how many
    // threads shared one.
    fn get_found_on_threads(name: &str, body: &str, config: &str) -> (String, String, usize) {
        let ir = lower(
            name,
            &format!("---- MODULE {name} ----\nEXTENDS Integers, TLC\n{body}====\n"),
            config,
        );
        // The native checker's search, which follows TLC's registers.
        let settings = |threads| Settings {
            threads,
            minimum_shared_level: 1,
            is_violation_reported: true,
            ..Settings::default()
        };
        let (one, _) = get_found(&ir, &settings(1));
        let (four, threads) = get_found(&ir, &settings(4));
        (one, four, threads)
    }

    const COUNTER: &str = "VARIABLES n, d\nInit == n = 0 /\\ d = Drawn\nNext == \\E k \\in 1..10 : n' = (n + k) % 200 /\\ d' = Drawn\nSpec == Init /\\ [][Next]_<<n, d>>\n";

    // A constant that draws TLC computes once as it starts (SpecProcessor.processConstantDefns),
    // and nothing draws again: the threads share the levels and read the value drawn, which is in
    // every state they fingerprint.
    #[test]
    fn shares_the_levels_of_a_search_whose_only_draw_tlc_made_at_startup() {
        let (one, four, threads) = get_found_on_threads(
            "Drawn",
            &format!("Drawn == RandomElement(1..1000000)\n{COUNTER}"),
            "SPECIFICATION Spec\n",
        );
        assert_eq!(four, one);
        assert!(threads > 1);
    }

    // An assumption prints as TLC checks it, before the initial states, and never again.
    #[test]
    fn shares_the_levels_of_a_search_whose_only_print_is_an_assumption() {
        let (one, four, threads) = get_found_on_threads(
            "Assumed",
            &format!("Drawn == 7\nASSUME PrintT(<<\"drawn\", Drawn>>)\n{COUNTER}"),
            "SPECIFICATION Spec\n",
        );
        assert_eq!(four, one);
        assert!(threads > 1);
    }

    // What prints, draws or reads a register as the search goes keeps it on one thread: in the
    // next-state relation, in an invariant, and in an operator, which the compiler keeps by its
    // definition, that both a constant and the next-state relation apply.
    #[test]
    fn keeps_a_search_that_prints_or_draws_as_it_goes_on_one_thread() {
        for (name, body, config) in [
            (
                "Stepped",
                "VARIABLE n\nInit == n = 0\nNext == \\E k \\in 1..10 : n' = (n + k) % 200 /\\ PrintT(k)\nSpec == Init /\\ [][Next]_n\n".to_string(),
                "SPECIFICATION Spec\n",
            ),
            (
                "Checked",
                format!("Drawn == 7\n{COUNTER}Inv == RandomElement({{n}}) = n\n"),
                "SPECIFICATION Spec\nINVARIANT Inv\n",
            ),
            (
                "Applied",
                "Pick(S) == RandomElement(S)\nDrawn == Pick(1..1000000)\nVARIABLES n, d\nInit == n = 0 /\\ d = Drawn\nNext == \\E k \\in 1..10 : n' = (n + k) % 200 /\\ d' = Pick({Drawn})\nSpec == Init /\\ [][Next]_<<n, d>>\n".to_string(),
                "SPECIFICATION Spec\n",
            ),
            (
                "Registered",
                "ASSUME TLCSet(1, 7)\nDrawn == 7\nVARIABLES n, d\nInit == n = 0 /\\ d = Drawn\nNext == \\E k \\in 1..10 : n' = (n + k) % 200 /\\ d' = TLCGet(1)\nSpec == Init /\\ [][Next]_<<n, d>>\n".to_string(),
                "SPECIFICATION Spec\n",
            ),
        ] {
            let (one, four, threads) = get_found_on_threads(name, &body, config);
            assert_eq!(four, one, "{name}");
            assert_eq!(threads, 1, "{name}");
        }
    }

    // An effect a constant has through an operator it applies or a definition its LET makes is
    // compiled with that definition, which the compiler may use again: only one written in the
    // constant's own body counts as made at startup.
    #[test]
    fn keeps_a_search_on_one_thread_where_a_constant_draws_through_another_definition() {
        for (name, constant) in [
            (
                "Through",
                "Pick(S) == RandomElement(S)\nDrawn == Pick(1..1000000)\n",
            ),
            (
                "Let",
                "Drawn == LET Picked == RandomElement(1..1000000) IN Picked\n",
            ),
        ] {
            let (one, four, threads) = get_found_on_threads(
                name,
                &format!("{constant}{COUNTER}"),
                "SPECIFICATION Spec\n",
            );
            assert_eq!(four, one, "{name}");
            assert_eq!(threads, 1, "{name}");
        }
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

// MonolithSpecExtractor.config reads lines independently of the module parser.
fn embedded_config(text: &str, name: &str) -> String {
    let mut active = false;
    let mut result = String::new();
    let lines = text.replace("\r\n", "\n").replace('\r', "\n");
    for line in lines.split('\n') {
        if active && line.starts_with("====") {
            break;
        }
        if !active && embedded_config_header(line, name) {
            active = true;
        } else if active {
            result.push_str(line);
            result.push('\n');
        }
    }
    result.trim_matches(|c| c <= '\u{20}').to_owned()
}

fn embedded_config_header(line: &str, name: &str) -> bool {
    let whitespace = |c: char| matches!(c, ' ' | '\t' | '\n' | '\x0b' | '\x0c' | '\r');
    let Some(rest) = line.strip_prefix("----") else {
        return false;
    };
    let rest = rest.trim_start_matches('-').trim_start_matches(whitespace);
    let Some(rest) = rest.strip_prefix("CONFIG") else {
        return false;
    };
    let trimmed = rest.trim_start_matches(whitespace);
    if trimmed.len() == rest.len() {
        return false;
    }
    let Some(rest) = trimmed.strip_prefix(name) else {
        return false;
    };
    let rest = rest.trim_start_matches(whitespace);
    rest.len() >= 4 && rest.bytes().all(|b| b == b'-')
}

#[cfg(test)]
mod embedded_config_tests {
    use super::embedded_config;

    #[test]
    fn extracts_tlcs_named_section() {
        let text = "---- CONFIG Other ----\nBAD\n====\n---- CONFIG M ----\r\nINIT Init\r\nNEXT Next\r\n==== ignored\r\n---- CONFIG M ----\nBAD\n====";
        assert_eq!(embedded_config(text, "M"), "INIT Init\nNEXT Next");
        assert_eq!(
            embedded_config(" ---- CONFIG M ----\nINIT Init\n====", "M"),
            ""
        );
        assert_eq!(
            embedded_config("---- CONFIG M ---- INIT Init\n====", "M"),
            ""
        );
        assert_eq!(
            embedded_config("---- CONFIG M ----\rINIT Init\r====", "M"),
            "INIT Init"
        );
    }
}
