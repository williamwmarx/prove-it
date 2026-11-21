//! The command line: the TLC options of `prove-it <Spec>`, read as `TLC.handleParameters` reads
//! them, and the Java launch `prove-it [<JVM option>]... tlc2.TLC <option>... <Spec>`
//! that tools running TLC with Java use.

use tla_front::TlcVersion;
use tla_values::fingerprint::POLYNOMIALS;

use crate::host_path::Platform;

pub const USAGE: &str = "Usage: tla-ts <Spec.tla|Spec.cfg|glob>... [-config <Spec.cfg>] [-continue] [-deadlock] [-dump [<format>] <file>] [-fp <num>] [-lncheck <final|default>] [-metadir <directory>] [-nowarning] [-seed <num>] [-tool] [-workers <count|auto>]
       tla-ts tlapm [-N] [--summary] [--strict] [--toolbox <start> <end>] [--line <num>] [--printallobs] [--threads <num>] [--version] [-I <directory>]... [-k] [--noproving] [--nofp] [--nofpl <start> <end>] [--safefp] [--cleanfp] [--usefp <file>] [--cache-dir <directory>] <Module.tla|glob>...
       tla-ts [<JVM option>]... tlc2.TLC <TLC option>... <Spec>
       (-cp tla2tools.jar or -Dtla-ts.tlc=1.7.4 picks the TLC to reproduce)
       tla-ts [<JVM option>]... tla2sany.xml.XMLExporter [-I <directory>]... [-o] [-t] [-r] [-u] <Module.tla>";

const JAVA_MAIN_CLASSES: [&str; 2] = ["tlc2.TLC", "tla2sany.xml.XMLExporter"];

/// What the JVM options in front of TLC's set.
#[derive(Debug, Default, PartialEq)]
pub struct Java {
    pub has_opaque_vm_options: bool,
    pub libraries: Vec<String>,
    pub class_path: Option<String>,
    /// `java.io.tmpdir`, where TLC copies the standard modules it parses.
    pub temporary_directory: Option<String>,
    /// The TLC to reproduce: the one `-Dtla-ts.tlc` names, or else the tla2tools.jar on the class
    /// path is.
    pub tlc_version: Option<TlcVersion>,
    /// The first system property of TLC's that the binary doesn't model.
    pub unmodelled_property: Option<String>,
    /// The names of the system properties the command line sets, which `TLCGet("-Dname")` reads.
    pub properties: Vec<String>,
}

impl Java {
    pub fn origin_profile(&self, tools_jar: Option<&str>) -> tla_front::model::JavaProfile {
        if self.has_opaque_vm_options
            || self.properties.iter().any(|name| is_class_property(name))
            || self
                .class_path
                .as_deref()
                .is_some_and(|path| Some(path) != tools_jar)
        {
            tla_front::model::JavaProfile::Opaque
        } else {
            tla_front::model::JavaProfile::Default
        }
    }
}

/// Where TLC's classes name their system properties.
pub const TLC_PROPERTY_NAMESPACES: [&str; 4] = ["tlc2.", "util.", "tla2sany.", "tlc."];

/// The system properties the command line's options model, which the binary reads only there.
pub const MODELLED_PROPERTIES: [&str; 3] = ["TLA-Library", "java.io.tmpdir", "tla-ts.tlc"];

/// Whether a system property is the JVM's own, such as `java.class.path` or
/// `java.system.class.loader`, which may change which classes TLC loads, and how. One in no
/// namespace of the JVM's or TLC's is read only by code that asks for it by name: TLC's own
/// properties decline (`Java::unmodelled_property`) and so does `TLCGet("-Dname")` of one.
pub fn is_class_property(name: &str) -> bool {
    !MODELLED_PROPERTIES.contains(&name)
        && ["java.", "javax.", "jdk.", "sun.", "com.sun."]
            .iter()
            .any(|namespace| name.starts_with(namespace))
}

/// Whether a system property is one of TLC's that the binary doesn't model.
pub fn is_unmodelled_property(name: &str) -> bool {
    TLC_PROPERTY_NAMESPACES
        .iter()
        .any(|namespace| name.starts_with(namespace))
        && !SILENT_PROPERTIES.contains(&name)
}

/// The properties of TLC's that change nothing TLC prints: both only reach the execution
/// statistics TLC reports home (TLC.java:1710, ExecutionStatisticsCollector.java:74 and 205).
const SILENT_PROPERTIES: [&str; 2] = ["tlc2.TLC.ide", "util.ExecutionStatisticsCollector.id"];

/// A Java launch: the main class, its arguments and the JVM's options.
#[derive(Debug, PartialEq)]
pub struct Launch {
    pub main_class: String,
    pub args: Vec<String>,
    pub java: Java,
}

pub fn get_java_launch(args: &[String], platform: Platform) -> Option<Launch> {
    let mut java = Java::default();
    let mut index = 0;
    while index < args.len() {
        let arg = &args[index];
        let rest = |from: usize| args.get(from..).unwrap_or_default().to_vec();
        if let Some(property) = arg.strip_prefix("-D") {
            let name = property.split_once('=').map_or(property, |(name, _)| name);
            java.properties.push(name.into());
        }
        if arg == "-cp" || arg == "-classpath" || arg == "--class-path" {
            index += 1;
            java.class_path = args.get(index).cloned();
        } else if arg == "-jar" {
            java.class_path = args.get(index + 1).cloned();
            return Some(Launch {
                main_class: "tlc2.TLC".into(),
                args: rest(index + 2),
                java,
            });
        } else if let Some(libraries) = arg
            .strip_prefix("-DTLA-Library=")
            .or((arg == "-DTLA-Library").then_some(""))
        {
            // The JVM keeps a property's last value, which TLC splits as Java's String.split
            // does, dropping the empty paths at the end (`SimpleFilenameToStream.parsePaths`).
            let delimiter = platform.delimiter();
            let mut paths: Vec<String> = libraries.split(delimiter).map(String::from).collect();
            while libraries.contains(delimiter) && paths.last().is_some_and(String::is_empty) {
                paths.pop();
            }
            java.libraries = paths;
        } else if let Some(directory) = arg.strip_prefix("-Djava.io.tmpdir=") {
            java.temporary_directory = Some(directory.into());
        } else if let Some(version) = arg.strip_prefix("-Dtla-ts.tlc=") {
            java.tlc_version = Some(if version == "1.7.4" {
                TlcVersion::V1_7_4
            } else {
                TlcVersion::Master
            });
        } else if let Some(property) = arg.strip_prefix("-D") {
            let name = property.split_once('=').map_or(property, |(name, _)| name);
            if is_unmodelled_property(name) {
                java.unmodelled_property.get_or_insert_with(|| name.into());
            }
        } else if arg.starts_with("-X") {
            java.has_opaque_vm_options |= is_class_vm_option(arg);
        } else {
            let is_launch = index > 0 || JAVA_MAIN_CLASSES.contains(&arg.as_str());
            return is_launch.then(|| Launch {
                main_class: arg.clone(),
                args: rest(index + 1),
                java,
            });
        }
        index += 1;
    }
    None
}

/// Whether a JVM option of the `-X` kind can change which classes TLC loads: one that adds to the
/// boot class path, or reads more options from a file. A heap or stack size, a collector or a log
/// changes none of them.
pub fn is_class_vm_option(option: &str) -> bool {
    ["-Xbootclasspath", "-XX:Flags=", "-XX:VMOptionsFile="]
        .iter()
        .any(|prefix| option.starts_with(prefix))
}

/// The command line's invariant, `-inv` or `-invlevel`: its expression, and the modules TLC adds
/// to the root module's EXTENDS for it.
pub const INVARIANT: &str = "-inv";

/// The command line's postcondition `module!operator`, kept as its module and its operator.
pub const POST_CONDITION: &str = "-postCondition";

/// Why a command line starts no check.
#[derive(Debug, PartialEq)]
pub enum Stop {
    /// What `TLC.printErrorMsg` reports, and whether `-tool` came before it.
    Error { message: String, is_tool: bool },
    /// What TLC does with the command line that the binary doesn't do.
    NotNative(String),
    /// `-help` or `-h`, where TLC prints its usage text and stops (`TLC.printUsage`).
    Usage,
}

/// The options TLC reads that the binary doesn't model. TLC reads the last three in any case.
const UNMODELLED: [&str; 6] = [
    "-generate",
    "-terse",
    "-view",
    "-debug",
    "-inv",
    "-debugger",
];

/// `String.split(",")`: the pieces between commas, without the empty ones at the end, and no
/// piece of an empty text but itself.
fn split_like_java(text: &str) -> Vec<&str> {
    let mut pieces: Vec<&str> = text.split(',').collect();
    if !text.is_empty() {
        while pieces.last().is_some_and(|piece| piece.is_empty()) {
            pieces.pop();
        }
    }
    pieces
}

/// The most fingerprint bits -fpbits takes in the binary.
const MODELLED_FP_BITS: i32 = 8;

pub const DUMP_TRACE: &str = "-dumpTrace";

/// The formats of -dumpTrace, as `TLC.DumpTraceFormat` names them.
const DUMP_FORMATS: [&str; 8] = [
    "json",
    "tla",
    "tlc",
    "tlcplain",
    "tlcTESpec",
    "tlcaction",
    "dot",
    "cbor",
];

/// The formats whose files the binary writes. TLC's others are modules that import the
/// CommunityModules, which its jar lacks (`checkDumpTraceModules`).
const NATIVE_DUMP_FORMATS: [&str; 2] = ["tlc", "json"];

/// The format -dumpTrace names, by its flag in any case (`DumpTraceFormat.of`).
fn get_dump_format(flag: &str) -> Option<&'static str> {
    DUMP_FORMATS
        .into_iter()
        .find(|format| format.eq_ignore_ascii_case(flag))
}

/// How the parsed options mark a code of SANY's.
const SANY_CODE: &str = "sany:";

/// The options and specs of a check, as `TLC.handleParameters` reads them.
#[derive(Debug, Default)]
pub struct Parsed {
    pub options: Vec<(String, Vec<String>)>,
    pub positionals: Vec<String>,
}

fn error(message: String, is_tool: bool) -> Stop {
    Stop::Error { message, is_tool }
}

/// The value an option takes, or the error TLC reports where none follows.
fn take(args: &[String], index: &mut usize, missing: &str, is_tool: bool) -> Result<String, Stop> {
    let value = args
        .get(*index)
        .ok_or_else(|| error(format!("Error: {missing}"), is_tool))?;
    *index += 1;
    Ok(value.clone())
}

impl Parsed {
    /// Reads the arguments in order and stops at the first that TLC rejects, as TLC does. With
    /// `is_tlc` the command line is `tlc2.TLC`'s, which takes one spec; without it, Prove It's
    /// own, which takes several without `-config`. Malformed invocations report TLC's first error.
    pub fn parse(args: &[String], is_tlc: bool) -> Result<Self, Stop> {
        let result = Self::parse_options(args, is_tlc);
        if is_tlc {
            return result;
        }
        match result {
            // An option that took `-config` for its value, as TLC takes it, leaves the
            // configuration's file to be read as TLC reads it, a second input.
            Ok(parsed)
                if (parsed.positionals.is_empty() && !args.is_empty())
                    || (parsed.has("-config") && parsed.positionals.len() > 1)
                    || parsed
                        .options
                        .iter()
                        .any(|(_, values)| values.iter().any(|value| value == "-config")) =>
            {
                Self::parse_options(args, true)
            }
            Err(reason) => match Self::parse_options(args, true) {
                // TLC may reject the second input before it reaches a later invalid option.
                Err(error @ Stop::Error { .. }) => Err(error),
                _ => Err(reason),
            },
            other => other,
        }
    }

    fn parse_options(args: &[String], is_tlc: bool) -> Result<Self, Stop> {
        let mut parsed = Self::default();
        match Self::read_options(args, is_tlc, &mut parsed) {
            // TLC prints the notice of an absolute -fpmem before it reports a later option.
            Err(Stop::Error { .. } | Stop::Usage) if parsed.is_fpmem_absolute() => Err(
                Stop::NotNative("an error in the command line after -fpmem's notice".into()),
            ),
            Err(stop) => Err(stop),
            Ok(()) => Ok(parsed),
        }
    }

    /// The codes every time the option is given lists.
    /// The codes of SANY's an option names, kept apart from TLC's.
    pub fn get_sany_codes(&self, name: &str) -> Vec<u32> {
        self.options
            .iter()
            .filter(|(option, _)| option == name)
            .flat_map(|(_, values)| {
                values
                    .iter()
                    .filter_map(|code| code.strip_prefix(SANY_CODE)?.parse().ok())
            })
            .collect()
    }

    pub fn get_codes(&self, name: &str) -> Vec<u32> {
        self.options
            .iter()
            .filter(|(option, _)| option == name)
            .flat_map(|(_, values)| values.iter().filter_map(|code| code.parse().ok()))
            .collect()
    }

    /// How many times an -fpmem gives an absolute memory size, whose deprecation TLC prints each
    /// time it reads such an option.
    pub fn count_fpmem_absolute(&self) -> usize {
        self.options
            .iter()
            .filter(|(option, values)| {
                option == "-fpmem" && values.get(1).is_some_and(|v| v == "true")
            })
            .count()
    }

    /// Whether an -fpmem gives an absolute memory size.
    pub fn is_fpmem_absolute(&self) -> bool {
        self.count_fpmem_absolute() > 0
    }

    fn read_options(args: &[String], is_tlc: bool, parsed: &mut Self) -> Result<(), Stop> {
        let mut index = 0;
        while index < args.len() {
            let arg = args[index].as_str();
            index += 1;
            let is_tool = parsed.has("-tool");
            // Java reads digits and compares letters of any script, and throws on no characters.
            if arg.is_empty() || !arg.is_ascii() {
                return Err(Stop::NotNative(format!("the argument {arg:?}")));
            }
            let values = match arg {
                "-modelcheck"
                | "-terse"
                | "-view"
                | "-deadlock"
                | "-nowarning"
                | "-continue"
                | "-tool"
                | "-difftrace"
                | "-noGenerateSpecTE"
                | "-noGenerateSpecTEBin" => Vec::new(),
                "-generateSpecTE" => {
                    if args.get(index).is_some_and(|next| next == "nomonolith") {
                        index += 1;
                    }
                    Vec::new()
                }
                "-lncheck" => {
                    let strategy = take(
                        args,
                        &mut index,
                        "expect a strategy such as final for -lncheck option.",
                        is_tool,
                    )?;
                    vec![strategy]
                }
                // `Paths.get` of the path, which fails on a NUL alone.
                "-teSpecOutDir" => {
                    let path = take(
                        args,
                        &mut index,
                        "expected a path for -teSpecOutDir option.",
                        is_tool,
                    )?;
                    if path.contains('\0') {
                        return Err(error(
                            format!("Error: invalid path for -teSpecOutDir option: {path}"),
                            is_tool,
                        ));
                    }
                    vec![path]
                }
                "-metadir" => vec![take(
                    args,
                    &mut index,
                    "need to specify the metadata directory.",
                    is_tool,
                )?],
                "-config" => {
                    let name = take(
                        args,
                        &mut index,
                        "expect a file name for -config option.",
                        is_tool,
                    )?;
                    vec![format!(
                        "{}.cfg",
                        name.strip_suffix(".cfg").unwrap_or(&name)
                    )]
                }
                "-seed" => {
                    let seed = take(args, &mut index, "seed required.", is_tool)?;
                    if !seed.is_ascii() {
                        return Err(Stop::NotNative(format!("the seed {seed:?}")));
                    }
                    if seed.parse::<i64>().is_err() {
                        return Err(error(
                            format!("Error: An integer for seed required. But encountered {seed}"),
                            is_tool,
                        ));
                    }
                    vec![seed]
                }
                // TLC takes the next argument as the simulation's settings when it names one:
                // `num=`, `file=`, `stats=` or `sched`, separated by commas. It ignores any other.
                // -generate simulates too, generating one successor of an action at random
                // (`Tool.probabilistic`), and takes the same settings.
                "-simulate" | "-generate" => {
                    if arg == "-generate" {
                        parsed.options.push((arg.into(), Vec::new()));
                    }
                    let Some(settings) = args.get(index).filter(|next| {
                        ["stats=", "file=", "num=", "sched"]
                            .iter()
                            .any(|setting| next.contains(setting))
                    }) else {
                        parsed.options.push(("-simulate".into(), Vec::new()));
                        continue;
                    };
                    index += 1;
                    let mut values = Vec::new();
                    let mut file = None;
                    let mut unsupported = None;
                    for setting in settings.split(',') {
                        if let Some(number) = setting.strip_prefix("num=") {
                            // `Long.parseLong` of the setting without each `num=` in it, which
                            // throws past TLC's checks where it isn't a number.
                            let number = number.replace("num=", "");
                            if number.parse::<i64>().is_err() {
                                return Err(Stop::NotNative(format!("-simulate {setting}")));
                            }
                            values = vec![number];
                        } else if setting.starts_with("file=") {
                            file = Some(setting);
                        } else if ["stats=basic", "stats=full", "sched=rl", "sched=rlaction"]
                            .contains(&setting)
                        {
                            unsupported.get_or_insert(setting);
                        }
                    }
                    // TLC writes each trace to a file only of a bounded number of them, and
                    // rejects the command line otherwise once it has read the settings. The
                    // number is `TLC.traceNum`, which an earlier -simulate's `num=` set and a
                    // later one without it keeps.
                    let number = values.first().or_else(|| {
                        parsed
                            .options
                            .iter()
                            .rev()
                            .filter(|(option, _)| option == "-simulate")
                            .find_map(|(_, values)| values.first())
                    });
                    if file.is_some()
                        && number.is_none_or(|number| number.parse::<i64>() == Ok(i64::MAX))
                    {
                        return Err(error(
                            "Error: You need to specify a 'num' argument when using the 'file' argument, for example: '\"num=5,file=test.txt\"'.".into(),
                            is_tool,
                        ));
                    }
                    if let Some(setting) = file.or(unsupported) {
                        return Err(Stop::NotNative(format!("-simulate {setting}")));
                    }
                    parsed.options.push(("-simulate".into(), values));
                    continue;
                }
                "-depth" => {
                    let depth = take(args, &mut index, "trace length required.", is_tool)?;
                    if !depth.is_ascii() {
                        return Err(Stop::NotNative(format!("the trace length {depth:?}")));
                    }
                    if depth.parse::<i32>().is_err() {
                        return Err(error(
                            format!(
                                "Error: An integer for trace length required. But encountered {depth}"
                            ),
                            is_tool,
                        ));
                    }
                    vec![depth]
                }
                "-aril" => {
                    let aril = take(args, &mut index, "aril required.", is_tool)?;
                    if !aril.is_ascii() {
                        return Err(Stop::NotNative(format!("the aril {aril:?}")));
                    }
                    if aril.parse::<i64>().is_err() {
                        return Err(error(
                            format!("Error: An integer for aril required. But encountered {aril}"),
                            is_tool,
                        ));
                    }
                    vec![aril]
                }
                "-workers" => {
                    let workers = take(
                        args,
                        &mut index,
                        "expect an integer or 'auto' for -workers option.",
                        is_tool,
                    )?;
                    if !workers.is_ascii() {
                        return Err(Stop::NotNative(format!("the worker number {workers:?}")));
                    }
                    if !is_auto(&workers) {
                        let Ok(count) = workers.parse::<i32>() else {
                            return Err(error(
                                format!(
                                    "Error: worker number or 'auto' required. But encountered {workers}"
                                ),
                                is_tool,
                            ));
                        };
                        if count < 1 {
                            return Err(error(
                                "Error: at least one worker required.".into(),
                                is_tool,
                            ));
                        }
                    }
                    vec![workers]
                }
                // `Integer.parseInt(minutes) * 60 * 1000`, which overflows as Java's ints do.
                "-coverage" => {
                    let minutes = take(
                        args,
                        &mut index,
                        "coverage report interval required.",
                        is_tool,
                    )?;
                    if !minutes.is_ascii() {
                        return Err(Stop::NotNative(format!("-coverage {minutes:?}")));
                    }
                    let Ok(number) = minutes.parse::<i32>() else {
                        return Err(error(
                            format!(
                                "Error: An integer for coverage report interval required. But encountered {minutes}"
                            ),
                            is_tool,
                        ));
                    };
                    if number.wrapping_mul(60).wrapping_mul(1000) < 0 {
                        return Err(error(
                            "Error: expect a nonnegative integer for -coverage option.".into(),
                            is_tool,
                        ));
                    }
                    vec![minutes]
                }
                "-dfid" => {
                    let limit = take(
                        args,
                        &mut index,
                        "expect a nonnegative integer for -dfid option.",
                        is_tool,
                    )?;
                    if !limit.is_ascii() {
                        return Err(Stop::NotNative(format!("-dfid {limit:?}")));
                    }
                    let Ok(number) = limit.parse::<i32>() else {
                        return Err(error(
                            format!(
                                "Error: expect a nonnegative integer for -dfid option. But encountered {limit}"
                            ),
                            is_tool,
                        ));
                    };
                    if number < 0 {
                        return Err(error(
                            "Error: expect a nonnegative integer for -dfid option.".into(),
                            is_tool,
                        ));
                    }
                    vec![limit]
                }
                "-fp" => {
                    let polynomial = take(
                        args,
                        &mut index,
                        "expect an integer for -fp option.",
                        is_tool,
                    )?;
                    if !polynomial.is_ascii() {
                        return Err(Stop::NotNative(format!("-fp {polynomial:?}")));
                    }
                    let Ok(number) = polynomial.parse::<i32>() else {
                        return Err(error(
                            format!(
                                "Error: A number for -fp is required. But encountered {polynomial}"
                            ),
                            is_tool,
                        ));
                    };
                    if !(0..POLYNOMIALS.len() as i32).contains(&number) {
                        return Err(error(
                            format!(
                                "Error: The number for -fp must be between 0 and {} (inclusive).",
                                POLYNOMIALS.len() - 1
                            ),
                            is_tool,
                        ));
                    }
                    vec![polynomial]
                }
                // TLC splits the list at commas and trims each code before `Integer.parseInt`,
                // whose exception it reports, and sorts each code as its own or SANY's
                // (`classifyMessageCode`).
                "-suppressMessages" | "-messagesAsErrors" => {
                    let Some(list) = args.get(index) else {
                        return Err(error(
                            format!(
                                "Error: {arg} requires a comma-separated list of message codes."
                            ),
                            is_tool,
                        ));
                    };
                    index += 1;
                    let mut codes = Vec::new();
                    for item in split_like_java(list) {
                        let item = item.trim_matches(|c: char| c <= ' ');
                        // `Integer.parseInt` reads a decimal digit of any script.
                        if !item.is_ascii() {
                            return Err(Stop::NotNative(format!("{arg} {item:?}")));
                        }
                        let Ok(code) = item.parse::<i32>() else {
                            return Err(error(
                                format!("Error: For input string: \"{item}\""),
                                is_tool,
                            ));
                        };
                        // EC's codes lie between UNIT_TEST and TLC_MODULE_OVERRIDE_STDOUT, and
                        // SANY's between them too; the only other negative one is UNKNOWN, -1
                        // (`EC.isKnownCode` reads every static int of EC).
                        if !(-123456..=20000).contains(&code) || (-123456 < code && code < -1) {
                            return Err(error(
                                format!("Error: unknown message code: {code}"),
                                is_tool,
                            ));
                        }
                        // `classifyMessageCode`: a code EC doesn't know is one of SANY's
                        // `ErrorCode`s, of which -suppressMessages rejects an error's at once.
                        if let Some((_, is_error)) = crate::messages::get_sany_code(code) {
                            if arg == "-suppressMessages" && is_error {
                                return Err(error(
                                    format!(
                                        "Error: code {code} is an error and cannot be suppressed."
                                    ),
                                    is_tool,
                                ));
                            }
                            codes.push(format!("{SANY_CODE}{code}"));
                            continue;
                        }
                        if !crate::messages::is_controlled_code(code) {
                            return Err(Stop::NotNative(format!("{arg} {code}")));
                        }
                        codes.push(code.to_string());
                    }
                    codes
                }
                // The states directory TLC deletes, and the files it compresses, are none the
                // binary reads; TLC deletes `states` in the working directory, which the binary
                // leaves alone (check.rs).
                "-cleanup" | "-gzip" => Vec::new(),
                // `Integer.parseInt(minutes) * 1000 * 60`, which overflows as Java's ints do. A
                // duration other than zero checkpoints, which the binary doesn't.
                "-checkpoint" => {
                    let minutes = take(args, &mut index, "checkpoint interval required.", is_tool)?;
                    if !minutes.is_ascii() {
                        return Err(Stop::NotNative(format!("-checkpoint {minutes:?}")));
                    }
                    let Ok(number) = minutes.parse::<i32>() else {
                        return Err(error(
                            format!(
                                "Error: An integer for checkpoint interval is required. But encountered {minutes}"
                            ),
                            is_tool,
                        ));
                    };
                    let duration = number.wrapping_mul(1000).wrapping_mul(60);
                    if duration < 0 {
                        return Err(error(
                            "Error: expect a nonnegative integer for -checkpoint option.".into(),
                            is_tool,
                        ));
                    }
                    if duration != 0 {
                        return Err(Stop::NotNative(format!("-checkpoint {minutes}")));
                    }
                    vec![minutes]
                }
                // The fingerprint set's memory, which changes nothing TLC prints but the notice of
                // an absolute amount (TLC.java:1105), which TLC prints as it reads the option.
                // `Double.parseDouble` reads what Rust's parser does of a plain decimal, and
                // fails on text with no digit that spells neither NaN nor Infinity; the binary
                // declines other text.
                "-fpmem" => {
                    let size = take(args, &mut index, "fpset memory size required.", is_tool)?;
                    let is_decimal = {
                        let unsigned = size.strip_prefix(['+', '-']).unwrap_or(&size);
                        let (mantissa, exponent) = unsigned
                            .split_once(['e', 'E'])
                            .map_or((unsigned, None), |(mantissa, exponent)| {
                                (mantissa, Some(exponent))
                            });
                        let (whole, fraction) = mantissa.split_once('.').unwrap_or((mantissa, ""));
                        (!whole.is_empty() || !fraction.is_empty())
                            && whole.bytes().all(|byte| byte.is_ascii_digit())
                            && fraction.bytes().all(|byte| byte.is_ascii_digit())
                            && exponent.is_none_or(|exponent| {
                                let digits = exponent.strip_prefix(['+', '-']).unwrap_or(exponent);
                                !digits.is_empty()
                                    && digits.bytes().all(|byte| byte.is_ascii_digit())
                            })
                    };
                    let rejected = error(
                        format!(
                            "Error: An positive integer or a fraction for fpset memory size/percentage required. But encountered {size}"
                        ),
                        is_tool,
                    );
                    if !is_decimal {
                        if !size.bytes().any(|byte| byte.is_ascii_digit())
                            && !size.contains("NaN")
                            && !size.contains("Infinity")
                        {
                            return Err(rejected);
                        }
                        return Err(Stop::NotNative(format!("-fpmem {size}")));
                    }
                    let Ok(number) = size.parse::<f64>() else {
                        return Err(Stop::NotNative(format!("-fpmem {size}")));
                    };
                    if number < 0.0 {
                        return Err(rejected);
                    }
                    parsed
                        .options
                        .push((arg.into(), vec![size, (number > 1.0).to_string()]));
                    continue;
                }
                // How many fingerprint sets TLC divides its memory into, which changes nothing it
                // prints for few; the binary declines more, where the Java heap's size decides
                // whether TLC can allocate them (MultiFPSet.getNestedFPSets).
                "-fpbits" => {
                    let bits = take(args, &mut index, "fpbits required.", is_tool)?;
                    if !bits.is_ascii() {
                        return Err(Stop::NotNative(format!("-fpbits {bits:?}")));
                    }
                    let Ok(number) = bits.parse::<i32>() else {
                        return Err(error(
                            format!(
                                "Error: An integer for fpbits required. But encountered {bits}"
                            ),
                            is_tool,
                        ));
                    };
                    if !(0..=30).contains(&number) {
                        return Err(error(
                            format!(
                                "Error: Value in interval [0, 30] for fpbits required. But encountered {bits}"
                            ),
                            is_tool,
                        ));
                    }
                    if number > MODELLED_FP_BITS {
                        return Err(Stop::NotNative(format!("-fpbits {bits}")));
                    }
                    vec![bits]
                }
                // TLC takes a format only when the next argument starts with dot and a file
                // follows, and throws where nothing follows -dump.
                "-dump" => {
                    let rest = &args[index..];
                    if rest.is_empty() {
                        return Err(Stop::NotNative("-dump".into()));
                    }
                    // `Class.forName` of a class that implements `IStateWriter`, which only
                    // TLC's own classes do in the jar: TLC rejects any other, unless the class
                    // path holds more (check.rs).
                    if let Some(class) = rest[0].strip_prefix("class,") {
                        if class.starts_with("tlc2.") {
                            return Err(Stop::NotNative("-dump class,".into()));
                        }
                        return Err(error(
                            format!(
                                "Trying to instantiate a custom IStateWriter implementation {}.",
                                rest[0].replace("class,", "")
                            ),
                            is_tool,
                        ));
                    }
                    let count = if rest.len() > 1 && rest[0].starts_with("dot") {
                        2
                    } else {
                        1
                    };
                    index += count;
                    rest[..count].to_vec()
                }
                // TLC rejects a bound that isn't a positive int (`TLCGlobals.isValidSetSize`); the
                // binary declines a valid one, whose bound it doesn't model.
                "-maxSetSize" => {
                    let bound = take(args, &mut index, "maxSetSize required.", is_tool)?;
                    if !bound.is_ascii() {
                        return Err(Stop::NotNative(format!("-maxSetSize {bound:?}")));
                    }
                    let Ok(number) = bound.parse::<i32>() else {
                        return Err(error(
                            format!(
                                "Error: An integer for maxSetSize required. But encountered {bound}"
                            ),
                            is_tool,
                        ));
                    };
                    if number < 1 {
                        return Err(error(
                            format!(
                                "Error: Value in interval [0, {}] for maxSetSize required. But encountered {bound}",
                                i32::MAX
                            ),
                            is_tool,
                        ));
                    }
                    return Err(Stop::NotNative(format!("the TLC option {arg}")));
                }
                // `Integer.parseInt` of the level, where TLC throws past the last argument; the
                // binary declines a valid one, whose runtime invariant it doesn't model.
                "-invlevel" => {
                    let Some(level) = args.get(index) else {
                        return Err(Stop::NotNative(format!("the TLC option {arg}")));
                    };
                    if !level.is_ascii() {
                        return Err(Stop::NotNative(format!("-invlevel {level:?}")));
                    }
                    if level.parse::<i32>().is_err() {
                        return Err(error(
                            format!(
                                "Error: An integer for -invlevel required. But encountered {level}"
                            ),
                            is_tool,
                        ));
                    }
                    // TLC pastes the level as written into an expression of the modules TLC and
                    // Naturals, which it adds to the root module's EXTENDS; a sign there is
                    // Integers' or nobody's.
                    if !level.bytes().all(|byte| byte.is_ascii_digit()) {
                        return Err(Stop::NotNative(format!("-invlevel {level}")));
                    }
                    index += 1;
                    parsed.options.push((
                        INVARIANT.into(),
                        vec![
                            format!(
                                "LET _T == INSTANCE TLC _N == INSTANCE Naturals IN _N!<(_T!TLCGet(\"level\"), {level})"
                            ),
                            "TLC".into(),
                            "Naturals".into(),
                        ],
                    ));
                    continue;
                }
                // An invariant TLC parses in a module of its own that extends the root module,
                // adding to the root module's EXTENDS each module the expression names after
                // INSTANCE (`TLC.handleParameters`, `RuntimeInvariantTemplate`); TLC throws where
                // no expression follows.
                "-inv" => {
                    let Some(expression) = args.get(index) else {
                        return Err(Stop::NotNative(format!("the TLC option {arg}")));
                    };
                    index += 1;
                    let mut values = vec![expression.clone()];
                    let mut rest = expression.as_str();
                    while let Some(at) = rest.find("INSTANCE") {
                        rest = &rest[at + "INSTANCE".len()..];
                        let name: String = rest
                            .trim_start_matches(|character: char| character.is_ascii_whitespace())
                            .chars()
                            .take_while(|&character| {
                                character.is_ascii_alphanumeric() || character == '_'
                            })
                            .collect();
                        let is_spaced =
                            rest.starts_with(|character: char| character.is_ascii_whitespace());
                        if is_spaced && !name.is_empty() && !values[1..].contains(&name) {
                            values.push(name);
                        }
                    }
                    parsed.options.push((INVARIANT.into(), values));
                    continue;
                }
                // TLC takes `module!operator` in any case of the flag and checks its form before
                // it reads the next option.
                _ if arg.eq_ignore_ascii_case("-postCondition") => {
                    let rejected = |message: String| Err(error(message, is_tool));
                    let Some(module_bang_op) = args.get(index) else {
                        return rejected(
                            "Error: Module!Operator for postCondition required.".into(),
                        );
                    };
                    if !module_bang_op.contains('!') {
                        return rejected(format!(
                            "Module!Operator for postCondition required. Encountered: {module_bang_op}"
                        ));
                    }
                    // `String.split("!")`, which drops the empty pieces at the end.
                    let mut parts: Vec<&str> = module_bang_op.split('!').collect();
                    while parts.last().is_some_and(|part| part.is_empty()) {
                        parts.pop();
                    }
                    let [module, def] = parts[..] else {
                        return rejected(format!(
                            "Module!Operator for postCondition must be of the form module!operator. Encountered: {module_bang_op}"
                        ));
                    };
                    if module.is_empty() {
                        return rejected(format!(
                            "Module name for postCondition required. Encountered: {module_bang_op}"
                        ));
                    }
                    if module.contains('.') {
                        return rejected(format!(
                            "Module name for postCondition must not contain a dot. Encountered: {module}"
                        ));
                    }
                    if def.contains('.') {
                        return rejected(format!(
                            "Operator name for postCondition must not contain a dot. Encountered: {def}"
                        ));
                    }
                    let values = vec![module.to_string(), def.to_string()];
                    index += 1;
                    parsed.options.push((POST_CONDITION.into(), values));
                    continue;
                }
                _ if arg.eq_ignore_ascii_case("-noTE") => {
                    parsed
                        .options
                        .push(("-noGenerateSpecTE".into(), Vec::new()));
                    continue;
                }
                _ if arg.eq_ignore_ascii_case("-noTEBin") => {
                    parsed
                        .options
                        .push(("-noGenerateSpecTEBin".into(), Vec::new()));
                    continue;
                }
                _ if arg.eq_ignore_ascii_case(DUMP_TRACE) => {
                    // TLC takes a format and a file, and knows the format by its flag in any case.
                    let [format, file] = args.get(index..index + 2).unwrap_or_default() else {
                        return Err(error(
                            "Error: A format and a file name for dumping traces required.".into(),
                            is_tool,
                        ));
                    };
                    index += 2;
                    let Some(format) = get_dump_format(format) else {
                        return Err(error(
                            format!("Error: Unknown format {format} given to -dumpTrace."),
                            is_tool,
                        ));
                    };
                    if !NATIVE_DUMP_FORMATS.contains(&format) {
                        return Err(Stop::NotNative(format!(
                            "-dumpTrace {format}, whose module needs the CommunityModules"
                        )));
                    }
                    parsed
                        .options
                        .push((DUMP_TRACE.into(), vec![format.into(), file.clone()]));
                    continue;
                }
                "-help" | "-h" => return Err(Stop::Usage),
                // The directory of the checkpoint to recover from, which TLC reads as it starts
                // (`UniqueString.internTbl.recover`).
                "-recover" => vec![take(
                    args,
                    &mut index,
                    "need to specify the metadata directory for recovery.",
                    is_tool,
                )?],
                // The file Print and PrintT write to in place of the console, which TLC creates as
                // it reads the option (check.rs creates it).
                "-userFile" => vec![take(
                    args,
                    &mut index,
                    "need to specify the full qualified file.",
                    is_tool,
                )?],
                // TLC takes a format and a file, and knows the format in any case; the binary
                // declines the trace's constraint a known one adds.
                _ if arg.eq_ignore_ascii_case("-loadTrace") => {
                    let [format, _] = args.get(index..index + 2).unwrap_or_default() else {
                        return Err(error(
                            "Error: A format and a file name for loading traces required.".into(),
                            is_tool,
                        ));
                    };
                    if !format.eq_ignore_ascii_case("tlc") && !format.eq_ignore_ascii_case("json") {
                        return Err(error(
                            format!("Error: Unknown format {format} given to -loadTrace."),
                            is_tool,
                        ));
                    }
                    return Err(Stop::NotNative(format!("the TLC option {arg}")));
                }
                _ if UNMODELLED.contains(&arg) => {
                    return Err(Stop::NotNative(format!("the TLC option {arg}")));
                }
                _ if arg.starts_with('-') => {
                    return Err(error(format!("Error: unrecognized option: {arg}"), is_tool));
                }
                _ => {
                    if let Some(first) = parsed.positionals.first().filter(|_| is_tlc) {
                        return Err(error(
                            format!(
                                "Error: more than one input files: {} and {arg}",
                                first.strip_suffix(".tla").unwrap_or(first)
                            ),
                            is_tool,
                        ));
                    }
                    parsed.positionals.push(arg.into());
                    continue;
                }
            };
            parsed.options.push((arg.into(), values));
        }
        // TLC rejects -nowarning with codes to suppress, and a code both suppressed and made an
        // error, after it reads every option (`handleParameters`).
        let suppressed = parsed.get_codes("-suppressMessages");
        let sany_suppressed = parsed.get_sany_codes("-suppressMessages");
        if parsed.has("-nowarning") && !(suppressed.is_empty() && sany_suppressed.is_empty()) {
            return Err(error(
                "Error: -nowarning already suppresses all warnings, making -suppressMessages \
                 redundant. Remove -nowarning to suppress only the specified messages, or remove \
                 -suppressMessages to suppress all warnings."
                    .into(),
                parsed.has("-tool"),
            ));
        }
        let mut both: Vec<u32> = parsed
            .get_codes("-messagesAsErrors")
            .into_iter()
            .filter(|code| suppressed.contains(code))
            .collect();
        both.sort_unstable();
        both.dedup();
        match both[..] {
            [] => {}
            // A HashSet's order, which the binary follows for one code.
            [code] => {
                return Err(error(
                    format!(
                        "Error: The following codes were set to both -suppressMessages and -messagesAsErrors: [{code}]"
                    ),
                    parsed.has("-tool"),
                ));
            }
            _ => {
                return Err(Stop::NotNative(
                    "several codes both suppressed and made errors".into(),
                ));
            }
        }
        // Then SANY's codes, named as `ErrorCode` names them.
        let mut both: Vec<u32> = parsed
            .get_sany_codes("-messagesAsErrors")
            .into_iter()
            .filter(|code| sany_suppressed.contains(code))
            .collect();
        both.sort_unstable();
        both.dedup();
        match both[..] {
            [] => {}
            [code] => {
                let (name, _) =
                    crate::messages::get_sany_code(code as i32).expect("a code SANY names");
                return Err(error(
                    format!(
                        "Error: The following codes were set to both -suppressMessages and -messagesAsErrors: [{name}]"
                    ),
                    parsed.has("-tool"),
                ));
            }
            _ => {
                return Err(Stop::NotNative(
                    "several codes both suppressed and made errors".into(),
                ));
            }
        }
        // What SANY suppresses or fails with is followed for its linter's warning alone, whose
        // code no message of its parser or semantic analysis has.
        let is_lint_code = |code: &u32| *code == tla_front::report::RECORD_FIELD_NAME_CLASH;
        if !(sany_suppressed.iter().all(is_lint_code)
            && parsed
                .get_sany_codes("-messagesAsErrors")
                .iter()
                .all(is_lint_code))
        {
            return Err(Stop::NotNative(
                "SANY's message codes of -suppressMessages or -messagesAsErrors".into(),
            ));
        }
        // `MP.printWarning` fails with a code of -messagesAsErrors even under -nowarning, where
        // the binary doesn't compute the warnings.
        if parsed.has("-nowarning") && !parsed.get_codes("-messagesAsErrors").is_empty() {
            return Err(Stop::NotNative("-messagesAsErrors with -nowarning".into()));
        }
        if is_tlc && parsed.positionals.is_empty() {
            return Err(error(
                "Error: Missing input TLA+ module.".into(),
                parsed.has("-tool"),
            ));
        }
        Ok(())
    }

    pub fn has(&self, name: &str) -> bool {
        self.options.iter().any(|(option, _)| option == name)
    }

    /// The values of the last time the option is given.
    pub fn get(&self, name: &str) -> Option<&[String]> {
        self.options
            .iter()
            .rev()
            .find(|(option, _)| option == name)
            .map(|(_, values)| values.as_slice())
    }

    pub fn first(&self, name: &str) -> Option<&str> {
        self.get(name)?.first().map(String::as_str)
    }
}

/// Whether -workers asks for a worker a core, as TLC's `trim().toLowerCase().equals("auto")`.
pub fn is_auto(workers: &str) -> bool {
    workers
        .trim_matches(|character| character <= ' ')
        .eq_ignore_ascii_case("auto")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn strings(args: &[&str]) -> Vec<String> {
        args.iter().map(|&arg| arg.to_string()).collect()
    }

    #[test]
    fn reads_a_java_launch() {
        let libraries = "-DTLA-Library=/a:/b".to_string();
        let launch = get_java_launch(
            &strings(&[
                &libraries,
                "-Xmx4g",
                "-Djava.io.tmpdir=/t",
                "tlc2.TLC",
                "-tool",
                "Spec",
            ]),
            Platform::Unix,
        )
        .expect("a launch");
        assert_eq!(launch.java.temporary_directory.as_deref(), Some("/t"));
        assert_eq!(launch.main_class, "tlc2.TLC");
        assert_eq!(launch.args, strings(&["-tool", "Spec"]));
        assert_eq!(launch.java.libraries, strings(&["/a", "/b"]));
        // A Windows host separates the paths with `;`, which a drive's `:` is part of.
        let windows = get_java_launch(
            &strings(&["-DTLA-Library=C:\\a;D:\\b;", "tlc2.TLC", "Spec"]),
            Platform::Windows,
        )
        .expect("a launch");
        assert_eq!(windows.java.libraries, strings(&["C:\\a", "D:\\b"]));
        let last = get_java_launch(
            &strings(&[&libraries, "-DTLA-Library=/c", "tlc2.TLC", "Spec"]),
            Platform::Unix,
        )
        .expect("a launch");
        assert_eq!(last.java.libraries, strings(&["/c"]));
        assert_eq!(launch.java.unmodelled_property, None);
        assert_eq!(
            get_java_launch(&strings(&["Spec.tla", "-tool"]), Platform::Unix),
            None
        );
        let properties = get_java_launch(
            &strings(&[
                "-Dtlc2.TLC.ide=vscode",
                "-Dutil.ExecutionStatisticsCollector.id=abc",
                "-Dfile.encoding=UTF-8",
                "-Dtlc2.tool.fp.FPSet.impl=tlc2.tool.fp.MSBDiskFPSet",
                "-Dtlc2.tool.ModelChecker.BAQueue=true",
                "tlc2.TLC",
                "Spec",
            ]),
            Platform::Unix,
        )
        .expect("a launch");
        assert_eq!(
            properties.java.unmodelled_property.as_deref(),
            Some("tlc2.tool.fp.FPSet.impl")
        );
        let jar = get_java_launch(&strings(&["-jar", "tla2tools.jar", "Spec"]), Platform::Unix)
            .expect("a jar");
        assert_eq!(jar.java.class_path.as_deref(), Some("tla2tools.jar"));
        assert_eq!(jar.args, strings(&["Spec"]));
    }

    fn parse(args: &[&str]) -> Result<Parsed, Stop> {
        Parsed::parse(&strings(args), true)
    }

    fn get_error(args: &[&str]) -> String {
        match parse(args) {
            Err(Stop::Error { message, .. }) => message,
            other => panic!("no error: {other:?}"),
        }
    }

    #[test]
    fn reads_the_options_it_models() {
        let parsed = parse(&[
            "-seed",
            "5",
            "-noTE",
            "-dump",
            "dot",
            "out",
            "Spec.tla",
            "-seed",
            "7",
            "-NOTEBIN",
            "-generateSpecTE",
            "nomonolith",
            "-config",
            "Model",
            "-workers",
            " AUTO ",
            "-coverage",
            "+3",
        ])
        .expect("options");
        assert_eq!(parsed.positionals, strings(&["Spec.tla"]));
        assert_eq!(parsed.first("-seed"), Some("7"));
        assert_eq!(
            parsed.get("-dump"),
            Some(strings(&["dot", "out"]).as_slice())
        );
        assert!(parsed.has("-noGenerateSpecTE") && parsed.has("-noGenerateSpecTEBin"));
        assert_eq!(parsed.first("-config"), Some("Model.cfg"));
        assert!(parsed.first("-workers").is_some_and(is_auto));
        assert_eq!(parsed.first("-coverage"), Some("+3"));
        // 71583 minutes overflow into a positive int, which TLC takes.
        assert!(parse(&["-coverage", "71583", "Spec"]).is_ok());
        let dotted = parse(&["Spec", "-config", "Model.cfg", "-dump", "dot"]).expect("options");
        assert_eq!(dotted.first("-config"), Some("Model.cfg"));
        assert_eq!(dotted.get("-dump"), Some(strings(&["dot"]).as_slice()));
        assert_eq!(dotted.positionals, strings(&["Spec"]));
    }

    // Each message is what TLC at d8fb231 prints for the command line.
    #[test]
    fn rejects_what_tlc_rejects() {
        for (args, message) in [
            (&["-foo", "Spec"][..], "unrecognized option: -foo"),
            (
                &["Spec", "-config"],
                "expect a file name for -config option.",
            ),
            (&["-workers", "0", "Spec"], "at least one worker required."),
            (
                &["-workers", "x", "Spec"],
                "worker number or 'auto' required. But encountered x",
            ),
            (
                &["-workers", " 1", "Spec"],
                "worker number or 'auto' required. But encountered  1",
            ),
            (
                &["-workers"],
                "expect an integer or 'auto' for -workers option.",
            ),
            (
                &["-fp", "131", "Spec"],
                "The number for -fp must be between 0 and 130 (inclusive).",
            ),
            (
                &["-fp", "x", "Spec"],
                "A number for -fp is required. But encountered x",
            ),
            (&["-fp"], "expect an integer for -fp option."),
            (&["-seed"], "seed required."),
            (&["-depth"], "trace length required."),
            (
                &["-depth", "x", "Spec"],
                "An integer for trace length required. But encountered x",
            ),
            (&["-aril"], "aril required."),
            (
                &["-aril", "1.5", "Spec"],
                "An integer for aril required. But encountered 1.5",
            ),
            (
                &["-seed", "x", "Spec"],
                "An integer for seed required. But encountered x",
            ),
            (
                &["-lncheck"],
                "expect a strategy such as final for -lncheck option.",
            ),
            (&["-metadir"], "need to specify the metadata directory."),
            (&["-coverage"], "coverage report interval required."),
            (
                &["-coverage", "x", "Spec"],
                "An integer for coverage report interval required. But encountered x",
            ),
            (
                &["-coverage", "-1", "Spec"],
                "expect a nonnegative integer for -coverage option.",
            ),
            (
                &["-coverage", "40000", "Spec"],
                "expect a nonnegative integer for -coverage option.",
            ),
            (
                &["-coverage", "2147483648", "Spec"],
                "An integer for coverage report interval required. But encountered 2147483648",
            ),
            (
                &["Stop.tla", "Two"],
                "more than one input files: Stop and Two",
            ),
            (&["-deadlock"], "Missing input TLA+ module."),
            (
                &["Spec", "-dumpTrace", "tlc"],
                "A format and a file name for dumping traces required.",
            ),
            (
                &["-dumpTrace", "xml", "out", "Spec"],
                "Unknown format xml given to -dumpTrace.",
            ),
            // The format and the file are the two arguments after the option, whatever they are.
            (&["-dumpTrace", "tlc", "Spec"], "Missing input TLA+ module."),
        ] {
            assert_eq!(get_error(args), format!("Error: {message}"));
        }
        // TLC stops at the first argument it rejects, and marks the error only after -tool.
        assert_eq!(
            parse(&["-tool", "-seed", "x", "-foo"]).err(),
            Some(Stop::Error {
                message: "Error: An integer for seed required. But encountered x".into(),
                is_tool: true
            })
        );
        assert!(matches!(
            parse(&["-seed", "x", "-tool", "Spec"]),
            Err(Stop::Error { is_tool: false, .. })
        ));
    }

    #[test]
    fn rejects_invalid_dfid_limits() {
        for (args, message) in [
            (
                &["-dfid"][..],
                "Error: expect a nonnegative integer for -dfid option.",
            ),
            (
                &["-dfid", "-1", "Spec"][..],
                "Error: expect a nonnegative integer for -dfid option.",
            ),
            (
                &["-dfid", "x", "Spec"][..],
                "Error: expect a nonnegative integer for -dfid option. But encountered x",
            ),
            (
                &["-dfid", "2147483648", "Spec"][..],
                "Error: expect a nonnegative integer for -dfid option. But encountered 2147483648",
            ),
        ] {
            assert_eq!(get_error(args), message);
        }
    }

    #[test]
    fn rejects_a_trace_file_without_a_number_of_traces() {
        let message = "Error: You need to specify a 'num' argument when using the 'file' argument, for example: '\"num=5,file=test.txt\"'.";
        for args in [
            &["-simulate", "file=trace", "Spec"][..],
            &["-simulate", "file=trace,stats=basic", "Spec"],
            &["-simulate", "num=9223372036854775807,file=trace", "Spec"],
            &[
                "-simulate",
                "num=1",
                "-simulate",
                "num=9223372036854775807,file=t",
                "Spec",
            ],
            &["-simulate", "file=trace", "-simulate", "num=1", "Spec"],
        ] {
            assert_eq!(get_error(args), message);
        }
    }

    #[test]
    fn reads_dfid_depth() {
        let parsed = parse(&["-dfid", "3", "Spec"]).expect("valid depth");
        assert_eq!(parsed.first("-dfid"), Some("3"));
    }

    #[test]
    fn declines_what_it_does_not_model() {
        for args in [
            &["-debug", "Spec"][..],
            &["-simulate", "num=3,file=trace", "Spec"],
            // An earlier -simulate's number of traces holds for a later one's file.
            &["-simulate", "num=1", "-simulate", "file=trace", "Spec"],
            &[
                "-simulate",
                "num=1",
                "-simulate",
                "-simulate",
                "file=trace",
                "Spec",
            ],
            &["-simulate", "stats=basic", "Spec"],
            &["-simulate", "num=x", "Spec"],
            &["-maxSetSize", "10", "Spec"],
            &["-invlevel", "+3", "Spec"],
            &["-invlevel"],
            &["-inv"],
            &["-loadTrace", "json", "trace.json", "Spec"],
            &["-dump", "class,tlc2.util.NoopStateWriter", "Spec"],
            &["-DUMPTRACE", "dot", "out.dot", "Spec"],
            &["-dumpTrace", "TLCTESPEC", "out.tla", "Spec"],
            &["-dump"],
            &["", "Spec"],
            &["-noTEB\u{131}n", "Spec"],
        ] {
            assert!(matches!(parse(args), Err(Stop::NotNative(_))), "{args:?}");
        }
    }

    #[test]
    fn rejects_the_values_tlc_rejects() {
        for (args, message) in [
            (
                &["-maxSetSize", "0"][..],
                "Error: Value in interval [0, 2147483647] for maxSetSize required. But encountered 0",
            ),
            (
                &["-maxSetSize", "2147483648"],
                "Error: An integer for maxSetSize required. But encountered 2147483648",
            ),
            (&["-maxSetSize"], "Error: maxSetSize required."),
            (
                &["-invlevel", "x"],
                "Error: An integer for -invlevel required. But encountered x",
            ),
            (
                &["-POSTCONDITION", "Op"],
                "Module!Operator for postCondition required. Encountered: Op",
            ),
            (
                &["-postCondition", "a!b!c"],
                "Module!Operator for postCondition must be of the form module!operator. Encountered: a!b!c",
            ),
            (
                &["-postCondition", "!"],
                "Module!Operator for postCondition must be of the form module!operator. Encountered: !",
            ),
            (
                &["-postCondition", "!b"],
                "Module name for postCondition required. Encountered: !b",
            ),
            (
                &["-postCondition", "a.b!c"],
                "Module name for postCondition must not contain a dot. Encountered: a.b",
            ),
            (
                &["-postCondition", "a!b.c"],
                "Operator name for postCondition must not contain a dot. Encountered: b.c",
            ),
            (
                &["-postCondition"],
                "Error: Module!Operator for postCondition required.",
            ),
            (
                &["-teSpecOutDir"],
                "Error: expected a path for -teSpecOutDir option.",
            ),
        ] {
            assert_eq!(get_error(args), message, "{args:?}");
        }
        // `String.split` drops the empty pieces at the end.
        let parsed = parse(&["-postCondition", "a!b!", "Spec"]).expect("options");
        assert_eq!(
            parsed.get(POST_CONDITION),
            Some(&["a".to_string(), "b".to_string()][..])
        );
        assert_eq!(
            get_error(&["-dump", "class,Writer", "Spec"]),
            "Trying to instantiate a custom IStateWriter implementation Writer."
        );
        assert_eq!(
            get_error(&["-loadTrace", "xml", "in.xml", "Spec"]),
            "Error: Unknown format xml given to -loadTrace."
        );
        assert_eq!(
            get_error(&["-userFile"]),
            "Error: need to specify the full qualified file."
        );
        assert_eq!(
            get_error(&["-recover"]),
            "Error: need to specify the metadata directory for recovery."
        );
        assert!(matches!(
            parse(&["-deadlock", "-help", "-bogus"]),
            Err(Stop::Usage)
        ));
    }

    #[test]
    fn reads_the_options_tlc_reads_as_it_reads_them() {
        let parsed = parse(&[
            "-terse",
            "-view",
            "-generate",
            "num=2",
            "-inv",
            "LET S == INSTANCE Sequences IN S!Len(<<>>) = 0",
            "-invlevel",
            "4",
            "Spec",
        ])
        .expect("options");
        assert!(parsed.has("-terse") && parsed.has("-view") && parsed.has("-generate"));
        assert_eq!(parsed.get("-simulate"), Some(&["2".to_string()][..]));
        let invariants: Vec<_> = parsed
            .options
            .iter()
            .filter(|(option, _)| option == INVARIANT)
            .map(|(_, values)| values.clone())
            .collect();
        assert_eq!(invariants[0][1..], ["Sequences".to_string()]);
        assert_eq!(
            invariants[1],
            [
                "LET _T == INSTANCE TLC _N == INSTANCE Naturals IN _N!<(_T!TLCGet(\"level\"), 4)",
                "TLC",
                "Naturals"
            ]
        );
    }

    #[test]
    fn reads_each_dump_trace_in_order() {
        let parsed = parse(&[
            "-DumpTrace",
            "JSON",
            "a.json",
            "Spec",
            "-dumptrace",
            "tlc",
            "-tool",
        ])
        .expect("options");
        assert_eq!(
            parsed.options,
            [
                ("-dumpTrace".to_string(), strings(&["json", "a.json"])),
                ("-dumpTrace".to_string(), strings(&["tlc", "-tool"])),
            ]
        );
        assert!(!parsed.has("-tool"));
    }

    #[test]
    fn reads_the_simulation_settings() {
        let parsed = parse(&[
            "-simulate",
            "num=4,sched",
            "-depth",
            "-1",
            "-aril",
            "2",
            "Spec",
        ])
        .expect("options");
        assert_eq!(parsed.get("-simulate"), Some(strings(&["4"]).as_slice()));
        assert_eq!(parsed.first("-depth"), Some("-1"));
        assert_eq!(parsed.first("-aril"), Some("2"));
        assert_eq!(parsed.positionals, strings(&["Spec"]));
        // TLC takes the next argument as settings only where it names one.
        let bare = parse(&["-simulate", "Spec"]).expect("options");
        assert_eq!(bare.get("-simulate"), Some(&[][..]));
        assert_eq!(bare.positionals, strings(&["Spec"]));
    }

    #[test]
    fn takes_several_specs_as_its_own_command_line() {
        let parsed = Parsed::parse(&strings(&["One.tla", "Two.cfg"]), false).expect("options");
        assert_eq!(parsed.positionals, strings(&["One.tla", "Two.cfg"]));
        assert!(
            Parsed::parse(&[], false)
                .expect("options")
                .positionals
                .is_empty()
        );
    }
}

#[cfg(test)]
mod origin_profile_tests {
    use super::*;
    use tla_front::model::JavaProfile;

    #[test]
    fn parsed_launch_profile_separates_known_options_from_unknown_lookup() {
        for (arguments, expected) in [
            (
                vec!["-cp", "tla2tools.jar", "tlc2.TLC", "M"],
                JavaProfile::Default,
            ),
            (
                vec![
                    "-Xss2m",
                    "-XX:+UseParallelGC",
                    "-cp",
                    "tla2tools.jar",
                    "tlc2.TLC",
                    "M",
                ],
                JavaProfile::Default,
            ),
            (
                vec!["-cp", "extra:tla2tools.jar", "tlc2.TLC", "M"],
                JavaProfile::Opaque,
            ),
            (
                vec!["-Djava.class.path=extra:tla2tools.jar", "tlc2.TLC", "M"],
                JavaProfile::Opaque,
            ),
            (
                vec![
                    "-Xmx4g",
                    "-Xms1g",
                    "-Xss4m",
                    "-XX:+UseG1GC",
                    "-cp",
                    "tla2tools.jar",
                    "tlc2.TLC",
                    "M",
                ],
                JavaProfile::Default,
            ),
            (
                vec![
                    "-XX:VMOptionsFile=options",
                    "-cp",
                    "tla2tools.jar",
                    "tlc2.TLC",
                    "M",
                ],
                JavaProfile::Opaque,
            ),
            (
                vec![
                    "-Xbootclasspath/a:extra",
                    "-cp",
                    "tla2tools.jar",
                    "tlc2.TLC",
                    "M",
                ],
                JavaProfile::Opaque,
            ),
        ] {
            let arguments: Vec<_> = arguments.into_iter().map(String::from).collect();
            let launch = get_java_launch(&arguments, Platform::NATIVE).unwrap();
            assert_eq!(launch.java.origin_profile(Some("tla2tools.jar")), expected);
        }
    }
}
