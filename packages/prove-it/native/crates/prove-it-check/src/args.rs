//! The command line: the TLC options of `prove-it <Spec>`, read as `TLC.handleParameters` reads
//! them, and the Java launch `prove-it [<JVM option>]... tlc2.TLC <option>... <Spec>`
//! that tools running TLC with Java use.

use tla_values::fingerprint::POLYNOMIALS;

pub const USAGE: &str = "Usage: tla-ts <Spec.tla|Spec.cfg|glob>... [-config <Spec.cfg>] [-continue] [-deadlock] [-dump [<format>] <file>] [-fp <num>] [-lncheck <final|default>] [-metadir <directory>] [-nowarning] [-seed <num>] [-tool] [-workers <count|auto>]
       tla-ts tlapm [-N] [--summary] [--strict] [--toolbox <start> <end>] [--line <num>] [--printallobs] [--threads <num>] [--version] [-I <directory>]... [-k] [--noproving] [--nofp] [--nofpl <start> <end>] [--safefp] [--cleanfp] [--usefp <file>] [--cache-dir <directory>] <Module.tla|glob>...
       tla-ts [<JVM option>]... tlc2.TLC <TLC option>... <Spec>
       (-cp tla2tools.jar or -Dtla-ts.tlc=1.7.4 picks the TLC to reproduce)
       tla-ts [<JVM option>]... tla2sany.xml.XMLExporter [-I <directory>]... [-o] [-t] [-r] [-u] <Module.tla>";

/// What separates the directories of a path list, as Node's `path.delimiter`.
const PATH_DELIMITER: char = if cfg!(windows) { ';' } else { ':' };

const JAVA_MAIN_CLASSES: [&str; 2] = ["tlc2.TLC", "tla2sany.xml.XMLExporter"];

/// What the JVM options in front of TLC's set.
#[derive(Debug, Default, PartialEq)]
pub struct Java {
    pub libraries: Vec<String>,
    pub class_path: Option<String>,
    /// `java.io.tmpdir`, where TLC copies the standard modules it parses.
    pub temporary_directory: Option<String>,
    pub is_174: bool,
    /// The first system property of TLC's that the binary doesn't model.
    pub unmodelled_property: Option<String>,
    /// The names of the system properties the command line sets, which `TLCGet("-Dname")` reads.
    pub properties: Vec<String>,
}

/// Where TLC's classes name their system properties.
const TLC_PROPERTY_NAMESPACES: [&str; 4] = ["tlc2.", "util.", "tla2sany.", "tlc."];

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

pub fn get_java_launch(args: &[String]) -> Option<Launch> {
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
        } else if let Some(libraries) = arg.strip_prefix("-DTLA-Library=") {
            java.libraries
                .extend(libraries.split(PATH_DELIMITER).map(String::from));
        } else if let Some(directory) = arg.strip_prefix("-Djava.io.tmpdir=") {
            java.temporary_directory = Some(directory.into());
        } else if let Some(version) = arg.strip_prefix("-Dtla-ts.tlc=") {
            java.is_174 = version == "1.7.4";
        } else if let Some(property) = arg.strip_prefix("-D") {
            let name = property.split_once('=').map_or(property, |(name, _)| name);
            if TLC_PROPERTY_NAMESPACES
                .iter()
                .any(|namespace| name.starts_with(namespace))
                && !SILENT_PROPERTIES.contains(&name)
            {
                java.unmodelled_property.get_or_insert_with(|| name.into());
            }
        } else if !arg.starts_with("-X") {
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

/// Why a command line starts no check.
#[derive(Debug, PartialEq)]
pub enum Stop {
    /// What `TLC.printErrorMsg` reports, and whether `-tool` came before it.
    Error { message: String, is_tool: bool },
    /// What TLC does with the command line that the binary doesn't do.
    NotNative(String),
}

/// The options TLC reads that the binary doesn't model. TLC reads the last three in any case.
const UNMODELLED: [&str; 26] = [
    "-simulate",
    "-generate",
    "-difftrace",
    "-cleanup",
    "-suppressMessages",
    "-messagesAsErrors",
    "-gzip",
    "-terse",
    "-view",
    "-debug",
    "-inv",
    "-invlevel",
    "-debugger",
    "-teSpecOutDir",
    "-help",
    "-h",
    "-coverage",
    "-checkpoint",
    "-depth",
    "-aril",
    "-maxSetSize",
    "-recover",
    "-userFile",
    "-dfid",
    "-fpmem",
    "-fpbits",
];
const UNMODELLED_IN_ANY_CASE: [&str; 3] = ["-loadTrace", "-dumpTrace", "-postCondition"];

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
    /// own, which takes several.
    pub fn parse(args: &[String], is_tlc: bool) -> Result<Self, Stop> {
        let mut parsed = Self::default();
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
                | "-deadlock"
                | "-nowarning"
                | "-continue"
                | "-tool"
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
                    // With off, TLC checks no temporal property (LiveCheck.java:238).
                    if strategy.eq_ignore_ascii_case("off") {
                        return Err(Stop::NotNative("-lncheck off".into()));
                    }
                    vec![strategy]
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
                // TLC takes a format only when the next argument starts with dot and a file
                // follows, and throws where nothing follows -dump.
                "-dump" => {
                    let rest = &args[index..];
                    if rest.is_empty() || rest[0].starts_with("class,") {
                        return Err(Stop::NotNative("-dump".into()));
                    }
                    let count = if rest.len() > 1 && rest[0].starts_with("dot") {
                        2
                    } else {
                        1
                    };
                    index += count;
                    rest[..count].to_vec()
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
                _ if UNMODELLED.contains(&arg)
                    || UNMODELLED_IN_ANY_CASE
                        .iter()
                        .any(|option| arg.eq_ignore_ascii_case(option)) =>
                {
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
        if is_tlc && parsed.positionals.is_empty() {
            return Err(error(
                "Error: Missing input TLA+ module.".into(),
                parsed.has("-tool"),
            ));
        }
        Ok(parsed)
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
        let libraries = format!("-DTLA-Library=/a{PATH_DELIMITER}/b");
        let launch = get_java_launch(&strings(&[
            &libraries,
            "-Xmx4g",
            "-Djava.io.tmpdir=/t",
            "tlc2.TLC",
            "-tool",
            "Spec",
        ]))
        .expect("a launch");
        assert_eq!(launch.java.temporary_directory.as_deref(), Some("/t"));
        assert_eq!(launch.main_class, "tlc2.TLC");
        assert_eq!(launch.args, strings(&["-tool", "Spec"]));
        assert_eq!(launch.java.libraries, strings(&["/a", "/b"]));
        assert_eq!(launch.java.unmodelled_property, None);
        assert_eq!(get_java_launch(&strings(&["Spec.tla", "-tool"])), None);
        let properties = get_java_launch(&strings(&[
            "-Dtlc2.TLC.ide=vscode",
            "-Dutil.ExecutionStatisticsCollector.id=abc",
            "-Dfile.encoding=UTF-8",
            "-Dtlc2.tool.fp.FPSet.impl=tlc2.tool.fp.MSBDiskFPSet",
            "-Dtlc2.tool.ModelChecker.BAQueue=true",
            "tlc2.TLC",
            "Spec",
        ]))
        .expect("a launch");
        assert_eq!(
            properties.java.unmodelled_property.as_deref(),
            Some("tlc2.tool.fp.FPSet.impl")
        );
        let jar = get_java_launch(&strings(&["-jar", "tla2tools.jar", "Spec"])).expect("a jar");
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
            (
                &["-seed", "x", "Spec"],
                "An integer for seed required. But encountered x",
            ),
            (
                &["-lncheck"],
                "expect a strategy such as final for -lncheck option.",
            ),
            (&["-metadir"], "need to specify the metadata directory."),
            (
                &["Stop.tla", "Two"],
                "more than one input files: Stop and Two",
            ),
            (&["-deadlock"], "Missing input TLA+ module."),
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
    fn declines_what_it_does_not_model() {
        for args in [
            &["-difftrace", "Spec"][..],
            &["-simulate", "Spec"],
            &["-coverage", "1", "Spec"],
            &["-maxSetSize", "10", "Spec"],
            &["-dfid", "3", "Spec"],
            &["-DUMPTRACE", "json", "out.json", "Spec"],
            &["-lncheck", "OFF", "Spec"],
            &["-dump"],
            &["-dump", "class,Writer", "Spec"],
            &["", "Spec"],
            &["-noTEB\u{131}n", "Spec"],
        ] {
            assert!(matches!(parse(args), Err(Stop::NotNative(_))), "{args:?}");
        }
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
