//! `prove-it tla2sany.xml.XMLExporter ...`: `exportXml` in `src/cli/xml-exporter.ts`, SANY's
//! XMLExporter of TLC master, which prints a spec's semantic tree as XML.

use std::path::Path;

use tla_front::TlcVersion;
use tla_front::errors::FrontError;
use tla_front::get_standard_module;
use tla_front::sany::export::{EXIT_UNCAUGHT_EXCEPTION, ExportFlags, export_xml};

use crate::messages::Output;

const SUCCESS: i32 = 0;
const ARGS_PARSING_FAILURE: i32 = EXIT_UNCAUGHT_EXCEPTION;

fn bold(text: &str) -> String {
    format!("\x1b[1m{text}\x1b[0m")
}

/// The usage that XMLExporter.printUsage prints with UsageGenerator.
fn get_usage() -> String {
    let options = [
        (
            "-I",
            "Include; use given directory path to resolve module dependencies.",
        ),
        ("-help", "Print this usage information."),
        ("-o", "Offline mode; skip XML schema validation step."),
        (
            "-r",
            "Restrict mode; include only declarations and definitions of the specified module, excluding extended or instantiated modules.",
        ),
        ("-t", "Terse; format XML output without tabs or newlines."),
        (
            "-u",
            "Uncomment; process boxed comments and single-line comments (\\*) in pre-comments to extract their content.",
        ),
    ];
    let tips = [
        "Only one root TLA+ file can be parsed per run.",
        "Multiple directory search paths can be given by providing multiple -I arguments.",
        "XML schema validation does not require network access.",
    ];
    let mut lines = vec![
        String::new(),
        bold("NAME"),
        String::new(),
        "\ttla2sany.xml.XMLExporter - Emit SANY's parse tree as XML - Version 2.2 created 08 July 2020".to_owned(),
        String::new(),
        String::new(),
        bold("SYNOPSIS"),
        String::new(),
        format!(
            "\t{} [{}] [{}] FILE",
            bold("tla2sany.xml.XMLExporter"),
            bold("-Iortu"),
            bold("-help")
        ),
        String::new(),
        bold("DESCRIPTION"),
        String::new(),
        "\tGiven a TLA+ file, parse that file with SANY then translate the module's semantic parse tree to XML, including all the modules depended on. The XML is printed to stdout and its output format is given by an XML Schema file (.xsd) found at https://proofs.tlapl.us/doc/web/sany.xsd.".to_owned(),
        String::new(),
        bold("OPTIONS"),
        String::new(),
    ];
    lines.extend(
        options
            .iter()
            .map(|(flag, description)| format!("\t{}\n\t\t{description}", bold(flag))),
    );
    lines.extend([String::new(), bold("TIPS"), String::new()]);
    lines.extend(
        tips.iter()
            .flat_map(|tip| [format!("\t{tip}"), String::new()]),
    );
    lines.push(String::new());
    lines.join("\n")
}

fn print_usage_error(output: &mut Output<'_>, message: &str) -> i32 {
    let _ = write!(output.err, "ERROR: {message}\n{}", get_usage());
    ARGS_PARSING_FAILURE
}

/// The flags and -I directories XMLExporter reads before the last argument, which names the
/// module. It skips an argument it doesn't know, which then counts as another module.
enum ParsedArgs {
    Parsed {
        flags: Vec<String>,
        includes: Vec<String>,
    },
    MissingInclude,
    SeveralFiles,
}

fn parse_args(args: &[String]) -> ParsedArgs {
    let mut flags = Vec::new();
    let mut includes = Vec::new();
    let mut last_flag: Option<usize> = None;
    let mut index = 0;
    while index + 1 < args.len() {
        let arg = &args[index];
        if ["-o", "-t", "-r", "-u"].contains(&arg.as_str()) {
            flags.push(arg.clone());
            last_flag = Some(index);
        } else if arg == "-I" {
            index += 1;
            if index + 2 > args.len() {
                return ParsedArgs::MissingInclude;
            }
            includes.push(args[index].clone());
            last_flag = Some(index);
        }
        index += 1;
    }
    if last_flag.map_or(-1, |index| index as i64) != args.len() as i64 - 2 {
        return ParsedArgs::SeveralFiles;
    }
    ParsedArgs::Parsed { flags, includes }
}

/// Runs XMLExporter with the arguments after its class name.
pub fn run_xml_exporter(args: &[String], output: &mut Output<'_>) -> Result<i32, String> {
    if args.is_empty() {
        return Ok(print_usage_error(
            output,
            "at least one .tla file must be given",
        ));
    }
    let (flags, includes) = match parse_args(args) {
        ParsedArgs::MissingInclude => {
            return Ok(print_usage_error(
                output,
                "the -I flag must be followed by a directory and at least one .tla file",
            ));
        }
        ParsedArgs::SeveralFiles => {
            return Ok(print_usage_error(
                output,
                "Only one TLA file to check allowed!",
            ));
        }
        ParsedArgs::Parsed { flags, includes } => (flags, includes),
    };
    let name = &args[args.len() - 1];
    if name == "-help" {
        let _ = write!(output.out, "{}", get_usage());
        return Ok(SUCCESS);
    }
    let file_name = if name.ends_with(".tla") {
        name.clone()
    } else {
        format!("{name}.tla")
    };
    // SANY looks for each module in the working directory, then in the -I directories, which
    // XMLExporter passes in place of TLA-Library, then among its standard modules.
    let directories: Vec<&Path> = std::iter::once(Path::new("."))
        .chain(includes.iter().map(Path::new))
        .collect();
    let path = directories
        .iter()
        .map(|directory| directory.join(&file_name))
        .find(|path| output.host.is_file(path));
    let root = Path::new(&file_name)
        .file_stem()
        .and_then(|stem| stem.to_str())
        .unwrap_or_default()
        .to_owned();
    let source = match &path {
        Some(path) => output
            .host
            .read_text(path)
            .ok_or_else(|| "a root module whose file can't be read".to_owned())?,
        None => get_standard_module(&root, TlcVersion::Master)
            .ok_or_else(|| "a root module without a file".to_owned())?
            .to_owned(),
    };
    let host = output.host;
    let load_module = |module: &str| host.load_module(&directories, module);
    let flags = ExportFlags {
        is_restricted: flags.iter().any(|flag| flag == "-r"),
        is_uncommented: flags.iter().any(|flag| flag == "-u"),
        is_terse: flags.iter().any(|flag| flag == "-t"),
    };
    let exported =
        export_xml(&root, &source, name, &load_module, flags).map_err(|error| match error {
            FrontError::NotYet(reason) => reason,
            other => format!("{other:?}"),
        })?;
    let _ = write!(output.err, "{}", exported.stderr);
    let _ = write!(output.out, "{}", exported.stdout);
    Ok(exported.exit_code)
}
