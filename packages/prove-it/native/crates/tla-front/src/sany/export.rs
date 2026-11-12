//! `exportXml` in `src/cli/xml-exporter.ts` after its arguments: what SANY's XMLExporter prints for
//! a spec, given the root module's text.

use std::rc::Rc;

use crate::parser::extract_module;
use crate::report::{ReportOptions, get_sany_text_of};
use crate::sany::generator::{GenerationOptions, generate_sany_specification};
use crate::sany::levels::{LevelCheck, check_module_levels};
use crate::sany::xml::{XML_EXPORT_SPEC_PARSING_FAILURE, XmlExportOptions, export_sany_xml};
use crate::sany::{Result, not_yet};
use crate::{TlcVersion, get_standard_module};

/// What XMLExporter prints and its exit status.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExportOutput {
    pub stdout: String,
    pub stderr: String,
    pub exit_code: i32,
}

/// The export of the spec whose root module `root` has the text `source`. `file_name` is the
/// argument XMLExporter was given, and `load_module` reads another module's file. SANY's report
/// decides whether SANY accepts the spec; the graph is built only then, and a message of the
/// graph's generator that the report didn't print is `NotYet`.
pub fn export_xml(
    root: &str,
    source: &str,
    file_name: &str,
    load_module: &dyn Fn(&str) -> Option<String>,
    options: &XmlExportOptions,
) -> Result<ExportOutput> {
    let report = get_sany_text_of(
        root,
        source,
        &ReportOptions {
            version: TlcVersion::Master,
            file_name: Some(file_name),
            load_module,
            describe_file: &|_, _| Ok(String::new()),
            root_extendees: &[],
            is_xml_export: true,
        },
    )?;
    // XMLExporter then prints the exception's Java stack trace, which isn't written.
    if report.exception.is_some() {
        return not_yet("the stack trace of SANY's generator exception");
    }
    if report.is_failed {
        return Ok(ExportOutput {
            stdout: String::new(),
            stderr: format!("{}ERROR: Failed to parse module.\n", report.text),
            exit_code: XML_EXPORT_SPEC_PARSING_FAILURE,
        });
    }
    // SANY.frontEndSemanticAnalysis: SANY level-checks each module while there are no errors.
    let check_levels = |graph: &mut _, module, messages: &mut Vec<_>| {
        if messages
            .iter()
            .all(|message: &crate::sany::nodes::SanyMessage| message.is_warning)
        {
            check_module_levels(graph, module, &mut LevelCheck { messages });
        }
    };
    // `SimpleFilenameToStream.locate`: a module's own file, then a standard module, then a module
    // of the root module's file, as the report reads them.
    let load_source = |name: &str| {
        load_module(name)
            .or_else(|| get_standard_module(name, TlcVersion::Master).map(str::to_owned))
            .or_else(|| extract_module(source, name))
    };
    let specification = generate_sany_specification(
        source,
        &load_source,
        &GenerationOptions {
            root_file_name: Some(Rc::from(root)),
            root_file_path: Some(format!(
                "{}.tla",
                file_name.strip_suffix(".tla").unwrap_or(file_name)
            )),
            root_extendees: None,
            on_module: Some(&check_levels),
        },
    )?;
    if specification
        .messages
        .iter()
        .any(|message| !message.is_warning)
    {
        return not_yet("an error of SANY's generator that its report doesn't print");
    }
    Ok(match export_sany_xml(&specification, options)? {
        Ok(xml) => ExportOutput {
            stdout: xml,
            stderr: report.text,
            exit_code: 0,
        },
        // XMLExporter prints an exception with Java's stack traces, of each node it was exporting,
        // which aren't written.
        Err(error) if error.is_exception => {
            return not_yet("the stack traces of XMLExporter's exception");
        }
        Err(error) => ExportOutput {
            stdout: String::new(),
            stderr: format!("{}ERROR: {}\n", report.text, error.message),
            exit_code: error.exit_code,
        },
    })
}
