//! `exportXml` in `src/cli/xml-exporter.ts` after its arguments: what SANY's XMLExporter prints for
//! a spec, given the root module's text.

use crate::TlcVersion;
use crate::report::{ReportOptions, get_sany_text_of};
use crate::sany::Result;

/// XMLExporterExitCode, and the status Java exits with on an exception nothing catches.
pub const EXIT_UNCAUGHT_EXCEPTION: i32 = 1;
pub const EXIT_SPEC_PARSING_FAILURE: i32 = 2;

/// The flags of an export: -r, -u and -t (-o, which skips validating the XML against its schema,
/// changes nothing here).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ExportFlags {
    pub is_restricted: bool,
    pub is_uncommented: bool,
    pub is_terse: bool,
}

/// What XMLExporter prints and its exit status.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExportOutput {
    pub stdout: String,
    pub stderr: String,
    pub exit_code: i32,
}

/// The export of the spec whose root module `root` has the text `source`. `file_name` is the
/// argument XMLExporter was given, and `load_module` reads another module's file.
pub fn export_xml(
    root: &str,
    source: &str,
    file_name: &str,
    load_module: &dyn Fn(&str) -> Option<String>,
    flags: ExportFlags,
) -> Result<ExportOutput> {
    let report = get_sany_text_of(
        root,
        source,
        &ReportOptions {
            version: TlcVersion::Master,
            file_name: Some(file_name),
            load_module,
            describe_file: &|_, _| String::new(),
            is_xml_export: true,
        },
    )?;
    if report.is_failed {
        return Ok(ExportOutput {
            stdout: String::new(),
            stderr: format!("{}ERROR: Failed to parse module.\n", report.text),
            exit_code: EXIT_SPEC_PARSING_FAILURE,
        });
    }
    let _ = flags;
    crate::sany::not_yet("SANY's XML")
}
