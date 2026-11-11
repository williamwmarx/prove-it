//! `-dumpTrace tlc <file>` and `-dumpTrace json <file>`: TLC adds a postcondition of its trace
//! modules for each (`_TLCTrace!_TLCTrace`, `_JsonTrace!_JsonTrace`), which writes a violation's
//! counterexample to the file and prints `CounterExample written: <file>`, and nothing where the
//! search found none (`CounterExample.state = {}`).

use std::path::Path;

use tla_front::config::ModelConfig;
use tla_front::model::TRACE_MODULE;
use tla_ir::Ir;
use tla_trace::{CounterExample, Rebuilder, Unsupported};

use crate::args::{DUMP_TRACE, Parsed};
use crate::host::Host;

const JSON_MODULE: &str = "_JsonTrace";

/// Why the binary declines the trace's file the trace exploration spec's postcondition writes.
pub const TRACE_FILE_DECLINE: &str =
    "the trace file of the trace exploration spec, which TLC compresses with Java's Deflater";

/// The command line's -dumpTrace options and what they need of the configuration.
pub struct TraceDumps {
    /// Each option in the order given: whether it writes JSON, and its file.
    dumps: Vec<(bool, String)>,
    /// The configuration's model values in the order TLC makes them, whose positions a `tlc`
    /// dump writes.
    model_values: Vec<String>,
    /// Whether TLC records the trace for its trace exploration spec, whose postcondition writes
    /// its `.bin` with `_TLCTrace` after the command line's.
    is_trace_recorded: bool,
    /// That `.bin`, where the binary knows where TLC writes it.
    trace_file: Option<String>,
}

/// A file a dump writes, and what TLC prints as it writes it.
pub struct DumpedFile {
    pub path: String,
    pub bytes: Vec<u8>,
    /// Whether its postcondition prints that it wrote it, as the trace exploration spec's doesn't.
    pub is_printed: bool,
}

impl DumpedFile {
    /// `PrintT("CounterExample written: " \o file)`, which `TraceDumps::dump` keeps to files
    /// whose names print as they are.
    pub fn get_line(&self) -> String {
        format!("\"CounterExample written: {}\"", self.path)
    }
}

impl TraceDumps {
    pub fn new(
        args: &Parsed,
        config: &ModelConfig,
        is_trace_recorded: bool,
        trace_file: Option<String>,
    ) -> TraceDumps {
        TraceDumps {
            dumps: args
                .options
                .iter()
                .filter(|option| option.0 == DUMP_TRACE)
                .map(|option| (option.1[0] == "json", option.1[1].clone()))
                .collect(),
            model_values: config
                .get_model_values()
                .into_iter()
                .map(str::to_owned)
                .collect(),
            is_trace_recorded,
            trace_file: trace_file.filter(|_| is_trace_recorded),
        }
    }

    /// Leaves out the trace exploration spec's file, for a model whose spec the front end didn't
    /// read, such as an IR a test names, which the binary checks as TLC checks without the spec.
    pub fn leave_out_trace_file(&mut self) {
        self.is_trace_recorded = false;
        self.trace_file = None;
    }

    /// Whether the command line asks for a dump, as the trace exploration spec's postcondition
    /// doesn't.
    pub fn has_command_line_dumps(&self) -> bool {
        !self.dumps.is_empty()
    }

    /// Whether the trace exploration spec's postcondition writes the trace's file.
    pub fn is_trace_recorded(&self) -> bool {
        self.is_trace_recorded
    }

    pub fn is_empty(&self) -> bool {
        self.dumps.is_empty() && !self.is_trace_recorded
    }

    /// The modules TLC adds to the root module's EXTENDS for the postconditions, in the order it
    /// adds them: the command line's, then the trace exploration spec's.
    pub fn get_root_extendees(&self) -> Vec<&'static str> {
        self.dumps
            .iter()
            .map(|dump| if dump.0 { JSON_MODULE } else { TRACE_MODULE })
            .chain(self.is_trace_recorded.then_some(TRACE_MODULE))
            .collect()
    }

    /// The files the postconditions write of the counterexample, in their order. Each module's
    /// constant names its file, which TLC gives each postcondition of the module in turn
    /// (`processConstantsForModule`), so each writes the file of the last.
    pub fn dump(
        &self,
        ir: &Ir,
        rebuilder: &mut Rebuilder<'_>,
        counter_example: &CounterExample<'_>,
    ) -> Result<Vec<DumpedFile>, Unsupported> {
        if self.is_empty() {
            return Ok(Vec::new());
        }
        if self.is_trace_recorded {
            return Err(Unsupported(TRACE_FILE_DECLINE.into()));
        }
        // TLC finds the trace again for the postconditions, which a random draw may not find, and
        // then writes nothing.
        if ir.builtins.iter().any(|builtin| {
            matches!(
                &*ir.texts[builtin.name as usize],
                "RandomElement" | "RandomSubset"
            )
        }) {
            return Err(Unsupported(
                "-dumpTrace of a trace TLC may not find again for a random draw".into(),
            ));
        }
        let dumped = rebuilder.dump_trace(counter_example)?;
        let model_values: Vec<&str> = self.model_values.iter().map(String::as_str).collect();
        let mut files = Vec::new();
        // The trace exploration spec's postcondition writes `_TLCTrace`'s file after the command
        // line's.
        let dumps = self
            .dumps
            .iter()
            .map(|(is_json, path)| (*is_json, path.clone(), true))
            .chain(
                self.trace_file
                    .iter()
                    .map(|path| (false, path.clone(), false)),
            )
            .collect::<Vec<_>>();
        for (is_json, _, is_printed) in &dumps {
            let path = dumps
                .iter()
                .rev()
                .find(|dump| dump.0 == *is_json)
                .map_or_else(String::new, |dump| dump.1.clone());
            // TLC prints a name with quotes, escapes or other characters as its strings print them.
            if path.is_empty()
                || !path
                    .chars()
                    .all(|character| character.is_ascii_graphic() || character == ' ')
                || path.contains(['"', '\\'])
            {
                return Err(Unsupported(format!("-dumpTrace into the file {path:?}")));
            }
            let bytes = if *is_json {
                dumped.to_json()?.into_bytes()
            } else {
                dumped.to_tlc(&model_values)?
            };
            files.push(DumpedFile {
                path,
                bytes,
                is_printed: *is_printed,
            });
        }
        Ok(files)
    }
}

/// Whether the host can write each file: TLC writes a JSON dump into the directories it makes
/// and a `tlc` one into the directory that holds it, and fails where it can't.
pub fn is_writable(host: &dyn Host, files: &[DumpedFile]) -> bool {
    files.iter().all(|file| {
        Path::new(&file.path)
            .parent()
            .is_none_or(|parent| parent.as_os_str().is_empty() || host.is_file(parent))
    })
}

/// Writes the files in their order, as the postconditions do, or says it couldn't.
pub fn write(host: &dyn Host, files: &[DumpedFile]) -> bool {
    files
        .iter()
        .all(|file| host.write_file(Path::new(&file.path), &file.bytes, false))
}
