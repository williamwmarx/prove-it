//! TLC's messages, as `src/tlc/messages.ts` prints them: a message has a code from tlc2.output.EC
//! and a level from tlc2.output.MP. With -tool, TLC wraps each in markers that name both, and
//! otherwise starts it with the prefix of its level.

use std::collections::HashSet;
use std::io::{BufWriter, Write};

use crate::host::Host;
use crate::time::format_date;

pub const GENERAL: u32 = 1000;
pub const COMMAND_LINE_ERROR: u32 = 1102;
pub const STARTING: u32 = 2185;
pub const FINISHED: u32 = 2186;
pub const SANY_FINISHED: u32 = 2219;
pub const STARTING_SANY: u32 = 2220;
pub const PARSING_FAILED: u32 = 3002;
pub const PARSING_FAILED_EXCEPTION: u32 = 2171;
pub const MODEL_CHECKING: u32 = 2187;
pub const COMPUTING_INIT: u32 = 2189;
pub const INVARIANT_VIOLATED_INITIAL: u32 = 2107;
pub const PROPERTY_VIOLATED_INITIAL: u32 = 2108;
pub const INVARIANT_VIOLATED_BEHAVIOR: u32 = 2110;
pub const ACTION_PROPERTY_VIOLATED_BEHAVIOR: u32 = 2112;
pub const DEADLOCK_REACHED: u32 = 2114;
pub const NO_NEXT_ACTION: u32 = 2115;
pub const BEHAVIOR_UP_TO_THIS_POINT: u32 = 2121;
pub const NESTED_EXPRESSION: u32 = 2103;
pub const INCOMPLETE_SUCCESSOR: u32 = 2109;
pub const FINGERPRINT_FAILED: u32 = 2147;
pub const INIT_GENERATED_1: u32 = 2190;
pub const INIT_GENERATED_2: u32 = 2191;
pub const CHECKING_TEMPORAL: u32 = 2192;
pub const SUCCESS: u32 = 2193;
pub const SEARCH_DEPTH: u32 = 2194;
pub const STATS: u32 = 2199;
pub const PROGRESS: u32 = 2200;
pub const VERSION: u32 = 2262;
pub const CHECKING_TEMPORAL_END: u32 = 2267;
pub const STATE_GRAPH_OUTDEGREE: u32 = 2268;
pub const STATE_PRINT_2: u32 = 2217;
pub const STATE_PRINT_3: u32 = 2218;
pub const TEMPORAL_PROPERTY_VIOLATED: u32 = 2116;
pub const BACK_TO_STATE: u32 = 2122;
pub const COUNTER_EXAMPLE: u32 = 2264;
pub const ASSUMPTION_FALSE: u32 = 2104;
pub const POSTCONDITION_FALSE: u32 = 2404;
pub const POSTCONDITION_FAILED: u32 = 2405;
pub const NO_SPECIFICATION_BUT_PROPERTY: u32 = 2257;
pub const NO_FAIRNESS_BUT_PROPERTY: u32 = 2259;
pub const COMPUTING_INIT_PROGRESS: u32 = 2269;
pub const SYMMETRY_SET_TOO_SMALL: u32 = 2300;
pub const CONSTANT_INVARIANT: u32 = 2149;
pub const STATE_LEVEL_PROPERTY: u32 = 2255;
pub const CONFIG_FILE_ERROR: u32 = 5001;

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Level {
    None = 0,
    Error = 1,
    Warning = 3,
    State = 4,
}

/// Where a check writes: what TLC prints, and Prove It's own notes, such as that a model isn't
/// native yet, which the binary writes to stdout and stderr; and the host it reads from.
pub struct Output<'o> {
    pub out: &'o mut dyn Write,
    pub err: &'o mut dyn Write,
    pub host: &'o dyn Host,
}

/// Writes TLC's messages. MP.printWarning prints a warning once, which -nowarning drops, and
/// without -tool, TLC follows the first warning with how to drop them.
pub struct Printer<'o> {
    pub is_tool: bool,
    is_warning_enabled: bool,
    warnings: HashSet<String>,
    out: BufWriter<&'o mut dyn Write>,
    err: &'o mut dyn Write,
    pub host: &'o dyn Host,
    /// Whether the run records the trace TLC writes beside the spec for its trace exploration
    /// spec: TLC's default, where tla-front read the spec.
    pub is_trace_recorded: bool,
}

impl<'o> Printer<'o> {
    pub fn new(is_tool: bool, is_warning_enabled: bool, output: &'o mut Output<'_>) -> Self {
        Self {
            is_tool,
            is_warning_enabled,
            warnings: HashSet::new(),
            out: BufWriter::new(&mut *output.out),
            err: &mut *output.err,
            host: output.host,
            is_trace_recorded: false,
        }
    }

    /// The date and time now, as TLC prints them.
    pub fn date(&self) -> String {
        format_date(self.host.now(), self.host.zone())
    }

    pub fn print(&mut self, code: u32, level: Level, text: &str) {
        let is_warning = level == Level::Warning;
        if is_warning && !self.is_warning_enabled {
            return;
        }
        let message = if self.is_tool {
            format!(
                "@!@!@STARTMSG {code}:{} @!@!@\n{text}\n@!@!@ENDMSG {code} @!@!@",
                level as u8
            )
        } else {
            let prefix = match level {
                Level::None => "",
                Level::Error => "Error: ",
                Level::Warning => "Warning: ",
                Level::State => "State ",
            };
            let hint = if is_warning && self.warnings.is_empty() {
                "\n(Use the -nowarning option to disable this warning.)"
            } else {
                ""
            };
            format!("{prefix}{text}{hint}")
        };
        if is_warning && !self.warnings.insert(message.clone()) {
            return;
        }
        self.line(&message);
    }

    /// A line outside any message, such as what the front end printed.
    pub fn line(&mut self, text: &str) {
        let _ = writeln!(self.out, "{text}");
    }

    pub fn raw(&mut self, bytes: &[u8]) {
        let _ = self.out.write_all(bytes);
    }

    pub fn flush(&mut self) {
        let _ = self.out.flush();
    }

    /// A note of Prove It's own, after what TLC printed so far.
    pub fn note(&mut self, text: &str) {
        self.flush();
        let _ = writeln!(self.err, "{text}");
    }
}

impl Drop for Printer<'_> {
    fn drop(&mut self) {
        self.flush();
    }
}
