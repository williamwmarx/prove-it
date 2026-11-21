//! TLC's messages, as `src/tlc/messages.ts` prints them: a message has a code from tlc2.output.EC
//! and a level from tlc2.output.MP. With -tool, TLC wraps each in markers that name both, and
//! otherwise starts it with the prefix of its level.

use std::collections::HashSet;
use std::io::{BufWriter, Write};

use crate::host::Host;
use crate::outcome::{Outcome, Reported, ReportedState, Thrown};
use crate::plain::Variable;
use crate::te_spec::{RecordedTrace, TraceSpec};
use crate::time::{format_date, format_java_date};
use crate::trace::format_variables;

pub const GENERAL: u32 = 1000;
/// `EC.SYSTEM_STACK_OVERFLOW`.
pub const SYSTEM_STACK_OVERFLOW: u32 = 1005;
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
pub const INCOMPLETE_INITIAL: u32 = 2106;
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
pub const STATE_PRINT_1: u32 = 2216;
pub const STATE_PRINT_2: u32 = 2217;
pub const STATE_PRINT_3: u32 = 2218;
pub const TEMPORAL_PROPERTY_VIOLATED: u32 = 2116;
pub const BACK_TO_STATE: u32 = 2122;
pub const COUNTER_EXAMPLE: u32 = 2264;
pub const ASSUMPTION_FALSE: u32 = 2104;
pub const NO_STATES_SATISFYING_INIT: u32 = 2118;
pub const NO_STATES_SATISFYING_INIT_AND_CONSTRAINT: u32 = 2256;
pub const POSTCONDITION_FALSE: u32 = 2404;
pub const POSTCONDITION_FAILED: u32 = 2405;
pub const POSSIBLE_UNWITNESSED: u32 = 2780;
pub const NO_SPECIFICATION_BUT_PROPERTY: u32 = 2257;
pub const NO_FAIRNESS_BUT_PROPERTY: u32 = 2259;
pub const COMPUTING_INIT_PROGRESS: u32 = 2269;
pub const SYMMETRY_SET_TOO_SMALL: u32 = 2300;
pub const CONSTANT_INVARIANT: u32 = 2149;
pub const STATE_LEVEL_PROPERTY: u32 = 2255;
pub const CONFIG_FILE_ERROR: u32 = 5001;
pub const TRACE_SPEC_WRITTEN: u32 = 2501;
pub const TRACE_SPEC_FAILED: u32 = 2502;
pub const CONFIG_ID_REQUIRES_NO_ARG: u32 = 2228;
pub const CONFIG_ID_MUST_NOT_BE_CONSTANT: u32 = 2233;
pub const CONFIG_SPECIFIED_NOT_DEFINED: u32 = 2229;

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Level {
    None = 0,
    Error = 1,
    Warning = 3,
    State = 4,
}

/// Where a check writes: what TLC prints, and Prove It's own notes, such as that a model isn't
/// native yet, which the binary writes to stdout and stderr; the host it reads from; and the
/// outcome it records as it prints, which the library reads.
pub struct Output<'o> {
    pub out: &'o mut dyn Write,
    pub err: &'o mut dyn Write,
    pub host: &'o dyn Host,
    pub outcome: Outcome,
}

/// The codes TLC prints only through `MP.printMessage`, `printState` or `printWarning`, each of
/// which -suppressMessages silences, as its every caller does at d8fb231.
const SUPPRESSIBLE_CODES: [u32; 8] = [2149, 2190, 2191, 2193, 2194, 2199, 2217, 2268];

/// The codes TLC prints only through `MP.printError`, which -suppressMessages leaves alone.
const UNSUPPRESSED_CODES: [u32; 3] = [2110, 2121, 2404];

/// SANY's `ErrorCode`s by their standard values, with whether each is an error rather than a
/// warning, as `tla2sany.semantic.ErrorCode` lists them at d8fb231, but GENERAL, which is EC's.
const SANY_CODES: [(i32, &str, bool); 65] = [
    (4003, "INTERNAL_ERROR", true),
    (4004, "SUSPECTED_UNREACHABLE_CHECK", true),
    (4005, "UNSUPPORTED_LANGUAGE_FEATURE", true),
    (4200, "SYMBOL_UNDEFINED", true),
    (4201, "SYMBOL_REDEFINED", true),
    (4202, "BUILT_IN_SYMBOL_REDEFINED", true),
    (4203, "OPERATOR_NAME_INCOMPLETE", true),
    (4204, "OPERATOR_GIVEN_INCORRECT_NUMBER_OF_ARGUMENTS", true),
    (4205, "OPERATOR_LEVEL_CONSTRAINTS_EXCEEDED", true),
    (4206, "ASSUMPTION_IS_NOT_CONSTANT", true),
    (4220, "MODULE_FILE_CANNOT_BE_FOUND", true),
    (4221, "MODULE_NAME_DIFFERENT_FROM_FILE_NAME", true),
    (4222, "MODULE_DEPENDENCIES_ARE_CIRCULAR", true),
    (4223, "MODULE_REDEFINED", true),
    (4224, "EXTENDED_MODULES_SYMBOL_UNIFICATION_CONFLICT", true),
    (4240, "INSTANCE_SUBSTITUTION_MISSING_SYMBOL", true),
    (
        4241,
        "INSTANCE_SUBSTITUTION_SYMBOL_REDEFINED_MULTIPLE_TIMES",
        true,
    ),
    (
        4242,
        "INSTANCE_SUBSTITUTION_ILLEGAL_SYMBOL_REDEFINITION",
        true,
    ),
    (
        4243,
        "INSTANCE_SUBSTITUTION_OPERATOR_CONSTANT_INCORRECT_ARITY",
        true,
    ),
    (4244, "INSTANCE_SUBSTITUTION_NON_LEIBNIZ_OPERATOR", true),
    (
        4245,
        "INSTANCE_SUBSTITUTION_LEVEL_CONSTRAINTS_EXCEEDED",
        true,
    ),
    (4246, "INSTANCE_SUBSTITUTION_LEVEL_CONSTRAINT_NOT_MET", true),
    (
        4247,
        "INSTANCE_SUBSTITUTION_COPARAMETER_LEVEL_CONSTRAINTS_EXCEEDED",
        true,
    ),
    (4260, "FUNCTION_GIVEN_INCORRECT_NUMBER_OF_ARGUMENTS", true),
    (4261, "FUNCTION_EXCEPT_AT_USED_WHERE_UNDEFINED", true),
    (4262, "RECORD_CONSTRUCTOR_FIELD_REDEFINITION", true),
    (
        4270,
        "HIGHER_ORDER_OPERATOR_REQUIRED_BUT_EXPRESSION_GIVEN",
        true,
    ),
    (
        4271,
        "HIGHER_ORDER_OPERATOR_ARGUMENT_HAS_INCORRECT_ARITY",
        true,
    ),
    (
        4272,
        "HIGHER_ORDER_OPERATOR_PARAMETER_LEVEL_CONSTRAINT_NOT_MET",
        true,
    ),
    (
        4273,
        "HIGHER_ORDER_OPERATOR_COPARAMETER_LEVEL_CONSTRAINTS_EXCEEDED",
        true,
    ),
    (4274, "LAMBDA_OPERATOR_ARGUMENT_HAS_INCORRECT_ARITY", true),
    (4275, "LAMBDA_GIVEN_WHERE_EXPRESSION_REQUIRED", true),
    (4290, "RECURSIVE_OPERATOR_PRIMES_PARAMETER", true),
    (4291, "RECURSIVE_OPERATOR_DECLARED_BUT_NOT_DEFINED", true),
    (
        4292,
        "RECURSIVE_OPERATOR_DECLARATION_DEFINITION_ARITY_MISMATCH",
        true,
    ),
    (
        4293,
        "RECURSIVE_OPERATOR_DEFINED_IN_WRONG_LET_IN_LEVEL",
        true,
    ),
    (4294, "RECURSIVE_SECTION_CONTAINS_ILLEGAL_DEFINITION", true),
    (4310, "ALWAYS_PROPERTY_SENSITIVE_TO_STUTTERING", true),
    (4311, "EVENTUALLY_PROPERTY_SENSITIVE_TO_STUTTERING", true),
    (
        4312,
        "BINARY_TEMPORAL_OPERATOR_WITH_ACTION_LEVEL_PARAMETER",
        true,
    ),
    (
        4313,
        "LOGICAL_OPERATOR_WITH_MIXED_ACTION_TEMPORAL_PARAMETERS",
        true,
    ),
    (
        4314,
        "QUANTIFIED_TEMPORAL_FORMULA_WITH_ACTION_LEVEL_BOUND",
        true,
    ),
    (4315, "QUANTIFICATION_WITH_TEMPORAL_LEVEL_BOUND", true),
    (4330, "LABEL_PARAMETER_REPETITION", true),
    (4331, "LABEL_PARAMETER_MISSING", true),
    (4332, "LABEL_PARAMETER_UNNECESSARY", true),
    (4333, "LABEL_NOT_IN_DEFINITION_OR_PROOF_STEP", true),
    (
        4334,
        "LABEL_NOT_ALLOWED_IN_NESTED_ASSUME_PROVE_WITH_NEW",
        true,
    ),
    (4335, "LABEL_NOT_ALLOWED_IN_FUNCTION_EXCEPT", true),
    (4336, "LABEL_REDEFINITION", true),
    (4337, "LABEL_GIVEN_INCORRECT_NUMBER_OF_ARGUMENTS", true),
    (
        4350,
        "PROOF_STEP_WITH_IMPLICIT_LEVEL_CANNOT_HAVE_NAME",
        true,
    ),
    (4351, "PROOF_STEP_NON_EXPRESSION_USED_AS_EXPRESSION", true),
    (
        4352,
        "TEMPORAL_PROOF_GOAL_WITH_NON_CONSTANT_TAKE_WITNESS_HAVE",
        true,
    ),
    (4353, "TEMPORAL_PROOF_GOAL_WITH_NON_CONSTANT_CASE", true),
    (
        4354,
        "QUANTIFIED_TEMPORAL_PICK_FORMULA_WITH_NON_CONSTANT_BOUND",
        true,
    ),
    (4355, "ASSUME_PROVE_USED_WHERE_EXPRESSION_REQUIRED", true),
    (
        4356,
        "ASSUME_PROVE_NEW_CONSTANT_HAS_TEMPORAL_LEVEL_BOUND",
        true,
    ),
    (4357, "USE_OR_HIDE_FACT_NOT_VALID", true),
    (4800, "EXTENDED_MODULES_SYMBOL_UNIFICATION_AMBIGUITY", false),
    (
        4801,
        "INSTANCED_MODULES_SYMBOL_UNIFICATION_AMBIGUITY",
        false,
    ),
    (4802, "RECORD_CONSTRUCTOR_FIELD_NAME_CLASH", false),
    (
        4803,
        "PLUSCAL_ALGORITHM_AND_TRANSLATION_CHANGED_SINCE_LAST_TRANSLATION",
        false,
    ),
    (
        4804,
        "PLUSCAL_ALGORITHM_CHANGED_SINCE_LAST_TRANSLATION",
        false,
    ),
    (
        4805,
        "PLUSCAL_TRANSLATION_CHANGED_SINCE_LAST_TRANSLATION",
        false,
    ),
];

/// SANY's `ErrorCode` of a standard value, its name and whether it is an error.
pub fn get_sany_code(code: i32) -> Option<(&'static str, bool)> {
    SANY_CODES
        .iter()
        .find(|(value, _, _)| *value == code)
        .map(|&(_, name, is_error)| (name, is_error))
}

/// Whether the binary follows -suppressMessages and -messagesAsErrors of the code.
pub fn is_controlled_code(code: i32) -> bool {
    u32::try_from(code)
        .is_ok_and(|code| SUPPRESSIBLE_CODES.contains(&code) || UNSUPPRESSED_CODES.contains(&code))
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
    /// The trace exploration spec TLC writes after an error trace, where it writes one.
    pub trace_spec: Option<TraceSpec>,
    pub recorded_trace: RecordedTrace,
    /// Why the run declines, where it can't write the spec TLC writes.
    pub trace_spec_decline: Option<String>,
    /// The directory `-teSpecOutDir` names for the trace exploration spec, where nothing is
    /// there before the search, which TLC makes as it writes the spec (`File.mkdirs`).
    pub absent_trace_spec_directory: Option<String>,
    /// TLC's coverage report of the run, which comes before the statistics.
    pub coverage: Option<Vec<tla_trace::CoverageMessage>>,
    pub outcome: &'o mut Outcome,
    /// The codes of -suppressMessages, whose messages TLC records but doesn't print.
    pub suppressed: Vec<u32>,
    /// The codes of -messagesAsErrors, whose warnings TLC fails with.
    pub as_errors: Vec<u32>,
    /// The paths TLC makes before it evaluates anything (its metadir and its dumps), which a
    /// replay that reads the file system doesn't see. `None` where the check doesn't know them.
    pub made_paths: Option<Vec<std::path::PathBuf>>,
    /// Whether -difftrace asks TLC to print only what changed in a trace's state
    /// (`TLCGlobals.printDiffsOnly`).
    pub is_diff_trace: bool,
    /// `LoweredModel::alias_decline`: why a run that evaluates the ALIAS declines.
    pub alias_decline: Option<String>,
    /// The file of -userFile, where Print and PrintT write in place of the console
    /// (`tlc2.module.TLC.OUTPUT`).
    pub user_file: Option<std::path::PathBuf>,
    /// The trace's file of the trace exploration spec, where the directory -teSpecOutDir names
    /// isn't there as the check starts: `_TLCTrace`'s postcondition fails to write it, which only
    /// the report of a safety violation's trace follows, and takes it.
    pub unplaced_trace_file: Option<String>,
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
            trace_spec: None,
            recorded_trace: RecordedTrace::default(),
            trace_spec_decline: None,
            absent_trace_spec_directory: None,
            coverage: None,
            outcome: &mut output.outcome,
            suppressed: Vec::new(),
            as_errors: Vec::new(),
            made_paths: None,
            is_diff_trace: false,
            alias_decline: None,
            user_file: None,
            unplaced_trace_file: None,
        }
    }

    /// The message TLC reports a violation or an error with, which the outcome records with the
    /// states printed after it.
    pub fn report(&mut self, code: u32, headline: &str) {
        self.print(code, Level::Error, headline);
        self.record(Reported {
            code,
            headline: headline.to_string(),
            states: Vec::new(),
            loop_start: None,
        });
    }

    /// Keeps a violation or an error in the outcome, where its caller reads it (`Host::is_plain`).
    pub fn record(&mut self, reported: Reported) {
        if self.host.is_plain() {
            self.outcome.violations.push(reported);
        }
    }

    /// Keeps the error the library throws where TLC stops before it searches, where its caller reads
    /// it (`Host::is_plain`).
    pub fn set_thrown(&mut self, thrown: Option<Thrown>) {
        if self.host.is_plain() {
            if self.outcome.status.is_none() && matches!(thrown, Some(Thrown::NotNative(_))) {
                crate::transaction::mark_thrown();
            }
            self.outcome.thrown = thrown;
        }
    }

    /// A state of the behavior TLC reports, at its position from 1.
    pub fn state(&mut self, position: usize, label: &str, variables: Vec<Variable>) {
        self.print(
            STATE_PRINT_2,
            Level::State,
            &format!("{position}: <{label}>\n{}", format_variables(&variables)),
        );
        if let Some(reported) = self.outcome.violations.last_mut() {
            reported.states.push(ReportedState {
                label: label.to_string(),
                variables,
            });
        }
    }

    /// A state of a trace as -difftrace prints it: `text` holds only the variables that changed
    /// (`TLCStateMut.toString(TLCState)`), while the outcome records every variable.
    pub fn state_text(
        &mut self,
        position: usize,
        label: &str,
        text: &str,
        variables: Vec<Variable>,
    ) {
        self.print(
            STATE_PRINT_2,
            Level::State,
            &format!("{position}: <{label}>\n{text}"),
        );
        if let Some(reported) = self.outcome.violations.last_mut() {
            reported.states.push(ReportedState {
                label: label.to_string(),
                variables,
            });
        }
    }

    /// A line the spec printed, as TLC searched or as it printed a trace and checked the
    /// postconditions on it, which the outcome records where its caller reads it.
    pub fn printed(&mut self, text: &str) {
        self.user_print(text);
        if self.host.is_plain() {
            self.outcome.prints.push(text.to_string());
        }
    }

    pub(crate) fn replayed(
        &mut self,
        ir: &tla_ir::Ir,
        output: &crate::trace::PrintedOutput,
    ) -> Result<(), &'static str> {
        match output {
            tla_trace::OutputEvent::Print(text) => self.printed(text),
            tla_trace::OutputEvent::Warning(warning) => self.runtime_warning(ir, warning)?,
        }
        Ok(())
    }

    pub(crate) fn runtime_warning(
        &mut self,
        ir: &tla_ir::Ir,
        warning: &tla_ir::RuntimeWarning,
    ) -> Result<(), &'static str> {
        let mut node = match warning {
            tla_ir::RuntimeWarning::Except { node }
            | tla_ir::RuntimeWarning::Unchanged { node, .. } => *node,
        };
        while let Some(tla_ir::Node {
            kind: tla_ir::NodeKind::Reference(target),
            ..
        }) = ir.nodes.arena.get(node as usize)
        {
            node = *target;
        }
        let range = ir
            .nodes
            .arena
            .get(node as usize)
            .and_then(|node| node.range)
            .ok_or("a runtime warning without a source range")?;
        let module = ir
            .texts
            .get(range.module as usize)
            .ok_or("a runtime warning without a source module")?;
        let location = format!(
            "line {}, col {} to line {}, col {} of module {}",
            range.start_line, range.start_column, range.end_line, range.end_column, module
        );
        let (code, text) = match warning {
            tla_ir::RuntimeWarning::Except { .. } => (
                2144,
                format!(
                    "The EXCEPT was applied to non-existing fields of the value at\n{}",
                    location
                ),
            ),
            tla_ir::RuntimeWarning::Unchanged { variable, .. } => {
                let variable = ir
                    .variables
                    .get(*variable as usize)
                    .and_then(|name| ir.texts.get(*name as usize))
                    .ok_or("a runtime warning without a variable")?;
                (
                    2143,
                    format!(
                        "The variable {} was changed while it is specified as UNCHANGED at\n{}",
                        variable, location
                    ),
                )
            }
        };
        self.print(code, Level::Warning, &text);
        Ok(())
    }

    /// The date and time now, as TLC prints them.
    pub fn date(&self) -> String {
        format_date(self.host.now(), self.host.zone())
    }

    /// The date and time now as `java.util.Date.toString` writes it, where the binary knows the
    /// zone's name Java gives it: UTC's.
    pub fn java_date(&self) -> Option<String> {
        let is_named_utc = self
            .host
            .get_variable("TZ")
            .is_none_or(|name| matches!(name.trim_start_matches(':'), "UTC" | "Etc/UTC"));
        (is_named_utc && self.host.zone().is_utc()).then(|| format_java_date(self.host.now()))
    }

    pub fn print(&mut self, code: u32, level: Level, text: &str) {
        let is_warning = level == Level::Warning;
        // `MP.printWarning` fails with a code of -messagesAsErrors before it consults -nowarning.
        if is_warning && self.as_errors.contains(&code) {
            self.decline("a warning -messagesAsErrors makes an error");
            return;
        }
        if is_warning && !self.is_warning_enabled {
            return;
        }
        let is_suppressed = self.suppressed.contains(&code);
        if is_suppressed
            && !(SUPPRESSIBLE_CODES.contains(&code) && level != Level::Error
                || UNSUPPRESSED_CODES.contains(&code) && level == Level::Error)
        {
            self.decline("a message -suppressMessages names, printed as TLC may not silence");
            return;
        }
        // TLC's recorder takes the states of a behavior (TLC_STATE_PRINT2 and 3, and a lasso's
        // step back), not the error state the simulator prints alone (TLC_STATE_PRINT1).
        if level == Level::State && code != STATE_PRINT_1 {
            self.recorded_trace.note_printed();
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
        if self.host.is_plain() {
            self.outcome.messages.push(crate::outcome::Message {
                code,
                level: level as u8,
                text: text.to_string(),
                prints_before: self.outcome.prints.len(),
                counts: None,
            });
        }
        if is_suppressed && level != Level::Error {
            return;
        }
        self.line(&message);
    }

    /// Declines the run once it ends, whatever it printed.
    fn decline(&mut self, reason: &str) {
        self.trace_spec_decline
            .get_or_insert_with(|| reason.to_owned());
    }

    /// Notes the search's counts with the message just printed, for the library's events.
    pub fn count_message(&mut self, counts: crate::outcome::Counts) {
        if let Some(message) = self.outcome.messages.last_mut() {
            message.counts = Some(counts);
        }
    }

    /// A line outside any message, such as what the front end printed.
    pub fn line(&mut self, text: &str) {
        let _ = writeln!(self.out, "{text}");
    }

    /// What Print or PrintT prints: a line on the console, or, with -userFile, a line TLC
    /// writes to that file (`OUTPUT.write`), which it flushes as it ends.
    pub fn user_print(&mut self, text: &str) {
        match &self.user_file {
            Some(path) => {
                self.host
                    .write_file(path, format!("{text}\n").as_bytes(), true);
            }
            None => self.line(text),
        }
    }

    pub fn raw(&mut self, bytes: &[u8]) {
        let _ = self.out.write_all(bytes);
    }

    pub fn flush(&mut self) {
        let _ = self.out.flush();
        let _ = self.err.flush();
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
