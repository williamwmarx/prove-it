//! The trace exploration spec TLC writes after an error trace in its default mode
//! (`TraceExplorationSpec.writeSpecTEStreams`, `SpecTraceExpressionWriter`): one file that holds
//! the spec, the modules it instances, and its configuration, beside the checked spec.

use std::path::Path;
use std::time::{SystemTime, UNIX_EPOCH};

use tla_front::config::ModelConfig;
use tla_values::fingerprint::{MODEL_VALUE, Polynomial};

use crate::messages::{self as code, Level, Printer};

const INDENT: &str = "    ";
const SEPARATOR: &str = "----";
const CLOSING_TAG_WIDTH: usize = 77;

/// Where TLC writes the trace exploration files of the spec at `main_file`, the path it was given
/// without `.tla`, for a run that started at `started`: the directory as `Path.getParent` names it,
/// the spec's module, and `<Spec>_TTrace_<epoch>`, the name of the files without their extension.
pub fn get_files_place(main_file: &str, started: SystemTime) -> (String, &str, String) {
    let (directory, module) = match main_file.rsplit_once('/') {
        Some(("", module)) => ("/".to_string(), module),
        Some((directory, module)) => (directory.to_string(), module),
        None => (".".to_string(), main_file),
    };
    let epoch = started
        .duration_since(UNIX_EPOCH)
        .map_or(0, |duration| duration.as_secs());
    (directory, module, format!("{module}_TTrace_{epoch}"))
}

/// What TLC knows of the run as it writes the spec, but the trace.
pub struct TraceSpec {
    /// The checked spec's module.
    pub module: String,
    /// `<Spec>_TTrace_<epoch>`, the spec's module and the stem of its files.
    pub name: String,
    /// The directory TLC writes the files in, as `Path.resolve` prints it.
    pub directory: String,
    /// The variables in TLC's order of their declarations.
    pub variables: Vec<String>,
    /// The configuration's CONSTANT entries, split as `getConstantsAsList` splits them.
    pub constants: Vec<Vec<String>>,
    /// The model values in the order TLC made them (`ModelValue.mvs`).
    pub model_values: Vec<ModelValueName>,
    /// Why the binary can't write the spec TLC writes, where it can't.
    pub unsupported: Option<String>,
}

pub struct ModelValueName {
    pub name: String,
    /// `Value.hashCode`: of its fingerprint from the run's polynomial, the high word xor the low.
    pub hash: i32,
    /// Whether the spec defines or declares its name, which `Defns` holds.
    pub is_defined: bool,
}

impl TraceSpec {
    /// The spec TLC writes for the spec at `main_file`, the path TLC was given without `.tla`, of
    /// a run that started at `started`.
    pub fn new(
        main_file: &str,
        started: SystemTime,
        ir: &tla_ir::Ir,
        config: &ModelConfig,
        defined_names: &[String],
        fingerprint_index: usize,
    ) -> TraceSpec {
        let (directory, module, name) = get_files_place(main_file, started);
        let texts = &ir.texts[..ir.ranked_count as usize];
        let polynomial = Polynomial::get(fingerprint_index);
        let mut unsupported = None;
        let model_values = config
            .get_model_values()
            .into_iter()
            .map(|name| {
                // `Value.hashCode` fingerprints a model value by its name's intern token, one
                // more than its rank in TLC's order of strings.
                let token = texts.iter().position(|text| &**text == name);
                if token.is_none() {
                    unsupported = Some("a model value TLC's order of strings doesn't rank".into());
                }
                let fingerprint = polynomial.extend_int(
                    polynomial.extend_byte(polynomial.value(), MODEL_VALUE),
                    token.map_or(0, |rank| rank as i32 + 1),
                );
                ModelValueName {
                    name: name.to_string(),
                    hash: ((fingerprint >> 32) as i32) ^ (fingerprint as i32),
                    is_defined: defined_names.iter().any(|defined| defined == name),
                }
            })
            .collect();
        if ir
            .builtins
            .iter()
            .any(|builtin| &*ir.texts[builtin.name as usize] == "TLCModelValue")
        {
            unsupported = Some("model values the spec makes with TLCModelValue".into());
        }
        if main_file.contains("//") || main_file.ends_with('/') || module.contains('.') {
            unsupported = Some("a trace exploration spec beside a spec of that path".into());
        }
        TraceSpec {
            name,
            module: module.to_string(),
            directory,
            variables: ir
                .tlc_order
                .iter()
                .map(|&position| ir.texts[ir.variables[position as usize] as usize].to_string())
                .collect(),
            constants: config
                .raw_constants
                .iter()
                .map(|entry| java_split(entry.trim(), " = "))
                .collect(),
            model_values,
            unsupported,
        }
    }

    /// The path of the spec's file with the extension, as TLC prints it.
    pub fn get_path(&self, extension: &str) -> String {
        format!("{}/{}{extension}", self.directory, self.name)
    }
}

#[derive(Clone, Copy, PartialEq)]
enum Mark {
    State,
    Stuttering,
    BackToState,
}

#[derive(Clone)]
struct RecordedState {
    number: usize,
    /// Each variable's `Value.toString`, in TLC's order of the variables; `None` for one the step
    /// left undefined.
    values: Vec<Option<String>>,
    mark: Mark,
}

/// The error trace TLC's `ErrorTraceMessagePrinterRecorder` records from the states it prints.
#[derive(Default)]
pub struct RecordedTrace {
    states: Vec<RecordedState>,
    is_finished: bool,
    /// The states the printer printed as a trace's and those recorded, which differ where a trace
    /// was printed that the binary doesn't record.
    printed: usize,
    recorded: usize,
}

impl RecordedTrace {
    pub fn note_printed(&mut self) {
        self.printed += 1;
    }

    /// A state of the trace (`TLC_STATE_PRINT2`).
    pub fn record_state(&mut self, number: usize, values: Vec<Option<String>>) {
        self.recorded += 1;
        if !self.is_finished {
            self.states.push(RecordedState {
                number,
                values,
                mark: Mark::State,
            });
        }
    }

    /// The trace ends in stuttering (`TLC_STATE_PRINT3`).
    pub fn record_stuttering(&mut self) {
        self.recorded += 1;
        if !self.is_finished {
            self.is_finished = true;
            if let Some(last) = self.states.last() {
                let stuttering = RecordedState {
                    mark: Mark::Stuttering,
                    ..last.clone()
                };
                self.states.push(stuttering);
            }
        }
    }

    /// The trace's lasso goes back to the state of the number (`TLC_BACK_TO_STATE`), which the
    /// printer prints as a state's message with -tool only.
    pub fn record_back_to_state(&mut self, number: usize, is_printed_as_state: bool) {
        if is_printed_as_state {
            self.recorded += 1;
        }
        if !self.is_finished {
            self.is_finished = true;
            if let Some(state) = number
                .checked_sub(1)
                .and_then(|index| self.states.get(index))
            {
                let back = RecordedState {
                    mark: Mark::BackToState,
                    ..state.clone()
                };
                self.states.push(back);
            }
        }
    }
}

/// After `Finished in`: the spec TLC writes for a trace of two states or more, and the line that
/// says where. Where the binary can't write what TLC writes, the run declines.
pub fn write_after_finish(printer: &mut Printer) {
    let Some(spec) = printer.trace_spec.take() else {
        return;
    };
    let trace = std::mem::take(&mut printer.recorded_trace);
    if trace.printed != trace.recorded {
        printer.trace_spec_decline =
            Some("an error trace the trace exploration spec doesn't record".into());
        return;
    }
    if trace.states.len() <= 1 {
        return;
    }
    if let Some(reason) = &spec.unsupported {
        printer.trace_spec_decline = Some(reason.clone());
        return;
    }
    let Some(date) = printer.java_date() else {
        printer.trace_spec_decline =
            Some("the date of the trace exploration spec outside UTC".into());
        return;
    };
    let text = match get_text(&spec, &trace.states, &date) {
        Ok(text) => text,
        Err(reason) => {
            printer.trace_spec_decline = Some(reason);
            return;
        }
    };
    let path = spec.get_path(".tla");
    if !printer
        .host
        .write_file(Path::new(&path), text.as_bytes(), false)
    {
        printer.trace_spec_decline = Some("a trace exploration spec it can't write".into());
        return;
    }
    printer.print(
        code::TRACE_SPEC_WRITTEN,
        Level::None,
        &format!("Trace exploration spec path: {path}"),
    );
}

/// Java's `String.hashCode`.
pub fn java_string_hash(text: &str) -> i32 {
    text.encode_utf16().fold(0i32, |hash, unit| {
        hash.wrapping_mul(31).wrapping_add(i32::from(unit))
    })
}

/// The order a `java.util.HashSet` or `HashMap` made with the default capacity iterates its keys
/// in, inserted in the order given: by bucket of the spread hash in the final table, then in the
/// order inserted. `None` where a bucket grows long enough for Java to make a tree of it.
pub fn java_hash_order<T>(keys: Vec<(i32, T)>) -> Option<Vec<T>> {
    let mut capacity = 16usize;
    while keys.len() > capacity * 3 / 4 {
        capacity *= 2;
    }
    let mut buckets: Vec<Vec<T>> = (0..capacity).map(|_| Vec::new()).collect();
    for (hash, key) in keys {
        let spread = (hash as u32) ^ ((hash as u32) >> 16);
        buckets[spread as usize & (capacity - 1)].push(key);
    }
    if buckets.iter().any(|bucket| bucket.len() >= 8) {
        return None;
    }
    Some(buckets.into_iter().flatten().collect())
}

// A set of module names, as the Java code builds it, in its iteration order.
fn module_set(names: &[&str]) -> Vec<String> {
    let mut unique: Vec<&str> = Vec::new();
    for name in names {
        if !unique.contains(name) {
            unique.push(name);
        }
    }
    java_hash_order(
        unique
            .into_iter()
            .map(|name| (java_string_hash(name), name.to_string()))
            .collect(),
    )
    .unwrap_or_default()
}

// `StringHelper.copyString("=", 77)` and a newline.
fn closing_tag() -> String {
    format!("{}\n", "=".repeat(CLOSING_TAG_WIDTH))
}

// `SpecWriterUtilities.getExtendingModuleContent`.
fn primer(module: &str, extended: &[String]) -> String {
    let mut text = format!("{SEPARATOR} MODULE {module} {SEPARATOR}\n");
    if !extended.is_empty() {
        text.push_str(&format!("EXTENDS {}\n\n", extended.join(", ")));
    }
    text
}

// Java's `String.split` on a literal: the pieces, without the empty ones that end it.
fn java_split(text: &str, separator: &str) -> Vec<String> {
    let mut pieces: Vec<String> = text.split(separator).map(str::to_string).collect();
    while pieces.len() > 1 && pieces.last().is_some_and(String::is_empty) {
        pieces.pop();
    }
    pieces
}

// Java's `split` on a newline: the pieces, without the empty ones that end it.
fn java_lines(text: &str) -> Vec<&str> {
    let mut lines: Vec<&str> = text.split('\n').collect();
    while lines.len() > 1 && lines.last() == Some(&"") {
        lines.pop();
    }
    if lines == [""] && !text.is_empty() {
        lines.clear();
    }
    lines
}

// `SpecTraceExpressionWriter.indentString`.
fn indent(text: &str, times: usize) -> String {
    let indentation = INDENT.repeat(times);
    format!(
        "{indentation}{}",
        java_lines(text).join(&format!("\n{indentation}"))
    )
}

// The variables of a state with their values, in the order of TLC's HashMap of them.
fn hashed_variables<'s>(
    spec: &'s TraceSpec,
    state: &'s RecordedState,
) -> Result<Vec<(&'s str, &'s str)>, String> {
    java_hash_order(
        spec.variables
            .iter()
            .zip(&state.values)
            .map(|(name, value)| {
                (
                    java_string_hash(name),
                    (name.as_str(), value.as_deref().unwrap_or("")),
                )
            })
            .collect(),
    )
    .ok_or_else(|| "the order of many variables of the same hash".into())
}

// `getStateConjunction`.
fn state_conjunction(
    spec: &TraceSpec,
    state: &RecordedState,
    prefix: Option<&str>,
) -> Result<String, String> {
    if state.mark != Mark::State {
        return Ok("null".into());
    }
    let mut formula = String::new();
    if let Some(prefix) = prefix {
        formula.push_str(&format!("{prefix}\n/\\\n"));
    }
    let conjuncts: Vec<String> = hashed_variables(spec, state)?
        .into_iter()
        .map(|(name, value)| format!("{name} = ({value})"))
        .collect();
    formula.push_str(&conjuncts.join("\n/\\\n"));
    Ok(indent(&formula, 2))
}

// `MCState.asSimpleRecord`.
fn simple_record(spec: &TraceSpec, state: &RecordedState) -> Result<String, String> {
    let fields: Vec<String> = hashed_variables(spec, state)?
        .into_iter()
        .map(|(name, value)| format!("{name} |-> {value}"))
        .collect();
    Ok(format!("[{}]", fields.join(",")))
}

/// The spec's text, `writeSpecTEStreams` as TLC writes it to the file.
fn get_text(spec: &TraceSpec, trace: &[RecordedState], date: &str) -> Result<String, String> {
    if trace
        .iter()
        .flat_map(|state| &state.values)
        .flatten()
        .any(|value| value.contains('\u{fffd}'))
    {
        return Err("a lone surrogate in the trace exploration spec".into());
    }
    let module = spec.module.as_str();
    let last = trace.last().ok_or("an empty trace")?;
    let is_lasso = last.mark == Mark::BackToState;
    let mut tla = String::new();
    let mut cfg = String::new();

    let mut constants: Vec<String> = spec
        .constants
        .iter()
        .map(|entry| match entry.as_slice() {
            [key, value, ..] => indent(&format!("{key} = {value}"), 1),
            [line] => indent(line, 1),
            [] => indent("", 1),
        })
        .collect();
    let reified = java_hash_order(
        spec.model_values
            .iter()
            .map(|value| (value.hash, value.name.as_str()))
            .collect(),
    )
    .ok_or("the order of many model values of the same hash")?;
    constants.extend(
        reified
            .iter()
            .map(|name| indent(&format!("{name} = {name}"), 1)),
    );
    if is_lasso {
        constants.push(format!("_TTraceLassoStart = {}", last.number));
        constants.push(format!("_TTraceLassoEnd = {}", trace.len() - 1));
    }
    if !constants.is_empty() {
        cfg.push_str("CONSTANTS\n");
        for constant in &constants {
            cfg.push_str(&format!("{constant}\n"));
        }
    }

    let mut module_constants: Vec<&str> = spec
        .model_values
        .iter()
        .filter(|value| !value.is_defined)
        .map(|value| value.name.as_str())
        .collect();
    if is_lasso {
        module_constants.extend(["_TTraceLassoStart", "_TTraceLassoEnd"]);
    }
    let constants_module = format!("{module}_TEConstants");
    let constant_modules = if module_constants.is_empty() {
        module_set(&["TLC"])
    } else {
        module_set(&["TLC", &constants_module])
    };
    let constant_module_names: Vec<&str> = constant_modules.iter().map(String::as_str).collect();
    let extended = module_set(
        &[
            &["Toolbox", "TLCExt", "Naturals", "Sequences"][..],
            &constant_module_names,
            &[module],
        ]
        .concat(),
    );

    tla.push_str(&primer(&spec.name, &extended));
    let expression_module = format!("{module}_TEExpression");
    tla.push_str(&format!(
        "_expression ==\n{INDENT}LET {expression_module} == INSTANCE {expression_module}\n{INDENT}IN {expression_module}!expression\n{SEPARATOR}\n\n"
    ));
    let trace_module = format!("{module}_TETrace");
    tla.push_str(&format!(
        "_trace ==\n{INDENT}LET {trace_module} == INSTANCE {trace_module}\n{INDENT}IN {trace_module}!trace\n{SEPARATOR}\n"
    ));

    match last.mark {
        Mark::Stuttering => {
            let state = &trace[trace.len() - 2];
            cfg.push_str(&format!("\nPROPERTY\n{INDENT}_prop\n"));
            tla.push_str(&format!(
                "\n_prop ==\n{INDENT}~<>[](\n{}\n{INDENT})",
                state_conjunction(spec, state, None)?
            ));
        }
        Mark::BackToState => {
            let state = &trace[trace.len() - 2];
            let back = trace
                .get(last.number.wrapping_sub(1))
                .ok_or("a lasso back to a state the trace doesn't hold")?;
            cfg.push_str(&format!("\nPROPERTY\n{INDENT}_prop\n"));
            let property = format!(
                "~(([]<>(\n{}\n))/\\([]<>(\n{}\n)))",
                state_conjunction(spec, state, None)?,
                state_conjunction(spec, back, None)?
            );
            tla.push_str(&format!("\n_prop ==\n{}", indent(&property, 1)));
        }
        Mark::State => {
            cfg.push_str(&format!("\nINVARIANT\n{INDENT}_inv\n"));
            tla.push_str(&format!(
                "\n_inv ==\n{INDENT}~(\n{}\n{INDENT})",
                state_conjunction(spec, last, Some("TLCGet(\"level\") = Len(_TETrace)"))?
            ));
        }
    }
    tla.push_str(&format!("\n{SEPARATOR}\n\n"));
    cfg.push_str(&format!(
        "\nCHECK_DEADLOCK\n{INDENT}\\* CHECK_DEADLOCK off because of PROPERTY or INVARIANT above.\n{INDENT}FALSE"
    ));

    cfg.push_str(&format!("\n\nINIT\n{INDENT}_init\n"));
    tla.push_str("_init ==\n");
    for variable in &spec.variables {
        tla.push_str(&format!(
            "{INDENT}/\\ {variable} = _TETrace[1].{variable}\n"
        ));
    }
    tla.push_str(&format!("{SEPARATOR}\n\n"));
    cfg.push_str(&format!("\nNEXT\n{INDENT}_next\n"));
    tla.push_str("_next ==\n");
    if trace.len() == 1 {
        tla.push_str(&format!("{INDENT}{INDENT}/\\ FALSE\n"));
    } else {
        tla.push_str(&format!("{INDENT}/\\ \\E i,j \\in DOMAIN _TETrace:\n"));
        tla.push_str(&format!("{INDENT}{INDENT}/\\ \\/ /\\ j = i + 1\n"));
        tla.push_str(&format!(
            "{INDENT}{INDENT}  {INDENT}/\\ i = TLCGet(\"level\")\n"
        ));
        if is_lasso {
            tla.push_str(&format!("{INDENT}{INDENT}   \\/ /\\ i = _TTraceLassoEnd\n"));
            tla.push_str(&format!(
                "{INDENT}{INDENT}  {INDENT}/\\ j = _TTraceLassoStart\n"
            ));
        }
        for variable in &spec.variables {
            tla.push_str(&format!(
                "{INDENT}{INDENT}/\\ {variable}  = _TETrace[i].{variable}\n"
            ));
            tla.push_str(&format!(
                "{INDENT}{INDENT}/\\ {variable}' = _TETrace[j].{variable}\n"
            ));
        }
    }
    let json = format!("{INDENT}\\* ");
    tla.push_str("\n\\* Uncomment the ASSUME below to write the states of the error trace\n");
    tla.push_str("\\* to the given file in Json format. Note that you can pass any tuple\n");
    tla.push_str("\\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.\n");
    tla.push_str(&format!("{json}ASSUME\n"));
    tla.push_str(&format!("{json}{INDENT}LET J == INSTANCE Json\n"));
    tla.push_str(&format!(
        "{json}{INDENT}{INDENT}IN J!JsonSerialize(\"{}.json\", _TETrace)\n",
        spec.name
    ));
    tla.push('\n');

    // `MCError.isLassoWithDuplicates` compares the trace's length with the number of distinct
    // states before its last, which is always fewer, so every lasso has a VIEW.
    if is_lasso {
        cfg.push_str(&format!("\nVIEW\n{INDENT}_view\n"));
        tla.push_str(&format!(
            "\n_view ==\n{INDENT}<<{}, IF TLCGet(\"level\") = _TTraceLassoEnd + 1 THEN _TTraceLassoStart ELSE TLCGet(\"level\")>>\n",
            spec.variables.join(", ")
        ));
    }
    tla.push_str(&closing_tag());
    tla.push('\n');

    tla.push_str(&format!(
        " Note that you can extract this module `{expression_module}`\n"
    ));
    tla.push_str("  to a dedicated file to reuse `expression` (the module in the \n");
    tla.push_str(&format!(
        "  dedicated `{expression_module}.tla` file takes precedence \n"
    ));
    tla.push_str(&format!("  over the module `{expression_module}` below)."));
    let expression = format!(
        "\n{}{}{}",
        primer(&expression_module, &extended),
        expression_stub(module, &spec.variables),
        closing_tag()
    );
    tla.push_str(&format!("\n{expression}\n\n"));

    tla.push('\n');
    tla.push_str("Parsing and semantic processing can take forever if the trace below is long.\n");
    tla.push_str(" In this case, it is advised to uncomment the module below to deserialize the\n");
    tla.push_str(" trace from a generated binary file.\n");
    let io_modules = module_set(&[&["IOUtils"][..], &constant_module_names, &[module]].concat());
    let deserialized = format!(
        "\n{}trace == IODeserialize(\"{}.bin\", TRUE)\n\n{}",
        primer(&trace_module, &io_modules),
        spec.name,
        closing_tag()
    );
    let commented = format!("\\*{}", deserialized.replace('\n', "\n\\*"));
    tla.push_str(&format!("\n{commented}\n\n"));

    let trace_modules = module_set(&[&constant_module_names[..], &[module]].concat());
    tla.push_str(&primer(&trace_module, &trace_modules));
    let records = trace
        .iter()
        .filter(|state| state.mark == Mark::State)
        .map(|state| Ok(format!("{INDENT}({})", simple_record(spec, state)?)))
        .collect::<Result<Vec<_>, String>>()?;
    tla.push_str(&format!(
        "trace == \n{INDENT}<<\n{}\n{INDENT}>>\n{SEPARATOR}\n\n\n",
        records.join(",\n")
    ));
    cfg.push_str(&format!("\nCONSTANT\n{INDENT}_TETrace <- _trace\n"));
    cfg.push_str(&format!("\nALIAS\n{INDENT}_expression\n"));

    if !module_constants.is_empty() {
        tla.push_str(&closing_tag());
        tla.push('\n');
        tla.push_str(&primer(&constants_module, &[module.to_string()]));
        tla.push_str(&format!("CONSTANTS {}\n\n", module_constants.join(", ")));
    }
    tla.push_str(&closing_tag());
    Ok(format!(
        "{tla}\n{SEPARATOR} CONFIG {} {SEPARATOR}\n{cfg}{}\\* Generated on {date}",
        spec.name,
        closing_tag()
    ))
}

// `addTraceExpressionStub`: the identity alias over the variables, with comments.
fn expression_stub(module: &str, variables: &[String]) -> String {
    let mut local = String::new();
    local.push_str(&format!(
        "\\* To hide variables of the `{module}` spec from the error trace,\n"
    ));
    local.push_str("\\* remove the variables below.  The trace will be written in the order\n");
    local.push_str("\\* of the fields of this record.\n");
    let fields: Vec<String> = variables
        .iter()
        .map(|variable| format!("{variable} |-> {variable}"))
        .collect();
    local.push_str(&format!("{}\n\n", fields.join("\n,")));
    local.push_str("\\* Put additional constant-, state-, and action-level expressions here:\n");
    local.push_str("\\* ,_stateNumber |-> _TEPosition\n");
    if let Some(variable) = variables.first() {
        local.push_str(&format!(
            "\\* ,_{variable}Unchanged |-> {variable} = {variable}'\n\n"
        ));
        local.push_str(&format!(
            "\\* Format the `{variable}` variable as Json value.\n"
        ));
        local.push_str(&format!("\\* ,_{variable}Json |->\n"));
        local.push_str(&format!("\\* {INDENT}LET J == INSTANCE Json\n"));
        local.push_str(&format!("\\* {INDENT}IN J!ToJson({variable})\n\n"));
        local.push_str("\\* Lastly, you may build expressions over arbitrary sets of states by\n");
        local.push_str("\\* leveraging the _TETrace operator.  For example, this is how to\n");
        local.push_str("\\* count the number of times a spec variable changed up to the current\n");
        local.push_str("\\* state in the trace.\n");
        local.push_str(&format!("\\* ,_{variable}ModCount |->\n"));
        local.push_str(&format!("\\* {INDENT}LET F[s \\in DOMAIN _TETrace] ==\n"));
        local.push_str(&format!("\\* {INDENT}{INDENT}IF s = 1 THEN 0\n"));
        local.push_str(&format!(
            "\\* {INDENT}{INDENT}ELSE IF _TETrace[s].{variable} # _TETrace[s-1].{variable}\n"
        ));
        local.push_str(&format!(
            "\\* {INDENT}{INDENT}{INDENT}THEN 1 + F[s-1] ELSE F[s-1]\n"
        ));
        local.push_str(&format!("\\* {INDENT}IN F[_TEPosition - 1]\n"));
    }
    format!(
        "expression == \n{INDENT}[\n{}\n{INDENT}]\n\n",
        indent(&local, 2)
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    // The spec TLC wrote at d8fb231 in tests/te-spec/<case>, its name, and the date it wrote.
    fn read_written(case: &str) -> (String, String, String) {
        let directory = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/te-spec")
            .join(case);
        let path = std::fs::read_dir(&directory)
            .expect("the case")
            .map(|entry| entry.expect("an entry").path())
            .find(|path| path.to_string_lossy().contains("_TTrace_"))
            .expect("the spec TLC wrote");
        let text = std::fs::read_to_string(&path).expect("the spec");
        let name = path
            .file_stem()
            .expect("a stem")
            .to_string_lossy()
            .into_owned();
        let date = text
            .rsplit_once("\\* Generated on ")
            .expect("the date")
            .1
            .to_string();
        (text, name, date)
    }

    fn state(number: usize, values: &[&str], mark: Mark) -> RecordedState {
        RecordedState {
            number,
            values: values.iter().map(|value| Some(value.to_string())).collect(),
            mark,
        }
    }

    fn spec(module: &str, name: String, variables: &[&str]) -> TraceSpec {
        TraceSpec {
            module: module.into(),
            name,
            directory: ".".into(),
            variables: variables
                .iter()
                .map(|variable| variable.to_string())
                .collect(),
            constants: Vec::new(),
            model_values: Vec::new(),
            unsupported: None,
        }
    }

    #[test]
    fn writes_the_spec_of_a_deadlock_as_tlc() {
        let (text, name, date) = read_written("deadlock");
        let trace = [
            state(1, &["0", "\"a\""], Mark::State),
            state(2, &["1", "\"a\""], Mark::State),
            state(3, &["2", "\"a\""], Mark::State),
        ];
        let written = get_text(&spec("Dead", name, &["x", "y"]), &trace, &date);
        assert_eq!(written.as_deref(), Ok(text.as_str()));
    }

    #[test]
    fn writes_the_spec_of_a_lasso_as_tlc() {
        let (text, name, date) = read_written("lasso");
        let trace = [
            state(1, &["0"], Mark::State),
            state(2, &["1"], Mark::State),
            state(3, &["2"], Mark::State),
            state(1, &["0"], Mark::BackToState),
        ];
        let written = get_text(&spec("Loop", name, &["x"]), &trace, &date);
        assert_eq!(written.as_deref(), Ok(text.as_str()));
    }

    #[test]
    fn writes_the_spec_of_a_trace_that_stutters_as_tlc() {
        let (text, name, date) = read_written("stutter");
        let trace = [
            state(1, &["0"], Mark::State),
            state(2, &["1"], Mark::State),
            state(3, &["2"], Mark::State),
            state(3, &["2"], Mark::Stuttering),
        ];
        let written = get_text(&spec("Stut", name, &["x"]), &trace, &date);
        assert_eq!(written.as_deref(), Ok(text.as_str()));
    }

    #[test]
    fn orders_keys_as_a_java_hash_set() {
        // `new HashSet<>(List.of(...))` in Java iterates these names in this order.
        let names = ["Toolbox", "TLCExt", "Naturals", "Sequences", "TLC", "Viol"];
        let ordered = java_hash_order(
            names
                .iter()
                .map(|name| (java_string_hash(name), *name))
                .collect(),
        )
        .expect("no tree");
        assert_eq!(
            ordered,
            ["Sequences", "TLCExt", "Toolbox", "Viol", "Naturals", "TLC"]
        );
    }

    #[test]
    fn hashes_strings_as_java() {
        assert_eq!(java_string_hash("TLC"), 83_147);
        assert_eq!(java_string_hash(""), 0);
    }
}
