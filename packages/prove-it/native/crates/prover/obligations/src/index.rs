//! Generates the proof obligations tlapm prints for a module, in tlapm's order and layout.
//! A port of `src/obligations/index.ts`.
//!
//! The TypeScript's maps of modules are iterated, so `modules` is an `OrderedMap`; the others are
//! only looked up. Offsets into a source are JavaScript's UTF-16 offsets, as `findTab` takes them.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use tla_front::ast::Module;
use tla_front::errors::{SyntaxError, SyntaxFailure};
use tla_front::lexer::{TokenKind, tokenize};
use tla_front::ordered_map::OrderedMap;
use tla_front::parser::parse_tlapm_module;

use crate::anonymize::create_anonymizer;
use crate::errors::{ObligationError, Result, quote_json};
use crate::expression::{
    Channel, Locus, ObligationWarning, Sequent, Warn, get_at_prefix, get_error_note,
    get_locus_position, get_locus_prefix,
};
use crate::generate::{LineRange, ModuleSummary, TheoremSummary, create_generator};
use crate::module::{Mule, compare_names, flatten, get_dependencies, get_standard_modules};
use crate::normalize::{Pipeline, normalize};
use crate::pragma::OldMethod;
use crate::printer::format_obligation;
use crate::proof::{Counter, ObligationKind};
use crate::simplify::create_simplifier;
use crate::source::create_source;

#[derive(Clone, Debug)]
pub struct ObligationSource {
    pub file: String,
    pub source: String,
}

#[derive(Clone, Debug)]
pub struct PrintedObligation {
    pub id: usize,
    pub location: String,
    pub locus: Option<Locus>,
    pub text: String,
    pub kind: ObligationKind,
    pub sequent: Sequent,
    pub method: Option<OldMethod>,
}

#[derive(Clone, Debug)]
pub struct ModuleObligations {
    pub name: String,
    pub location: Option<Locus>,
    pub obligations: Vec<PrintedObligation>,
    pub summary: ModuleSummary,
}

pub const WHOLE_MODULE: LineRange = LineRange {
    start: 0.0,
    end: f64::INFINITY,
};

const END_FAILURE: &str = "Unexpected EOF";

const DASH: u16 = b'-' as u16;
const SPACE: u16 = b' ' as u16;
const TAB: u16 = b'\t' as u16;
const NEWLINE: u16 = b'\n' as u16;

/// `source.search(/-{4,} *MODULE/)`: the leftmost match, in UTF-16 units.
fn search_module_header(units: &[u16]) -> Option<usize> {
    let module: Vec<u16> = "MODULE".encode_utf16().collect();
    let mut index = 0;
    while index < units.len() {
        if units[index] != DASH {
            index += 1;
            continue;
        }
        let dashes_end = index
            + units[index..]
                .iter()
                .take_while(|unit| **unit == DASH)
                .count();
        let spaces_end = dashes_end
            + units[dashes_end..]
                .iter()
                .take_while(|unit| **unit == SPACE)
                .count();
        // A later start in the same run of dashes is followed by the same text.
        if dashes_end - index >= 4 && units[spaces_end..].starts_with(&module) {
            return Some(index);
        }
        index = dashes_end;
    }
    None
}

fn find_units(units: &[u16], needle: &[u16]) -> Option<usize> {
    units
        .windows(needle.len())
        .position(|window| window == needle)
}

fn format_locus(locus: Option<&Locus>) -> String {
    locus.map_or_else(String::new, |locus| {
        format!(
            "{}:{}:{}:{}",
            locus.start_line, locus.start_column, locus.end_line, locus.end_column
        )
    })
}

struct Tab {
    offset: usize,
    line: u32,
    column: u32,
    end: SyntaxFailure,
}

/// `catchSyntaxFailure`: a syntax error with a failure becomes the failure.
fn catch_syntax_failure<Value>(
    read: std::result::Result<Value, SyntaxError>,
) -> Result<std::result::Result<Value, SyntaxFailure>> {
    match read {
        Ok(value) => Ok(Ok(value)),
        Err(error) => match error.failure {
            Some(failure) => Ok(Err(failure)),
            None => Err(ObligationError::Syntax(error.message)),
        },
    }
}

fn find_tab(source: &str) -> std::result::Result<Option<Tab>, SyntaxError> {
    let tokens = tokenize(source)?;
    let units: Vec<u16> = source.encode_utf16().collect();
    let lines: Vec<&[u16]> = units.split(|unit| *unit == NEWLINE).collect();
    let end_line = tokens
        .last()
        .map_or(lines.len(), |token| token.line as usize);
    let before: i64 = lines
        .iter()
        .take(end_line.saturating_sub(1))
        .map(|line| line.len() as i64 + 1)
        .sum();
    let equals: Vec<u16> = "====".encode_utf16().collect();
    let module_end = before
        + end_line
            .checked_sub(1)
            .and_then(|index| lines.get(index))
            .and_then(|line| find_units(line, &equals))
            .map_or(-1, |index| index as i64);
    let start = search_module_header(&units).unwrap_or(0);
    let Some(offset) = units[start..]
        .iter()
        .position(|unit| *unit == TAB)
        .map(|index| start + index)
    else {
        return Ok(None);
    };
    if offset as i64 >= module_end {
        return Ok(None);
    }
    let line = units[..offset]
        .iter()
        .filter(|unit| **unit == NEWLINE)
        .count() as u32
        + 1;
    let column = units[..offset]
        .iter()
        .rposition(|unit| *unit == NEWLINE)
        .map_or(offset + 1, |newline| offset - newline) as u32;
    let last = tokens.iter().rev().find(|token| {
        token.kind != TokenKind::End
            && (token.line < line || (token.line == line && token.column < column))
    });
    let end = SyntaxFailure {
        reason: END_FAILURE.to_owned(),
        line: last.map_or(line, |token| token.line),
        column: last.map_or(column, |token| token.end_column + 1),
        is_end: true,
    };
    Ok(Some(Tab {
        offset,
        line,
        column,
        end,
    }))
}

/// The byte offset of a UTF-16 offset that falls on a character's start.
fn get_byte_offset(source: &str, offset: usize) -> usize {
    let mut units = 0;
    for (index, character) in source.char_indices() {
        if units >= offset {
            return index;
        }
        units += character.len_utf16();
    }
    source.len()
}

/// The module, or the failures tlapm reports.
fn parse_source(source: &str) -> Result<std::result::Result<Module, Vec<SyntaxFailure>>> {
    let tab = match catch_syntax_failure(find_tab(source))? {
        Ok(tab) => tab,
        Err(failure) => return Ok(Err(vec![failure])),
    };
    let text = tab
        .as_ref()
        .map_or(source, |tab| &source[..get_byte_offset(source, tab.offset)]);
    let parsed = catch_syntax_failure(parse_tlapm_module(text, None))?;
    if let Some(tab) = tab
        && parsed.as_ref().err().is_none_or(|failure| failure.is_end)
    {
        let end = match parsed {
            Err(failure) if failure.reason == END_FAILURE => failure,
            _ => tab.end,
        };
        return Ok(Err(vec![
            SyntaxFailure {
                reason: "Unexpected TAB character. TLAPS does not handle TAB characters in source files.".to_owned(),
                line: tab.line,
                column: tab.column,
                is_end: false,
            },
            end,
        ]));
    }
    Ok(parsed.map_err(|failure| vec![failure]))
}

// Module.Save.parse_file warns when a module's name differs from its file's, then renames it.
fn load_mule(
    input: &ObligationSource,
    counter: &Rc<Counter>,
    is_main: bool,
    on_warning: &mut Warn,
    error_prefix: &str,
) -> Result<Mule> {
    let units: Vec<u16> = input.source.encode_utf16().collect();
    if search_module_header(&units).is_none() {
        return Err(ObligationError::proof("No tokens in file"));
    }
    let parsed = match parse_source(&input.source)? {
        Ok(module) => module,
        Err(failures) => {
            for failure in failures {
                let text = format!(
                    "File {}, line {}, character {}\n{}",
                    quote_json(&input.file),
                    failure.line,
                    failure.column,
                    failure.reason
                );
                on_warning(ObligationWarning {
                    text: text.clone(),
                    channel: Channel::Stderr,
                });
                on_warning(ObligationWarning {
                    text: format!("{text}\n"),
                    channel: Channel::ToolboxOnly,
                });
            }
            let message = format!("Could not parse {} successfully.", quote_json(&input.file));
            on_warning(ObligationWarning {
                text: format!("{error_prefix}Error: {message}"),
                channel: Channel::Stderr,
            });
            return Err(ObligationError::proof_failure(
                message,
                "Module.Parser.parse_file",
            ));
        }
    };
    let mule = create_source(&input.file, &input.source, counter.clone(), is_main)
        .convert_module(&parsed)?;
    let file_name = &input.file[input.file.rfind('/').map_or(0, |slash| slash + 1)..];
    let name = file_name.strip_suffix(".tla").unwrap_or(file_name);
    if mule.name == name {
        return Ok(mule);
    }
    on_warning(ObligationWarning {
        text: format!(
            "{}Warning: module name {} does not match file name {}.",
            get_locus_prefix(mule.location.as_ref()),
            quote_json(&mule.name),
            quote_json(file_name)
        ),
        channel: Channel::Toolbox,
    });
    Ok(Mule {
        name: name.to_owned(),
        ..mule
    })
}

// Module.Dep.schedule: dependencies first, visiting modules and their dependencies by name.
fn schedule(modules: &OrderedMap<String, Rc<Mule>>) -> Result<Vec<Rc<Mule>>> {
    let dependencies: HashMap<&str, Vec<String>> = modules
        .iter()
        .map(|(name, module)| (name.as_str(), get_dependencies(module).dependencies))
        .collect();
    fn visit(
        name: &str,
        modules: &OrderedMap<String, Rc<Mule>>,
        dependencies: &HashMap<&str, Vec<String>>,
        seen: &mut HashSet<String>,
        order: &mut Vec<Rc<Mule>>,
    ) -> Result<()> {
        if !seen.insert(name.to_owned()) {
            return Ok(());
        }
        let module = modules
            .get(name)
            .ok_or_else(|| ObligationError::proof(format!("Module \"{name}\" not found")))?;
        for dependency in dependencies.get(name).into_iter().flatten() {
            visit(dependency, modules, dependencies, seen, order)?;
        }
        order.push(module.clone());
        Ok(())
    }
    let mut names: Vec<&String> = modules.keys().collect();
    names.sort_by(|left, right| compare_names(left, right));
    let mut seen = HashSet::new();
    let mut order = Vec::new();
    for name in names {
        visit(name, modules, &dependencies, &mut seen, &mut order)?;
    }
    Ok(order)
}

fn format_proofs(kind: &str, loci: &[Locus], before: usize) -> Vec<String> {
    if loci.is_empty() {
        return Vec::new();
    }
    [format!("    {kind}_proofs_count = {}", loci.len())]
        .into_iter()
        .chain(loci.iter().enumerate().map(|(index, locus)| {
            format!(
                "    {kind}_proof_{} at {}",
                before + index + 1,
                get_locus_position(locus)
            )
        }))
        .collect()
}

fn format_theorem_summary(theorem: &TheoremSummary, missing: usize, omitted: usize) -> Vec<String> {
    let start = theorem.location.as_ref().map_or_else(
        || "<unknown location>".to_owned(),
        |location| {
            get_locus_position(&Locus {
                end_line: location.start_line,
                end_column: location.start_column,
                ..location.clone()
            })
        },
    );
    [format!(
        "  ---- incomplete proof of theorem at {start} ----"
    )]
    .into_iter()
    .chain(format_proofs("missing", &theorem.absent, missing))
    .chain(format_proofs("omitted", &theorem.omitted, omitted))
    .chain(["  ====".to_owned()])
    .collect()
}

pub fn format_summary(result: &ModuleObligations) -> String {
    let summary = &result.summary;
    let mut theorems = Vec::new();
    let mut missing = 0;
    let mut omitted = 0;
    for theorem in &summary.theorems {
        if theorem.absent.len() + theorem.omitted.len() == 0 {
            continue;
        }
        theorems.extend(format_theorem_summary(theorem, missing, omitted));
        missing += theorem.absent.len();
        omitted += theorem.omitted.len();
    }
    let mut lines = vec![
        format!("---- summary of module {} ----", quote_json(&result.name)),
        format!("  obligations_count = {}", summary.total),
    ];
    if !summary.absent.is_empty() {
        lines.push(format!("  missing_proofs_count = {}", summary.absent.len()));
    }
    if !summary.omitted.is_empty() {
        lines.push(format!(
            "  omitted_proofs_count = {}",
            summary.omitted.len()
        ));
    }
    lines.extend(theorems);
    lines.push("====".to_owned());
    lines.join("\n")
}

// Each main module is one file given to tlapm. They load into one context and report in schedule
// order, each numbering its obligations from 1.
pub fn get_obligations(
    mains: &[ObligationSource],
    load_module: &mut dyn FnMut(&str) -> Option<ObligationSource>,
    lines: Option<LineRange>,
    on_warning: &mut Warn,
) -> Result<Vec<ModuleObligations>> {
    let lines = lines.unwrap_or(WHOLE_MODULE);
    let counter = Rc::new(Counter::default());
    let standard_modules = get_standard_modules();
    let standard_names: HashSet<String> = standard_modules
        .iter()
        .map(|module| module.name.clone())
        .collect();
    let mut modules: OrderedMap<String, Rc<Mule>> = standard_modules
        .into_iter()
        .map(|module| (module.name.clone(), Rc::new(module)))
        .collect();
    for main in mains {
        let module = Mule {
            is_important: true,
            ..load_mule(main, &counter, true, on_warning, "File \"<unknown>\":\n")?
        };
        modules.insert(module.name.clone(), Rc::new(module));
    }
    // Module.Save.complete_load: breadth first from every known module, by name.
    let mut queue: Vec<Rc<Mule>> = modules.values().cloned().collect();
    queue.sort_by(|left, right| compare_names(&left.name, &right.name));
    // A missing module is fine only if some loaded module declares it as a submodule.
    let mut requested: OrderedMap<String, Option<Locus>> = OrderedMap::new();
    let mut found = HashSet::new();
    let mut index = 0;
    while index < queue.len() {
        let result = get_dependencies(&queue[index]);
        index += 1;
        let get_location = |name: &str| {
            result
                .locations
                .iter()
                .find(|entry| entry.0 == name)
                .and_then(|entry| entry.1.clone())
        };
        for (name, submodule) in &result.submodules {
            found.insert(name.clone());
            if !modules.contains_key(name) {
                modules.insert(name.clone(), Rc::new(submodule.clone()));
            }
        }
        // A file named like a standard module replaces it, and is read again for each module citing it.
        for name in &result.dependencies {
            if modules.contains_key(name) && !standard_names.contains(name) {
                continue;
            }
            let Some(input) = load_module(name) else {
                if !modules.contains_key(name) && !requested.contains_key(name) {
                    requested.insert(name.clone(), get_location(name));
                }
                continue;
            };
            let loaded = Rc::new(load_mule(
                &input,
                &counter,
                false,
                on_warning,
                &get_at_prefix(get_location(name).as_ref()),
            )?);
            modules.insert(name.clone(), loaded.clone());
            queue.push(loaded);
        }
    }
    let mut missing: Vec<&String> = requested
        .keys()
        .filter(|name| !found.contains(*name))
        .collect();
    missing.sort_by(|left, right| compare_names(left, right));
    for name in &missing {
        on_warning(get_error_note(
            requested.get(*name).and_then(Option::as_ref),
            &format!("Unknown module {}", quote_json(name)),
        ));
    }
    if let Some(name) = missing.first() {
        return Err(ObligationError::proof_failure(
            format!("Unknown module {}", quote_json(name)),
            "Module.Parser.load_module",
        ));
    }
    let order = schedule(&modules)?
        .into_iter()
        .map(|module| {
            if module.is_standard {
                return Ok(module);
            }
            Ok(Rc::new(flatten(
                &|name| modules.get(name).map(|module| &**module),
                &module,
                &mut HashSet::new(),
                None,
            )?))
        })
        .collect::<Result<Vec<_>>>()?;
    let mut pipeline = Pipeline {
        anonymizer: create_anonymizer(counter.clone()),
        simplify: create_simplifier(counter),
        salts: Counter::default(),
        latest_modules: HashMap::new(),
        on_warning: RefCell::new(on_warning),
    };
    let generator = create_generator(mains.iter().map(|main| main.file.clone()).collect(), lines);
    // Instances see each module as flattened, and as normalized once its turn has come.
    let mut normalized: HashMap<String, Rc<Mule>> = order
        .iter()
        .map(|module| (module.name.clone(), module.clone()))
        .collect();
    let mut results = Vec::new();
    for module in &order {
        if module.is_standard {
            continue;
        }
        let result = normalize(&mut pipeline, &mut normalized, &None, module)?;
        if !module.is_important {
            continue;
        }
        let generated = {
            let mut sink = pipeline.on_warning.borrow_mut();
            generator.generate_module(&mut **sink, &[], &result)?
        };
        // tlapm numbers the obligations, then drops the omitted ones and those outside the lines.
        let mut obligations = Vec::new();
        for (index, obligation) in generated.obligations.into_iter().enumerate() {
            let location = obligation.location;
            if matches!(obligation.kind, ObligationKind::Omitted(_))
                || location.as_ref().is_some_and(|location| {
                    f64::from(location.start_line) < lines.start
                        || f64::from(location.end_line) > lines.end
                })
            {
                continue;
            }
            let text = match &obligation.kind {
                ObligationKind::Error(message) => message.clone(),
                _ => format!("{}\n", format_obligation(&obligation.sequent)?),
            };
            obligations.push(PrintedObligation {
                id: index + 1,
                location: format_locus(location.as_ref()),
                locus: location,
                text,
                kind: obligation.kind,
                sequent: obligation.sequent,
                method: obligation.method,
            });
        }
        results.push(ModuleObligations {
            name: module.name.clone(),
            location: module.location.clone(),
            obligations,
            summary: generated.summary,
        });
    }
    Ok(results)
}

#[cfg(test)]
mod tests {
    use super::*;

    // The expected values come from running the TypeScript.

    struct Run {
        results: Result<Vec<ModuleObligations>>,
        warnings: Vec<(Channel, String)>,
    }

    fn run(file: &str, source: &str, modules: &[(&str, &str)], lines: Option<LineRange>) -> Run {
        let mut warnings = Vec::new();
        let results = get_obligations(
            &[ObligationSource {
                file: file.to_owned(),
                source: source.to_owned(),
            }],
            &mut |name| {
                modules
                    .iter()
                    .find(|module| module.0 == name)
                    .map(|module| ObligationSource {
                        file: format!("{name}.tla"),
                        source: module.1.to_owned(),
                    })
            },
            lines,
            &mut |warning| warnings.push((warning.channel, warning.text)),
        );
        Run { results, warnings }
    }

    /// Each obligation's id, location, kind and text.
    fn get_printed(run: &Run) -> Vec<(usize, String, ObligationKind, String)> {
        let results = run.results.as_ref().expect("obligations");
        assert_eq!(results.len(), 1);
        results[0]
            .obligations
            .iter()
            .map(|obligation| {
                (
                    obligation.id,
                    obligation.location.clone(),
                    obligation.kind.clone(),
                    obligation.text.clone(),
                )
            })
            .collect()
    }

    fn get_summary(run: &Run) -> String {
        format_summary(&run.results.as_ref().expect("obligations")[0])
    }

    fn get_texts(body: &str) -> Vec<String> {
        let source = format!("---- MODULE M ----\nEXTENDS Naturals\n{body}\n====\n");
        get_printed(&run("M.tla", &source, &[], None))
            .into_iter()
            .map(|printed| printed.3)
            .collect()
    }

    fn get_parse_warnings(line: u32, column: u32, reasons: &[&str]) -> Vec<(Channel, String)> {
        let mut warnings = Vec::new();
        for reason in reasons {
            let text = format!("File \"M.tla\", line {line}, character {column}\n{reason}");
            warnings.push((Channel::Stderr, text.clone()));
            warnings.push((Channel::ToolboxOnly, format!("{text}\n")));
        }
        warnings.push((
            Channel::Stderr,
            "File \"<unknown>\":\nError: Could not parse \"M.tla\" successfully.".to_owned(),
        ));
        warnings
    }

    const TAB_REASON: &str =
        "Unexpected TAB character. TLAPS does not handle TAB characters in source files.";

    #[test]
    fn prints_an_at_that_no_earlier_step_defines() {
        let texts = get_texts(
            &[
                "VARIABLE x",
                "THEOREM x = 1",
                "<1>1. TRUE",
                "  OBVIOUS",
                "<1>2. @ = x",
                "  OBVIOUS",
                "<1>3. QED",
                "  OBVIOUS",
            ]
            .join("\n"),
        );
        assert_eq!(
            texts,
            [
                "ASSUME NEW VARIABLE x\nPROVE  x = 1\n",
                "ASSUME NEW VARIABLE x\nPROVE  TRUE\n",
                "ASSUME NEW VARIABLE x\nPROVE  @ = x\n",
            ]
        );
    }

    #[test]
    fn summarizes_missing_and_omitted_proofs() {
        let result = run(
            "M.tla",
            "---- MODULE M ----\nEXTENDS Naturals\nTHEOREM T1 == 1 + 1 = 2\nTHEOREM T2 == TRUE\n<1>1. TRUE\n<1>2. QED OMITTED\nTHEOREM T3 == FALSE OBVIOUS\n====\n",
            &[],
            None,
        );
        assert_eq!(
            get_printed(&result),
            [(
                4,
                "7:21:7:28".to_owned(),
                ObligationKind::Main,
                "FALSE\n".to_owned()
            )]
        );
        assert_eq!(
            get_summary(&result),
            "---- summary of module \"M\" ----\n  obligations_count = 4\n  missing_proofs_count = 2\n  omitted_proofs_count = 1\n  ---- incomplete proof of theorem at line 3, character 1 ----\n    missing_proofs_count = 1\n    missing_proof_1 at line 3, character 24\n  ====\n  ---- incomplete proof of theorem at line 4, character 1 ----\n    missing_proofs_count = 1\n    missing_proof_2 at line 5, characters 1-10\n    omitted_proofs_count = 1\n    omitted_proof_1 at line 6, characters 11-17\n  ====\n===="
        );
        assert!(result.warnings.is_empty());
    }

    #[test]
    fn rejects_a_tab_inside_the_module() {
        let result = run(
            "M.tla",
            "---- MODULE M ----\nTHEOREM\tTRUE\n====\n",
            &[],
            None,
        );
        assert_eq!(
            result.results.err(),
            Some(ObligationError::proof_failure(
                "Could not parse \"M.tla\" successfully.",
                "Module.Parser.parse_file"
            ))
        );
        assert_eq!(
            result.warnings,
            get_parse_warnings(2, 8, &[TAB_REASON, END_FAILURE])
        );
    }

    #[test]
    fn counts_the_column_of_a_tab_in_utf16_units() {
        let result = run(
            "M.tla",
            "---- MODULE M ----\n(* \u{1F600}é *) THEOREM TRUE\t\n====\n",
            &[],
            None,
        );
        assert!(result.results.is_err());
        assert_eq!(
            result.warnings,
            get_parse_warnings(2, 23, &[TAB_REASON, END_FAILURE])
        );
    }

    #[test]
    fn ignores_a_tab_after_the_module() {
        let result = run(
            "M.tla",
            "---- MODULE M ----\nTHEOREM TRUE\n====\n\t\n",
            &[],
            None,
        );
        assert_eq!(get_printed(&result), []);
        assert_eq!(
            get_summary(&result),
            "---- summary of module \"M\" ----\n  obligations_count = 1\n  missing_proofs_count = 1\n  ---- incomplete proof of theorem at line 2, character 1 ----\n    missing_proofs_count = 1\n    missing_proof_1 at line 2, character 13\n  ====\n===="
        );
    }

    #[test]
    fn reports_a_parse_failure() {
        let result = run(
            "M.tla",
            "---- MODULE M ----\nTHEOREM 1 = \n====\n",
            &[],
            None,
        );
        assert!(result.results.is_err());
        assert_eq!(
            result.warnings,
            get_parse_warnings(2, 12, &["Unexpected ===="])
        );
    }

    #[test]
    fn reports_unknown_modules_by_name() {
        let result = run(
            "M.tla",
            "---- MODULE M ----\nEXTENDS Foo, Bar\n====\n",
            &[],
            None,
        );
        assert_eq!(
            result.results.err(),
            Some(ObligationError::proof_failure(
                "Unknown module \"Bar\"",
                "Module.Parser.load_module"
            ))
        );
        assert_eq!(
            result.warnings,
            [
                (
                    Channel::Stderr,
                    "File \"M.tla\", line 2, characters 14-16:\nError: Unknown module \"Bar\""
                        .to_owned()
                ),
                (
                    Channel::Stderr,
                    "File \"M.tla\", line 2, characters 9-11:\nError: Unknown module \"Foo\""
                        .to_owned()
                ),
            ]
        );
    }

    #[test]
    fn renames_a_module_after_its_file() {
        let result = run(
            "dir/N.tla",
            "---- MODULE M ----\nTHEOREM TRUE\n====\n",
            &[],
            None,
        );
        assert_eq!(result.results.as_ref().expect("obligations")[0].name, "N");
        assert_eq!(
            result.warnings,
            [(
                Channel::Toolbox,
                "File \"dir/N.tla\", line 1, character 1 to line 3, character 4 :\nWarning: module name \"M\" does not match file name \"N.tla\".".to_owned()
            )]
        );
    }

    #[test]
    fn needs_a_module_header() {
        let result = run("M.tla", "MODULE M\n", &[], None);
        assert_eq!(
            result.results.err(),
            Some(ObligationError::proof("No tokens in file"))
        );
        assert!(result.warnings.is_empty());
    }

    #[test]
    fn loads_the_modules_a_module_extends() {
        let result = run(
            "M.tla",
            "---- MODULE M ----\nEXTENDS A\nTHEOREM X = 1 OBVIOUS\n====\n",
            &[("A", "---- MODULE A ----\nCONSTANT X\n====\n")],
            None,
        );
        assert_eq!(
            get_printed(&result),
            [(
                1,
                "3:15:3:22".to_owned(),
                ObligationKind::Main,
                "ASSUME NEW CONSTANT X\nPROVE  X = 1\n".to_owned()
            )]
        );
        assert_eq!(
            get_summary(&result),
            "---- summary of module \"M\" ----\n  obligations_count = 1\n===="
        );
    }

    #[test]
    fn keeps_the_obligations_of_the_lines() {
        let result = run(
            "M.tla",
            "---- MODULE M ----\nTHEOREM 1 = 1 OBVIOUS\nTHEOREM 2 = 2 OBVIOUS\n====\n",
            &[],
            Some(LineRange {
                start: 3.0,
                end: 3.0,
            }),
        );
        assert_eq!(
            get_printed(&result),
            [(
                1,
                "3:15:3:22".to_owned(),
                ObligationKind::Main,
                "2 = 2\n".to_owned()
            )]
        );
        assert_eq!(
            get_summary(&result),
            "---- summary of module \"M\" ----\n  obligations_count = 1\n===="
        );
    }

    #[test]
    fn matches_the_module_header_leftmost() {
        let get_units = |text: &str| text.encode_utf16().collect::<Vec<u16>>();
        assert_eq!(
            search_module_header(&get_units("--- ----- MODULE M")),
            Some(4)
        );
        assert_eq!(search_module_header(&get_units("x---- \tMODULE")), None);
        assert_eq!(search_module_header(&get_units("é------MODULE")), Some(1));
    }
}
