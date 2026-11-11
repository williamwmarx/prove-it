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
use tla_front::parser::{get_numeral_value, parse_tlapm_module};

use crate::alexer::{Place, find_int_failure};
use crate::anonymize::create_anonymizer;
use crate::errors::{ObligationError, Result, quote_json};
use crate::expression::{
    Channel, Locus, ObligationWarning, Sequent, Warn, get_at_prefix, get_error_note,
    get_locus_position, get_locus_prefix,
};
use crate::generate::{LineRange, ModuleSummary, TheoremSummary, create_generator};
use crate::module::{Mule, compare_names, flatten, get_dependencies, get_standard_modules};
use crate::normalize::{Pipeline, normalize};
use crate::ocaml::{MAX_INT, int_of_string};
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

const ORDER_DECLINE: &str = "an error tlapm may raise as it parses a module or after, beside another module's error or warning, whose order is unknown";

const LEVEL_DECLINE: &str = "a proof whose step level passes OCaml's max_int, where tlapm's wraps around and tla-front's doesn't";

const SELECTOR_DECLINE: &str = "a selector's number of 2^53 or more, which tla-front reads as an f64 and tlapm as an OCaml int";

const INT_DECLINE: &str =
    "a numeral past OCaml's ints, which tlapm fails on, and a parse error that may come first";

/// Whether tlapm's parser may have read the token at `place` before it failed at `failure`. Its
/// lexer is lazy, and `Pco.scan` exposes one token at a time (pco.ml:573-592), so a parser that
/// fails has read the token after the last it took. It may have read further on a path it then
/// gave up: `attempt` and `lookahead` restore the position the failure is reported at
/// (pco.ml:454-541), and `alt`, `star` and `optional` attempt. Such a path stays within the module
/// unit or proof step it began in: an expression or a definition's head takes no `==` outside
/// a LET or brackets, and nothing but a module unit begins with THEOREM, LEMMA, PROPOSITION,
/// COROLLARY, AXIOM, ASSUMPTION, `----` or `====` (module/m_parser.ml:21-74). So the parser reads
/// no further than the second such `==` after the failure, the definition being parsed and the
/// next one's head, or such a keyword; in a proof, whose DEFINE steps hold definitions, no further
/// than such a keyword.
fn may_read_ahead(source: &str, failure: &SyntaxFailure, place: Place) -> bool {
    let Ok(tokens) = tokenize(source) else {
        return true;
    };
    let start = Place {
        line: failure.line,
        column: failure.column,
    };
    let mut definitions = 0;
    let mut brackets = 0usize;
    let mut lets = 0usize;
    let mut is_proof = false;
    for token in tokens {
        let at = Place {
            line: token.line,
            column: token.column,
        };
        if at < start || token.kind == TokenKind::String {
            continue;
        }
        if at >= place {
            return true;
        }
        let text = &*token.text;
        match (token.kind, text) {
            (TokenKind::Separator | TokenKind::ModuleEnd | TokenKind::End, _) => return false,
            (
                TokenKind::Keyword,
                "THEOREM" | "LEMMA" | "PROPOSITION" | "COROLLARY" | "AXIOM" | "ASSUMPTION",
            ) => return false,
            (TokenKind::Keyword, "LET") => lets += 1,
            (TokenKind::Keyword, "IN") => lets = lets.saturating_sub(1),
            (TokenKind::Step, _) => is_proof = true,
            (_, "(" | "[" | "{" | "<<") => brackets += 1,
            (_, ")" | "]" | "]_" | "}" | ">>" | ">>_") => brackets = brackets.saturating_sub(1),
            (_, "==") if brackets == 0 && lets == 0 && !is_proof => {
                definitions += 1;
                if definitions == 2 {
                    return false;
                }
            }
            _ => {}
        }
    }
    true
}

/// Whether a step before a parse failure may be at level `max_int`, where tlapm's subproof
/// level wraps around and tla-front's doesn't, which may be why tla-front fails to parse where
/// tlapm doesn't. A step's level is at most the highest written before it plus the steps between.
fn may_wrap_before(source: &str, failure: &SyntaxFailure) -> bool {
    let Ok(tokens) = tokenize(source) else {
        return false;
    };
    let mut steps = 0i64;
    let mut highest = 0i64;
    for token in tokens
        .iter()
        .take_while(|token| (token.line, token.column) < (failure.line, failure.column))
    {
        if token.kind == TokenKind::Step {
            steps += 1;
            let digits: String = token.text[1..]
                .chars()
                .take_while(char::is_ascii_digit)
                .collect();
            highest = highest.max(int_of_string(&digits).unwrap_or(0));
        }
    }
    steps > 0 && highest.saturating_add(steps) >= MAX_INT
}

/// tlapm raises `Failure "int_of_string"` at `failure.place` (alexer.rs) once its parser reads
/// past `failure.read_by`, before any error it finds later, and the run ends there
/// (tlapm_lib.ml:645-668). A parse that succeeds read it, and so did one that fails past it. One
/// that fails before it reports its error, unless it may have read ahead to it, which is declined,
/// as is a source conversion's error, which has no place to compare. A step whose subproof's level
/// wraps before the token changes what tlapm parses there (`Source::get_wrapped_step`,
/// `may_wrap_before`), which is declined too. `None` goes on with the parse.
fn get_int_failure(
    input: &ObligationSource,
    counter: &Rc<Counter>,
    is_main: bool,
    place: Place,
) -> Option<ObligationError> {
    let error = ObligationError::proof("int_of_string");
    let decline = ObligationError::not_native(INT_DECLINE);
    let level_decline = ObligationError::not_native(LEVEL_DECLINE);
    match parse_source(&input.source) {
        Ok(Ok(module)) => {
            let source = create_source(&input.file, &input.source, counter.clone(), is_main);
            let converted = source.convert_module(&module);
            if source.get_wrapped_step().is_some_and(|step| step < place) {
                return Some(level_decline);
            }
            Some(match converted {
                Ok(_) => error,
                Err(_) => decline,
            })
        }
        Ok(Err(failures)) => {
            let first = failures.first()?;
            let at = Place {
                line: first.line,
                column: first.column,
            };
            if may_wrap_before(&input.source, first) {
                Some(level_decline)
            } else if at > place {
                Some(error)
            } else if may_read_ahead(&input.source, first, place) {
                Some(decline)
            } else {
                None
            }
        }
        Err(_) => Some(decline),
    }
}

/// Whether the module has a number of 2^53 or more after a `!`, as a selector's, which tla-front
/// reads as an f64 that may not hold it exactly, and tlapm's `nat` as an OCaml int
/// (tla_parser.ml:193-196, e_parser.ml:476), which it may not fit or which may wrap. Checked once
/// tla-front parses the module, before any conversion error.
fn has_inexact_selector(source: &str) -> bool {
    let Ok(tokens) = tokenize(source) else {
        return false;
    };
    tokens.windows(2).any(|pair| {
        &*pair[0].text == "!"
            && pair[1].kind == TokenKind::Number
            && get_numeral_value(&pair[1].text) >= 9_007_199_254_740_992.0
    })
}

/// A module as `load_mule` reads it.
enum Loaded {
    Module(Mule),
    /// The source conversion's error, which tlapm may raise as it parses the module or later, and
    /// the modules the module's text extends or instantiates.
    Unconverted {
        error: ObligationError,
        dependencies: Vec<String>,
    },
}

/// The names after EXTENDS and INSTANCE in a module's text, which may be modules it depends on.
fn get_named_modules(source: &str) -> Vec<String> {
    let Ok(tokens) = tokenize(source) else {
        return Vec::new();
    };
    let mut names = Vec::new();
    for (index, token) in tokens.iter().enumerate() {
        if token.kind != TokenKind::Keyword {
            continue;
        }
        match &*token.text {
            "EXTENDS" => {
                for (offset, name) in tokens[index + 1..].iter().enumerate() {
                    match (offset % 2, name.kind, &*name.text) {
                        (0, TokenKind::Identifier, text) => names.push(text.to_owned()),
                        (1, _, ",") => {}
                        _ => break,
                    }
                }
            }
            "INSTANCE" => {
                if let Some(name) = tokens.get(index + 1)
                    && name.kind == TokenKind::Identifier
                {
                    names.push(name.text.to_string());
                }
            }
            _ => {}
        }
    }
    names
}

// Module.Save.parse_file warns when a module's name differs from its file's, then renames it.
// Errors are those tlapm raises as it reads the module: of its lexer, its parser and its
// expansion of a command-line module's tuples.
fn load_mule(
    input: &ObligationSource,
    counter: &Rc<Counter>,
    is_main: bool,
    on_warning: &mut Warn,
    error_prefix: &str,
) -> Result<Loaded> {
    let units: Vec<u16> = input.source.encode_utf16().collect();
    let Some(header) = search_module_header(&units) else {
        return Err(ObligationError::proof("No tokens in file"));
    };
    if let Some(error) = find_int_failure(&units, header)
        .and_then(|place| get_int_failure(input, counter, is_main, place))
    {
        return Err(error);
    }
    let parsed = match parse_source(&input.source)? {
        Ok(module) => module,
        Err(failures)
            if failures
                .first()
                .is_some_and(|first| may_wrap_before(&input.source, first)) =>
        {
            return Err(ObligationError::not_native(LEVEL_DECLINE));
        }
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
    if has_inexact_selector(&input.source) {
        return Err(ObligationError::not_native(SELECTOR_DECLINE));
    }
    let source = create_source(&input.file, &input.source, counter.clone(), is_main);
    let mule = match source.convert_module(&parsed) {
        Ok(mule) => mule,
        Err(error @ ObligationError::NotNative(_)) => return Err(error),
        Err(error) => {
            return Ok(Loaded::Unconverted {
                error,
                dependencies: get_named_modules(&input.source),
            });
        }
    };
    if source.get_wrapped_step().is_some() {
        return Err(ObligationError::not_native(LEVEL_DECLINE));
    }
    let file_name = &input.file[input.file.rfind('/').map_or(0, |slash| slash + 1)..];
    let name = file_name.strip_suffix(".tla").unwrap_or(file_name);
    if mule.name == name {
        return Ok(Loaded::Module(mule));
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
    Ok(Loaded::Module(Mule {
        name: name.to_owned(),
        ..mule
    }))
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

/// Adds a module `load_mule` read, or holds the conversion error it read unordered, which a
/// second declines.
fn add_loaded(
    loaded: Loaded,
    modules: &mut OrderedMap<String, Rc<Mule>>,
    named: &mut Vec<String>,
    is_important: bool,
    unordered: &RefCell<Option<ObligationError>>,
) -> Result<Option<Rc<Mule>>> {
    match loaded {
        Loaded::Module(module) => {
            let module = Rc::new(Mule {
                is_important: is_important || module.is_important,
                ..module
            });
            modules.insert(module.name.clone(), module.clone());
            Ok(Some(module))
        }
        Loaded::Unconverted {
            error,
            dependencies,
        } => {
            if unordered.borrow().is_some() {
                return Err(ObligationError::not_native(ORDER_DECLINE));
            }
            *unordered.borrow_mut() = Some(error);
            named.extend(dependencies);
            Ok(None)
        }
    }
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
    // A source conversion error tlapm may raise as it parses its module or later, with the
    // modules the module names, which this goes on loading, to find whether anything else tlapm
    // reads errs or warns: it reports it unless something does, whose order it doesn't know.
    let unordered: RefCell<Option<ObligationError>> = RefCell::new(None);
    let is_held = std::cell::Cell::new(false);
    let mut forward = |warning: ObligationWarning| {
        if unordered.borrow().is_some() {
            is_held.set(true);
        } else {
            on_warning(warning);
        }
    };
    let decline = || ObligationError::not_native(ORDER_DECLINE);
    let mut named: Vec<String> = Vec::new();
    // An error tlapm raises as it reads a module, which comes first unless an unordered one is
    // held.
    let check = |error: ObligationError, unordered: &RefCell<Option<ObligationError>>| {
        if unordered.borrow().is_some() {
            decline()
        } else {
            error
        }
    };
    for main in mains {
        let loaded = load_mule(main, &counter, true, &mut forward, "File \"<unknown>\":\n")
            .map_err(|error| check(error, &unordered))?;
        add_loaded(loaded, &mut modules, &mut named, true, &unordered)?;
    }
    // Module.Save.complete_load: breadth first from every known module, by name.
    let mut queue: Vec<Rc<Mule>> = modules.values().cloned().collect();
    queue.sort_by(|left, right| compare_names(&left.name, &right.name));
    // A missing module is fine only if some loaded module declares it as a submodule.
    let mut requested: OrderedMap<String, Option<Locus>> = OrderedMap::new();
    let mut found = HashSet::new();
    let mut index = 0;
    while index < queue.len() || !named.is_empty() {
        // The modules a module that failed to convert names, read as its dependencies.
        let (dependencies, locations) = if index < queue.len() {
            let module = &queue[index];
            let result = get_dependencies(module);
            index += 1;
            for (name, submodule) in &result.submodules {
                found.insert(name.clone());
                if !modules.contains_key(name) {
                    modules.insert(name.clone(), Rc::new(submodule.clone()));
                }
            }
            (result.dependencies, result.locations)
        } else {
            (std::mem::take(&mut named), Vec::new())
        };
        let get_location = |name: &str| {
            locations
                .iter()
                .find(|entry| entry.0 == name)
                .and_then(|entry| entry.1.clone())
        };
        // A file named like a standard module replaces it, and is read again for each module citing it.
        for name in &dependencies {
            if modules.contains_key(name) && !standard_names.contains(name) {
                continue;
            }
            let Some(input) = load_module(name) else {
                if !modules.contains_key(name) && !requested.contains_key(name) {
                    requested.insert(name.clone(), get_location(name));
                }
                continue;
            };
            let loaded = load_mule(
                &input,
                &counter,
                false,
                &mut forward,
                &get_at_prefix(get_location(name).as_ref()),
            )
            .map_err(|error| check(error, &unordered))?;
            if let Some(loaded) = add_loaded(loaded, &mut modules, &mut named, false, &unordered)? {
                queue.push(loaded);
            }
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
        return Err(check(
            ObligationError::proof_failure(
                format!("Unknown module {}", quote_json(name)),
                "Module.Parser.load_module",
            ),
            &unordered,
        ));
    }
    if let Some(error) = unordered.take() {
        return Err(if is_held.get() { decline() } else { error });
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

    // tlapm recurses until its stack overflows on an INSTANCE that instantiates, inside a LET or
    // a DEFINE, a module whose instantiation it is in.
    #[test]
    fn fails_an_instance_inside_its_own_instantiation_as_a_stack_overflow() {
        let sources = [
            "---- MODULE M ----\n---- MODULE Inner ----\nTHEOREM LET I == INSTANCE Inner IN TRUE\n====\nTHEOREM TRUE\n====\n",
            "---- MODULE M ----\n---- MODULE P ----\nTHEOREM LET I == INSTANCE Q IN TRUE\n====\n---- MODULE Q ----\nTHEOREM LET J == INSTANCE P IN TRUE\n====\nTHEOREM TRUE\n====\n",
            "---- MODULE M ----\nTHEOREM LET I == INSTANCE M IN TRUE\n====\n",
            "---- MODULE M ----\n---- MODULE Inner ----\nTHEOREM LET I == INSTANCE Inner IN TRUE\n====\nJ == INSTANCE Inner\nTHEOREM TRUE\n====\n",
        ];
        for source in sources {
            let result = run("M.tla", source, &[], None);
            assert_eq!(
                result.results.err(),
                Some(ObligationError::bug("Stack overflow")),
                "{source}"
            );
        }
    }

    fn get_error(source: &str) -> Option<ObligationError> {
        run("M.tla", source, &[], None).results.err()
    }

    // alexer.mll:105-113: tlapm's lexer writes a \b, \o or \h numeral in decimal, wrapping one past
    // max_int into the negative ints, so every later stage sees the decimal.
    #[test]
    fn reads_based_numerals_in_decimal() {
        assert_eq!(
            get_texts(
                "THEOREM \\h1F + \\o17 + \\b101 + \\h0000000000000000000000001 = \\h4000000000000000 OBVIOUS"
            ),
            ["31 + 15 + 5 + 1 = -4611686018427387904\n"]
        );
        assert_eq!(
            get_texts("THEOREM \\hABCDEF = 11259375 OBVIOUS"),
            ["11259375 = 11259375\n"]
        );
        // \b only takes binary digits, so \b102 is \b10 and 2.
        assert_eq!(
            get_error("---- MODULE M ----\nTHEOREM \\b102 = 2 OBVIOUS\n===="),
            run(
                "M.tla",
                "---- MODULE M ----\nTHEOREM 2 2 = 2 OBVIOUS\n====",
                &[],
                None
            )
            .results
            .err()
        );
    }

    // alexer.mll:93, 105-113: int_of_string's Failure ends tlapm's run where its parser reads the
    // numeral or step number (tlapm_lib.ml:645-668), before the obligations, a later parse error, a
    // TAB or a later module.
    #[test]
    fn fails_on_an_int_past_ocamls_ints() {
        let failure = Some(ObligationError::proof("int_of_string"));
        for source in [
            "---- MODULE M ----\nTHEOREM \\h8000000000000000 = 1 OBVIOUS\n====\n",
            "---- MODULE M ----\nTHEOREM \\b1000000000000000000000000000000000000000000000000000000000000000 = 1\n====\n",
            "---- MODULE M ----\nTHEOREM \\o1000000000000000000000 = 1\n====\n",
            "---- MODULE M ----\nTHEOREM TRUE\n<4611686018427387904>1. TRUE\n<4611686018427387904>2. QED\n====\n",
            "---- MODULE M ----\nTHEOREM TRUE\n<1>1. TRUE\n<1>2. QED BY <99999999999999999999>1\n====\n",
            // In a pragma, which tlapm's lexer reads as tokens.
            "---- MODULE M ----\nTHEOREM TRUE OBVIOUS (*{ by (zenon \\hFFFFFFFFFFFFFFFFF) }*)\n====\n",
            // Before a parse error, and before a TAB.
            "---- MODULE M ----\nX == \\h8000000000000000\nY == == 1\n====\n",
            "---- MODULE M ----\nX == \\h8000000000000000\nY ==\t1\n====\n",
            // In a submodule.
            "---- MODULE M ----\n---- MODULE Inner ----\nX == \\h8000000000000000\n====\n====\n",
            // Before a comment the module doesn't close, an expression's next line, or a parse
            // error after it.
            "---- MODULE M ----\nX == \\h8000000000000000\n(* \n====\n",
            "---- MODULE M ----\nX == 1 +\n\\h8000000000000000\n====\n",
            "---- MODULE M ----\nTHEOREM TRUE\n<1>1. QED BY (<99999999999999999999>1\n====\n",
            "---- MODULE M ----\nTHEOREM TRUE\n<1>1. QED BY <99999999999999999999>1 ==\n====\n",
            "---- MODULE M ----\nTHEOREM TRUE\n<18446744073709551616>1. QED OBVIOUS\n====\n",
        ] {
            assert_eq!(get_error(source), failure, "{source}");
        }
        // In a module M extends, which tlapm reads after M parses.
        let result = run(
            "M.tla",
            "---- MODULE M ----\nEXTENDS Lib\nTHEOREM TRUE\n====\n",
            &[(
                "Lib",
                "---- MODULE Lib ----\nX == \\hFFFFFFFFFFFFFFFFF\n====\n",
            )],
            None,
        );
        assert_eq!(result.results.err(), failure);
    }

    // Where the lexer never reads: in a comment, a string, a line comment, past the module's end,
    // past a TAB, or as an uppercase \H, which tlapm's lexer doesn't take for a numeral.
    #[test]
    fn reads_no_int_where_tlapms_lexer_does_not() {
        for (body, after) in [
            ("(* \\h8000000000000000 *)", ""),
            ("X == \"a\\\\h8000000000000000\"", ""),
            ("\\* <99999999999999999999>", ""),
            ("", "\n\\h8000000000000000"),
        ] {
            let source = format!("---- MODULE M ----\n{body}\nTHEOREM TRUE OBVIOUS\n===={after}\n");
            assert_eq!(get_error(&source), None, "{source}");
        }
        assert_eq!(
            get_error("---- MODULE M ----\nX == \\H8000000000000000\n====\n"),
            get_error("---- MODULE M ----\nX == \\ H8000000000000000\n====\n")
        );
        let tab = run(
            "M.tla",
            "---- MODULE M ----\nX ==\t\\h8000000000000000\n====\n",
            &[],
            None,
        );
        assert!(!matches!(
            tab.results,
            Err(ObligationError::Proof { ref message, .. }) if message == "int_of_string"
        ));
    }

    fn get_parse_failure() -> Option<ObligationError> {
        Some(ObligationError::proof_failure(
            "Could not parse \"M.tla\" successfully.",
            "Module.Parser.parse_file",
        ))
    }

    // pco.ml:573-592: the parser reads one token at a time, so a parse error well before the
    // numeral comes first; one that its parser may have read ahead from is declined
    // (`may_read_ahead`).
    #[test]
    fn reports_a_parse_error_before_an_int_failure_unless_it_may_read_ahead() {
        for source in [
            "---- MODULE M ----\nY == == 1\nX == \\h8000000000000000\n====\n".to_owned(),
            format!(
                "---- MODULE M ----\nY == == 1\n{}X == \\h8000000000000000\n====\n",
                "Z == 1\n".repeat(50)
            ),
            "---- MODULE M ----\nTHEOREM 1 = = 1\nTHEOREM \\h8000000000000000 = 1\n====\n"
                .to_owned(),
        ] {
            assert_eq!(get_error(&source), get_parse_failure(), "{source}");
        }
        for source in [
            "---- MODULE M ----\nX == == \\h8000000000000000\n====\n",
            "---- MODULE M ----\nX == 1 + + LET A == 1 B == 2 IN \\h8000000000000000\n====\n",
            "---- MODULE M ----\nTHEOREM TRUE\n<1>1. TRUE = =\n<1> DEFINE A == 1 B == 2\n<1>2. QED BY \\h8000000000000000\n====\n",
        ] {
            assert_eq!(
                get_error(source),
                Some(ObligationError::not_native(INT_DECLINE)),
                "{source}"
            );
        }
    }

    // proof/p_parser.ml:102-140, 172-216: a subproof's level is currlv + 1, which wraps from
    // max_int to min_int. A leaf proof never reads it, so only a step at max_int whose proof
    // has steps, or takes the steps that follow it, is declined; tla-front, whose levels don't
    // wrap, may fail to parse one, which is declined too, after any parse error before it.
    #[test]
    fn declines_a_step_level_that_wraps_around_where_tlapm_reads_it() {
        let decline = Some(ObligationError::not_native(LEVEL_DECLINE));
        assert_eq!(
            get_error(
                "---- MODULE M ----\nTHEOREM TRUE\n<4611686018427387903>1. TRUE\n  <4611686018427387903>2. QED OBVIOUS\n<4611686018427387903>2. QED OBVIOUS\n====\n"
            ),
            decline
        );
        assert_eq!(
            get_error(
                "---- MODULE M ----\nTHEOREM TRUE\n<4611686018427387902>1. TRUE\n  <4611686018427387903>1. QED\n<4611686018427387902>2. QED OBVIOUS\n====\n"
            ),
            decline
        );
        // to_proof of no steps is `Omitted Implicit` (p_parser.ml:70-71): a last QED without a
        // proof never reads its subproof's level.
        assert_eq!(
            get_printed(&run(
                "M.tla",
                "---- MODULE M ----\nTHEOREM TRUE\n<4611686018427387903>1. QED\n====\n",
                &[],
                None
            ))
            .len(),
            0
        );
        assert_eq!(
            get_texts(
                "THEOREM TRUE\n<4611686018427387903>1. TRUE OBVIOUS\n<4611686018427387903>2. QED"
            ),
            ["TRUE\n"]
        );
        // tlapm wraps the level while it parses the THEOREM, before it reads a numeral after it,
        // whether tla-front parses the proof or not.
        for proof in [
            "<4611686018427387903>1. TRUE\n<4611686018427387903>2. QED OBVIOUS",
            "<4611686018427387903>1. TRUE\n<5>1. QED OBVIOUS\n<4611686018427387903>2. QED OBVIOUS",
        ] {
            for after in ["", "\nX == \\h8000000000000000"] {
                assert_eq!(
                    get_error(&format!(
                        "---- MODULE M ----\nTHEOREM TRUE\n{proof}{after}\n====\n"
                    )),
                    decline,
                    "{proof}{after}"
                );
            }
        }
        // A numeral before the step fails first.
        assert_eq!(
            get_error(
                "---- MODULE M ----\nX == \\h8000000000000000\nTHEOREM TRUE\n<4611686018427387903>1. TRUE\n<4611686018427387903>2. QED OBVIOUS\n====\n"
            ),
            Some(ObligationError::proof("int_of_string"))
        );
        assert_eq!(
            get_texts("THEOREM TRUE\n<4611686018427387903>1. QED OBVIOUS"),
            ["TRUE\n"]
        );
        assert_eq!(
            get_texts(
                "THEOREM TRUE\n<4611686018427387903>1. TRUE OBVIOUS\n<4611686018427387903>2. QED OBVIOUS"
            ),
            ["TRUE\n", "TRUE\n"]
        );
        assert_eq!(
            get_error(
                "---- MODULE M ----\nY == == 1\nTHEOREM TRUE\n<4611686018427387903>1. QED OBVIOUS\n====\n"
            ),
            get_parse_failure()
        );
    }

    fn get_loaded_error(main: &str, modules: &[(&str, &str)]) -> Option<ObligationError> {
        run("M.tla", main, modules, None).results.err()
    }

    fn get_selected(selector: &str) -> Option<ObligationError> {
        get_error(&format!(
            "---- MODULE M ----\nEXTENDS Naturals\nF(a) == a + 1\nTHEOREM F(2)!{selector} = 3 OBVIOUS\n====\n"
        ))
    }

    // tla_parser.ml:193-196, e_parser.ml:476: tlapm reads a selector's number with `nat`, an
    // OCaml int; tla-front reads an f64, exact below 2^53, where Prove It follows tlapm and past
    // which it declines.
    #[test]
    fn reads_a_selectors_number_below_2_pow_53() {
        // deref_num asserts n > 0 (e_deref.ml:213).
        assert_eq!(get_selected("0"), Some(ObligationError::assert_failure()));
        // "Cannot resolve !%d" prints the int (e_deref.ml:137-138).
        assert_eq!(
            get_selected("9007199254740991"),
            Some(ObligationError::proof_failure(
                "Cannot resolve !9007199254740991",
                "Expr.Deref.deref_num"
            ))
        );
        for selector in [
            "9007199254740992",
            "99999999999999999999",
            "\\h4000000000000000",
            "\\h7FFFFFFFFFFFFFFF",
        ] {
            assert_eq!(
                get_selected(selector),
                Some(ObligationError::not_native(SELECTOR_DECLINE)),
                "{selector}"
            );
        }
        // A DEF clause's `!` and EXCEPT's take no selector: tla-front's parse error stands.
        for body in [
            "USE DEF F!99999999999999999999",
            "THEOREM TRUE BY DEF F!99999999999999999999",
            "THEOREM TRUE BY DEF \\cdot!99999999999999999999",
            "f == [x \\in {1} |-> x]\nX == [f EXCEPT !99999999999999999999 = 1]",
        ] {
            assert_eq!(
                get_error(&format!("---- MODULE M ----\nF == 1\n{body}\n====\n")),
                get_parse_failure(),
                "{body}"
            );
        }
    }

    // tlapm parses each module as complete_load reads it (module/m_save.ml:203-250), before its
    // visitors meet an extended module's tuple declaration (m_dep.ml:19-58, e_visit.ml:570-576),
    // so a selector Prove It declines is declined before the tuple declaration's Failure, in
    // the same module or another.
    #[test]
    fn declines_a_selector_before_a_tuple_declaration() {
        let main = "---- MODULE M ----\nEXTENDS N\nTHEOREM TRUE OBVIOUS\n====\n";
        for module in [
            "---- MODULE N ----\nP == \\A <<a, b>> \\in {} : a\nF(x) == x\nQ == F!99999999999999999999\n====\n",
            "---- MODULE N ----\nF(x) == x\nP == \\A <<a, b>> \\in {F!99999999999999999999} : a\n====\n",
        ] {
            assert_eq!(
                get_loaded_error(main, &[("N", module)]),
                Some(ObligationError::not_native(SELECTOR_DECLINE)),
                "{module}"
            );
        }
        let main = "---- MODULE M ----\nEXTENDS N, O\nTHEOREM TRUE OBVIOUS\n====\n";
        assert_eq!(
            get_loaded_error(
                main,
                &[
                    (
                        "N",
                        "---- MODULE N ----\nP == {<<a, b>> \\in {} : TRUE}\n====\n"
                    ),
                    (
                        "O",
                        "---- MODULE O ----\nF(x) == x\nQ == F!99999999999999999999\n====\n"
                    ),
                ]
            ),
            Some(ObligationError::not_native(ORDER_DECLINE))
        );
    }

    // A source conversion error tlapm may raise as it parses or later is reported where nothing
    // else tlapm reads errs, and declined where something does, whose order is unknown.
    #[test]
    fn declines_a_conversion_error_beside_another_modules_error() {
        let main = "---- MODULE M ----\nEXTENDS N\nTHEOREM TRUE BY MODULE N\n====\n";
        assert_eq!(
            get_loaded_error(main, &[("N", "---- MODULE N ----\nX == 1\n====\n")]),
            Some(ObligationError::unsupported(
                "MODULE facts in proof obligations are not supported"
            ))
        );
        for module in [
            "---- MODULE N ----\nX == == 1\n====\n",
            "---- MODULE N ----\nX == \\h8000000000000000\n====\n",
        ] {
            assert_eq!(
                get_loaded_error(main, &[("N", module)]),
                Some(ObligationError::not_native(ORDER_DECLINE)),
                "{module}"
            );
        }
    }

    // Instantiating the same module twice, one after the other, is no recursion.
    #[test]
    fn instantiates_a_module_again_after_its_instantiation() {
        let result = run(
            "M.tla",
            "---- MODULE M ----\n---- MODULE Inner ----\nX == TRUE\n====\nTHEOREM LET I == INSTANCE Inner IN I!X\nOBVIOUS\nTHEOREM LET J == INSTANCE Inner IN J!X\nOBVIOUS\n====\n",
            &[],
            None,
        );
        let counts = result
            .results
            .expect("obligations")
            .iter()
            .map(|module| module.obligations.len())
            .collect::<Vec<_>>();
        assert_eq!(counts, [0, 2]);
    }

    // An INSTANCE of a module inside a substitute for its parameter expands once, as tlapm does.
    #[test]
    fn instantiates_a_module_inside_a_substitute_for_its_own_parameter() {
        let cases = [
            (
                "LET I == INSTANCE Inner WITH c <- (LET J == INSTANCE Inner WITH c <- TRUE IN J!X) IN I!X",
                "LET I!X == LET J!X == TRUE\n           IN  J!X\nIN  I!X\n",
            ),
            (
                "LET I == INSTANCE Inner WITH c <- (LET J == INSTANCE Inner WITH c <- (LET K == INSTANCE Inner WITH c <- TRUE IN K!X) IN J!X) IN I!X",
                "LET I!X == LET J!X == LET K!X == TRUE\n                      IN  K!X\n           IN  J!X\nIN  I!X\n",
            ),
            (
                "LET I(d) == INSTANCE Inner WITH c <- d IN I((LET J == INSTANCE Inner WITH c <- TRUE IN J!X))!X",
                "LET I!X(d) == d\nIN  I!X(LET J!X == TRUE\n        IN  J!X)\n",
            ),
        ];
        for (theorem, expected) in cases {
            let source = format!(
                "---- MODULE M ----\n---- MODULE Inner ----\nCONSTANT c\nX == c\n====\nTHEOREM {theorem}\nOBVIOUS\n====\n"
            );
            let result = run("M.tla", &source, &[], None);
            let texts = result
                .results
                .expect("obligations")
                .into_iter()
                .flat_map(|module| module.obligations)
                .map(|obligation| obligation.text)
                .collect::<Vec<_>>();
            assert_eq!(texts, [expected], "{theorem}");
        }
    }
}
