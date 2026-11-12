//! SANY's validation of a module's PlusCal algorithm against the checksums its translation
//! records, as `src/pcal/validate.ts` ports `pcal.Validator`: it parses and translates the
//! algorithm as the translator does, reporting its errors, and compares the checksums of the
//! algorithm's AST and of the translation with those the module records.

mod ast;
mod parse;
mod tokenize;
mod translate;

use std::collections::BTreeSet;

use ast::{Params, Position, VERSION_WEIGHT, format_algorithm, get_version_number};
use tokenize::{Reader, TokenizerState};

use crate::TlcVersion;

/// Validator.ValidationResult.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ValidationResult {
    NoPluscalExists,
    NoTranslationExists,
    NoPcalChecksumsExist,
    TlaDivergenceExists,
    PcalDivergenceExists,
    ErrorEncountered,
    NoDivergence,
}

impl ValidationResult {
    pub fn name(self) -> &'static str {
        match self {
            ValidationResult::NoPluscalExists => "NO_PLUSCAL_EXISTS",
            ValidationResult::NoTranslationExists => "NO_TRANSLATION_EXISTS",
            ValidationResult::NoPcalChecksumsExist => "NO_PCAL_CHECKSUMS_EXIST",
            ValidationResult::TlaDivergenceExists => "TLA_DIVERGENCE_EXISTS",
            ValidationResult::PcalDivergenceExists => "PCAL_DIVERGENCE_EXISTS",
            ValidationResult::ErrorEncountered => "ERROR_ENCOUNTERED",
            ValidationResult::NoDivergence => "NO_DIVERGENCE",
        }
    }
}

/// A Java exception that the validation doesn't catch, which SANY reports as a fatal error: a
/// RuntimeException with its message, or the java.lang.Error of PcalDebug.ReportBug.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PcalFatal {
    Runtime(String),
    Bug(String),
}

/// What the translator's Java throws: a PcalError, with the position of the statement it names, a
/// RuntimeException, or the Error of a bug it finds in itself.
#[derive(Debug)]
pub(crate) enum PcalError {
    Error {
        message: String,
        position: Option<Position>,
    },
    Runtime(String),
    Bug(String),
}

fn error(message: &str) -> PcalError {
    PcalError::Error {
        message: message.to_owned(),
        position: None,
    }
}

fn error_at(message: &str, position: Position) -> PcalError {
    PcalError::Error {
        message: message.to_owned(),
        position: Some(position),
    }
}

fn runtime(message: String) -> PcalError {
    PcalError::Runtime(message)
}

/// PcalDebug.ReportBug: the translator found itself in a state it considers a bug.
fn bug(message: &str) -> PcalError {
    PcalError::Bug(format!(
        "You have discovered a bug in pcal.trans.\nSend the following information and the\ninput file to the current maintainer(s).\n\n -- {message}."
    ))
}

#[derive(Debug, Default)]
struct Lookahead {
    tokens: [String; 10],
    columns: [i64; 10],
    lines: [i64; 10],
}

#[derive(Debug, Default)]
struct LastToken {
    column: i64,
    line: i64,
    text: String,
}

/// The translator's state that its Java code keeps in static fields, which SANY never resets
/// between the modules it validates: the options, the tokenizer's state, ParseAlgorithm's
/// lookahead buffer and last token, and whether a macro's parsing was cut short by an error. The
/// log holds the lines its reports print to ToolIO.out.
#[derive(Debug, Default)]
pub struct PcalSession {
    params: Params,
    tokenizer: TokenizerState,
    lookahead: Lookahead,
    last_token: LastToken,
    is_in_macro: bool,
    pub log: Vec<String>,
}

/// Java's \s.
fn is_java_space(unit: u16) -> bool {
    [0x20, 0x09, 0x0a, 0x0b, 0x0c, 0x0d].contains(&unit)
}

fn find_units(line: &[u16], text: &str) -> Option<usize> {
    let needle: Vec<u16> = text.encode_utf16().collect();
    line.windows(needle.len())
        .position(|window| window == needle)
}

fn starts_with_units(line: &[u16], start: usize, text: &str) -> bool {
    let needle: Vec<u16> = text.encode_utf16().collect();
    line.get(start..)
        .is_some_and(|rest| rest.starts_with(&needle))
}

fn get_unit(line: &[u16], index: usize) -> Option<u16> {
    line.get(index).copied()
}

/// The code points of the line from the start, as JavaScript's Array.from reads them.
fn get_chars(line: &[u16], start: usize) -> Vec<char> {
    char::decode_utf16(line.get(start..).unwrap_or(&[]).iter().copied())
        .map(|char| char.unwrap_or(char::REPLACEMENT_CHARACTER))
        .collect()
}

/// A cursor over a line, for Validator.CHECKSUM_PATTERN.
struct Matcher<'a> {
    chars: &'a [char],
    index: usize,
}

impl Matcher<'_> {
    fn peek(&self) -> Option<char> {
        self.chars.get(self.index).copied()
    }

    fn skip_spaces(&mut self) -> usize {
        let start = self.index;
        while self
            .peek()
            .is_some_and(|char| char.is_ascii() && is_java_space(char as u16))
        {
            self.index += 1;
        }
        self.index - start
    }

    fn eat(&mut self, text: &str) -> bool {
        let start = self.index;
        for expected in text.chars() {
            if self.peek() != Some(expected) {
                self.index = start;
                return false;
            }
            self.index += 1;
        }
        true
    }

    fn eat_ignoring_case(&mut self, text: &str) -> bool {
        let start = self.index;
        for expected in text.chars() {
            if !self
                .peek()
                .is_some_and(|char| char.eq_ignore_ascii_case(&expected))
            {
                self.index = start;
                return false;
            }
            self.index += 1;
        }
        true
    }

    /// `ch(ec)?ksum\(name\)`, without case.
    fn eat_checksum_name(&mut self, names: &[&str]) -> bool {
        if !self.eat_ignoring_case("ch") {
            return false;
        }
        self.eat_ignoring_case("ec");
        self.eat_ignoring_case("ksum(") && names.iter().any(|name| self.eat_ignoring_case(name))
    }

    /// `=\s*"(hex*)"` or `\\in\s*STRING`: the hex digits, or none for the latter.
    fn eat_value(&mut self) -> Option<Option<String>> {
        if self.eat("=") {
            self.skip_spaces();
            if !self.eat("\"") {
                return None;
            }
            let start = self.index;
            while self.peek().is_some_and(|char| char.is_ascii_hexdigit()) {
                self.index += 1;
            }
            let hex: String = self.chars[start..self.index].iter().collect();
            return self.eat("\"").then_some(Some(hex));
        }
        if self.eat("\\in") {
            self.skip_spaces();
            return self.eat("STRING").then_some(None);
        }
        None
    }

    /// The checksums of the algorithm and its translation, from the pattern at the cursor.
    fn match_checksums(&mut self) -> Option<(Option<String>, Option<String>)> {
        if !self.eat("\\* BEGIN TRANSLATION") || self.skip_spaces() == 0 || !self.eat("(") {
            return None;
        }
        self.skip_spaces();
        if !self.eat_checksum_name(&["pluscal)", "pcal)"]) {
            return None;
        }
        self.skip_spaces();
        let pcal = self.eat_value()?;
        self.skip_spaces();
        if !self.eat("/\\") {
            return None;
        }
        self.skip_spaces();
        if !self.eat_checksum_name(&["tla+)", "tla)"]) {
            return None;
        }
        self.skip_spaces();
        let tla = self.eat_value()?;
        self.skip_spaces();
        self.eat(")").then_some((pcal, tla))
    }
}

/// Validator.CHECKSUM_PATTERN's first match in the line: the checksums of the algorithm and its
/// translation, each none when the line declares it `\in STRING`.
fn find_checksums(line: &[char]) -> Option<(Option<String>, Option<String>)> {
    (0..line.len()).find_map(|start| {
        Matcher {
            chars: line,
            index: start,
        }
        .match_checksums()
    })
}

/// Validator.checksum: CRC32 of the string's bytes, in Long.toHexString's unpadded lowercase hex.
fn get_checksum(text: &str) -> String {
    let mut crc = 0xffff_ffffu32;
    for byte in text.bytes() {
        crc ^= u32::from(byte);
        for _ in 0..8 {
            crc = if crc & 1 == 1 {
                (crc >> 1) ^ 0xedb8_8320
            } else {
                crc >> 1
            };
        }
    }
    format!("{:x}", !crc)
}

/// trans.removeTabs: tabs reach the next multiple of 8, and every line gets a trailing space.
fn remove_tabs(lines: &[&str]) -> Vec<Vec<u16>> {
    lines
        .iter()
        .map(|line| {
            let mut result: Vec<u16> = Vec::new();
            for char in line.chars() {
                if char == '\t' {
                    let spaces = 8 - (result.len() % 8);
                    result.extend(std::iter::repeat_n(u16::from(b' '), spaces));
                } else {
                    let mut buffer = [0; 2];
                    result.extend_from_slice(char.encode_utf16(&mut buffer));
                }
            }
            result.push(u16::from(b' '));
            result
        })
        .collect()
}

/// trans.findTokenPair: the first line from start with first followed by second after spaces.
fn find_token_pair(lines: &[Vec<u16>], start: i64, first: &str, second: &str) -> i64 {
    for (index, line) in lines.iter().enumerate().skip(start.max(0) as usize) {
        let Some(column) = find_units(line, first) else {
            continue;
        };
        let after_first = column + first.len();
        let spaces = line[after_first..]
            .iter()
            .position(|unit| *unit != u16::from(b' '));
        if let Some(spaces) = spaces
            && Some(after_first + spaces) == find_units(line, second)
        {
            return index as i64;
        }
    }
    -1
}

struct SearchLocation {
    line: usize,
    column: usize,
}

/// ParseAlgorithm.GotoNextNonSpace: moves the location to the next character that isn't a space,
/// returning its line, or "" past the last line.
fn goto_next_non_space<'a>(lines: &'a [Vec<u16>], location: &mut SearchLocation) -> &'a [u16] {
    while location.line < lines.len() {
        let line = &lines[location.line];
        while get_unit(line, location.column) == Some(u16::from(b' ')) {
            location.column += 1;
        }
        if location.column < line.len() {
            return line;
        }
        location.line += 1;
        location.column = 0;
    }
    &[]
}

/// ParseAlgorithm.NextSpaceCol and NextDelimiterCol: the first delimiter from column on, or the
/// end of the line. The Java counts code points but returns a string index.
fn get_next_delimiter(line: &[u16], column: usize, delimiters: &str) -> usize {
    match get_chars(line, column)
        .iter()
        .position(|char| delimiters.contains(*char))
    {
        Some(index) => column + index,
        None => line.len(),
    }
}

/// ParseAlgorithm.FindToken: moves the location past the next occurrence of token that starts a
/// word and isn't followed by a letter or "_".
fn find_token(lines: &[Vec<u16>], location: &mut SearchLocation, token: &str) -> bool {
    while location.line < lines.len() {
        let line = goto_next_non_space(lines, location);
        if starts_with_units(line, location.column, token) {
            let end = location.column + token.len();
            let is_word_char = get_unit(line, end)
                .and_then(|unit| char::from_u32(u32::from(unit)))
                .is_some_and(|char| char.is_alphabetic() || char == '_');
            if !is_word_char {
                location.column = get_next_delimiter(line, end, " ");
                return true;
            }
        }
        location.column = get_next_delimiter(line, location.column, " ");
    }
    false
}

/// Vector.get on an index out of its range, whose message names the vector's capacity: the 10 it
/// starts with, doubled as it grows.
fn index_out_of_bounds(index: i64, size: usize) -> PcalFatal {
    let mut capacity = 10;
    while capacity < size {
        capacity *= 2;
    }
    PcalFatal::Runtime(format!(
        "java.lang.ArrayIndexOutOfBoundsException: Index {index} out of bounds for length {capacity}"
    ))
}

/// ParseAlgorithm.uncomment: blanks out the comment delimiters and nested comments from the
/// algorithm's start to the "*)" that ends the comment it is in, dropping the rest of that line,
/// and returns the error it throws for a line that ends in a string.
fn uncomment(lines: &mut [Vec<u16>], start_line: usize, start_column: usize) -> Option<String> {
    let units = |text: &str| text.encode_utf16().collect::<Vec<u16>>();
    let (open, close, line_comment) = (units("(*"), units("*)"), units("\\*"));
    let (backslash, quote) = (u16::from(b'\\'), u16::from(b'"'));
    let mut depth = 0;
    let mut is_done = false;
    for (index, slot) in lines.iter_mut().enumerate().skip(start_line) {
        if is_done {
            break;
        }
        let line = &*slot;
        let start = if index == start_line { start_column } else { 0 };
        let mut output: Vec<u16> = line[..start.min(line.len())].to_vec();
        let mut is_in_string = false;
        let mut column = start;
        while !is_done && column < line.len() {
            let char = line[column];
            let pair = &line[column..(column + 2).min(line.len())];
            if pair == open && !is_in_string {
                depth += 1;
                output.extend(units("  "));
                column += 2;
                continue;
            }
            if pair == close && !is_in_string && depth == 0 {
                output.extend_from_slice(pair);
                is_done = true;
                continue;
            }
            if pair == close && !is_in_string {
                depth -= 1;
                output.extend(units("  "));
                column += 2;
                continue;
            }
            if depth > 0 {
                output.push(u16::from(b' '));
                column += 1;
                continue;
            }
            if is_in_string && char == backslash && pair.len() == 2 {
                output.extend_from_slice(pair);
                column += 2;
                continue;
            }
            if !is_in_string && pair == line_comment {
                output.push(u16::from(b' '));
                break;
            }
            if char == quote {
                is_in_string = !is_in_string;
            }
            output.push(char);
            column += 1;
        }
        if is_in_string {
            return Some(format!("Unterminated string in line {}", index + 1));
        }
        *slot = output;
    }
    None
}

impl PcalSession {
    pub fn new() -> Self {
        PcalSession::default()
    }

    fn report_unrecoverable_error(&mut self, message: &str) {
        self.log
            .push(format!("\nUnrecoverable error:\n -- {message}.\n"));
    }

    /// PcalDebug.reportError: an UnrecoverablePositionedException names its statement's
    /// position.
    fn report_error(&mut self, message: &str, position: Option<Position>) {
        match position {
            Some(position) if position.line != 0 => self
                .report_unrecoverable_error(&format!("{message}\n    at {}", position.location())),
            _ => self.report_unrecoverable_error(message),
        }
    }

    /// trans.CommandLineError, which ends the message with a period before `reportError` adds its
    /// own.
    fn report_command_line_error(&mut self, message: &str) {
        self.report_unrecoverable_error(&format!("Command-line error: {message}."));
    }

    fn set_fairness(&mut self, option: &str, is_first: &mut bool) -> bool {
        if *is_first {
            self.params.fairness_option = String::new();
            *is_first = false;
        }
        if !self.params.fairness_option.is_empty() {
            self.report_command_line_error(
                "Can only have one of -wf, -sf, -wfNext, and -nof options",
            );
            return false;
        }
        self.params.fairness_option = option.to_owned();
        true
    }

    /// trans.parseAndProcessArguments for the options of a "PlusCal options" statement, which set
    /// the translator's options for the rest of SANY's run.
    fn process_option_arguments(&mut self, args: &[String]) {
        let mut is_first = true;
        let mut is_explicit_nof = false;
        let mut index = 0;
        while index < args.len() {
            let option = args[index].as_str();
            let argument = args.get(index + 1);
            index += 1;
            match option {
                "-spec" | "spec" | "-myspec" | "myspec" => {
                    let is_myspec = option.ends_with("myspec");
                    if is_myspec {
                        self.params.myspec_option = true;
                    } else {
                        self.params.spec_option = true;
                    }
                    if self.params.spec_option && self.params.myspec_option {
                        self.report_command_line_error(
                            "\nCan have at most one of the options -spec, -myspec, -spec2, -myspec2, writeAST",
                        );
                        return;
                    }
                    if argument.is_none() {
                        let name = if is_myspec { "myspec" } else { "spec" };
                        self.report_command_line_error(&format!(
                            "Specification name must follow `-{name}' option"
                        ));
                        return;
                    }
                    index += 1;
                }
                "-termination" | "termination" => self.params.check_termination = true,
                "-noold" | "-nocfg" | "-noDoneDisjunct" | "noDoneDisjunct" => {}
                "-wf" | "wf" | "-sf" | "sf" | "-wfNext" | "wfNext" | "-nof" | "nof" => {
                    if !self.set_fairness(option.trim_start_matches('-'), &mut is_first) {
                        return;
                    }
                    if option.ends_with("nof") {
                        is_explicit_nof = true;
                    }
                }
                "-label" | "label" => self.params.label_flag = true,
                "-labelRoot" | "labelRoot" => {
                    let Some(argument) = argument else {
                        self.report_command_line_error(
                            "Label root must follow `-labelRoot' option",
                        );
                        return;
                    };
                    let mut chars = argument.chars();
                    let is_valid = chars.next().is_some_and(|char| char.is_ascii_alphabetic())
                        && chars.all(|char| char.is_ascii_alphanumeric() || char == '_');
                    if !is_valid {
                        self.report_command_line_error(
                            "Label root must be a valid PlusCal identifier (must start with a letter and contain only letters, numbers, and underscores)",
                        );
                        return;
                    }
                    self.params.label_root = argument.clone();
                    index += 1;
                }
                "-version" | "version" => {
                    let Some(argument) = argument else {
                        self.report_command_line_error(
                            "Version number must follow `-version' option",
                        );
                        return;
                    };
                    // PcalParams.ProcessVersion.
                    let version = get_version_number(argument);
                    if !(0.0..=VERSION_WEIGHT).contains(&version) {
                        let message = if version < 0.0 {
                            format!("Illegal version {argument} specified.")
                        } else {
                            format!("Specified version {argument} later than current version 1.12")
                        };
                        self.report_unrecoverable_error(&message);
                        self.report_command_line_error("Bad version number");
                        return;
                    }
                    self.params.input_version_number = version;
                    index += 1;
                }
                "-lineWidth" => {
                    // PcalTLAGen's line width only shapes the translation's text.
                    let text = argument.map_or("", String::as_str);
                    let digits = text.strip_prefix(['+', '-']).unwrap_or(text);
                    let is_integer =
                        !digits.is_empty() && digits.chars().all(|char| char.is_ascii_digit());
                    if !is_integer || text.parse::<f64>().is_ok_and(|width| width < 60.0) {
                        self.report_command_line_error(
                            "Integer value at least 60 must follow `-lineWidth' option",
                        );
                        return;
                    }
                    index += 1;
                }
                _ => {
                    self.report_command_line_error(&format!(
                        "Unknown or illegal option in options statement: {option}"
                    ));
                    return;
                }
            }
        }
        if self.params.check_termination
            && self.params.fairness_option.is_empty()
            && !is_explicit_nof
        {
            self.params.fairness_option = "wf".to_owned();
        }
    }

    /// ParseAlgorithm.ProcessOptions: the location is just past "PlusCal".
    fn process_options(&mut self, lines: &[Vec<u16>], location: &mut SearchLocation) {
        goto_next_non_space(lines, location);
        location.column += "options".len();
        let after_options = goto_next_non_space(lines, location);
        if !starts_with_units(after_options, location.column, "(") {
            self.report_unrecoverable_error("`PlusCal options' not followed by '('");
            return;
        }
        location.column += 1;
        let mut args = Vec::new();
        loop {
            let line = goto_next_non_space(lines, location);
            if location.line >= lines.len()
                || get_unit(line, location.column) == Some(u16::from(b')'))
            {
                break;
            }
            if get_unit(line, location.column) == Some(u16::from(b',')) {
                location.column += 1;
                continue;
            }
            let end = get_next_delimiter(line, location.column, " ,)");
            let slice = &line[location.column.min(line.len())..end.min(line.len())];
            args.push(String::from_utf16_lossy(slice));
            location.column = end;
        }
        if location.line >= lines.len() {
            self.report_unrecoverable_error("No closing ')' found in options statement");
            return;
        }
        self.process_option_arguments(&args);
    }

    /// Validator.validate: checks the PlusCal algorithm of the module whose lines are given, from
    /// its first to its last, against the checksums its translation records.
    pub fn validate(
        &mut self,
        specification_text: &[&str],
        version: TlcVersion,
    ) -> Result<BTreeSet<ValidationResult>, PcalFatal> {
        let only = |result| Ok(BTreeSet::from([result]));
        let has_algorithm = specification_text
            .iter()
            .any(|line| line.find("algorithm").is_some_and(|index| index > 0));
        if !has_algorithm {
            return only(ValidationResult::NoPluscalExists);
        }
        let mut lines = remove_tabs(specification_text);
        let mut search_location = SearchLocation { line: 0, column: 0 };
        while find_token(&lines, &mut search_location, "PlusCal") {
            let line = goto_next_non_space(&lines, &mut search_location);
            let rest = get_chars(line, search_location.column);
            let is_id_char = |char: &char| char.is_alphanumeric() || *char == '_';
            if rest.starts_with(&['o', 'p', 't', 'i', 'o', 'n', 's'])
                && !rest.get(7).is_some_and(is_id_char)
            {
                self.process_options(&lines, &mut search_location);
                break;
            }
        }
        let mut begin_line = 0;
        let mut begin_column = 0;
        let mut is_found = false;
        let mut is_fair = false;
        while begin_line < lines.len() {
            let line = &lines[begin_line];
            // TLAConstants.MODULE_CLOSING_REGEX, which the trailing space removeTabs adds keeps
            // from matching.
            if !line.is_empty() && line.iter().all(|unit| *unit == u16::from(b'=')) {
                break;
            }
            if let Some(column) = find_units(line, "--algorithm") {
                begin_column = column + "--algorithm".len();
                is_found = true;
                break;
            }
            if let Some(column) = find_units(line, "--fair") {
                begin_column = column + "--fair".len();
                is_found = true;
                is_fair = true;
                break;
            }
            begin_line += 1;
        }
        let mut results = BTreeSet::new();
        let translation_line = find_token_pair(&lines, 0, "BEGIN", "TRANSLATION");
        if translation_line == -1 {
            results.insert(ValidationResult::NoTranslationExists);
        }
        let end_translation_line =
            find_token_pair(&lines, translation_line + 1, "END", "TRANSLATION");
        if end_translation_line == -1 {
            results.insert(ValidationResult::NoTranslationExists);
        }
        if translation_line == -1 && end_translation_line == -1 {
            return Ok(results);
        }
        if !is_found {
            results.insert(ValidationResult::NoPluscalExists);
            return Ok(results);
        }
        if let Some(message) = uncomment(&mut lines, begin_line, begin_column) {
            self.report_error(&message, None);
            return only(ValidationResult::ErrorEncountered);
        }
        let reader_lines: Vec<Vec<char>> = lines.iter().map(|line| get_chars(line, 0)).collect();
        let vcolumn = get_chars(
            &lines[begin_line][..begin_column.min(lines[begin_line].len())],
            0,
        )
        .len();
        let reader = Reader::new(reader_lines, begin_line, begin_column, vcolumn);
        // HACK: Validator reports the exceptions of ParseAlgorithm.getAlgorithm and
        // PCalTLAGenerator and goes on to compare the checksums.
        let mut ast = None;
        let outcome = match parse::parse_algorithm(self, reader, is_fair) {
            Err(error) => Err(error),
            Ok(mut result) => {
                let outcome = translate::translate_algorithm(
                    &mut result.ast,
                    result.omit_pc,
                    result.has_default_initialization,
                    &mut self.log,
                );
                ast = Some(result.ast);
                outcome
            }
        };
        match outcome {
            Ok(()) => {}
            Err(PcalError::Error { message, position }) => self.report_error(&message, position),
            Err(PcalError::Runtime(message)) => return Err(PcalFatal::Runtime(message)),
            Err(PcalError::Bug(message)) => return Err(PcalFatal::Bug(message)),
        }
        if translation_line == -1 {
            return Err(index_out_of_bounds(-1, lines.len()));
        }
        let translation_chars = get_chars(&lines[translation_line as usize], 0);
        let Some((pcal_checksum, tla_checksum)) = find_checksums(&translation_chars) else {
            results.insert(ValidationResult::NoPcalChecksumsExist);
            return Ok(results);
        };
        // The Java checksums the string "fair" for a --fair algorithm, unlike TLC 1.7.4's, and a
        // failed parse leaves an AST whose text, Object.toString's class name and hash code,
        // matches no checksum.
        let algorithm_text = if is_fair && version != TlcVersion::V1_7_4 {
            Some("fair".to_owned())
        } else {
            ast.as_ref()
                .map(|ast| format_algorithm(ast, self.params.input_version_number, version))
        };
        if let Some(pcal_checksum) = pcal_checksum
            && algorithm_text.is_none_or(|text| pcal_checksum != get_checksum(&text))
        {
            results.insert(ValidationResult::PcalDivergenceExists);
        }
        if let Some(tla_checksum) = tla_checksum {
            if end_translation_line == -1 {
                return Err(PcalFatal::Runtime(format!(
                    "java.lang.IllegalArgumentException: fromIndex({}) > toIndex(-1)",
                    translation_line + 1
                )));
            }
            let translation = specification_text
                [(translation_line + 1) as usize..end_translation_line as usize]
                .concat();
            if tla_checksum != get_checksum(&translation) {
                results.insert(ValidationResult::TlaDivergenceExists);
            }
        }
        if results.is_empty() {
            return only(ValidationResult::NoDivergence);
        }
        Ok(results)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn checksums_like_java() {
        assert_eq!(get_checksum(""), "0");
        assert_eq!(get_checksum("123456789"), "cbf43926");
    }
}
