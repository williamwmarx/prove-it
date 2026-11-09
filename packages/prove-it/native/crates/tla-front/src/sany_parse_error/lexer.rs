//! An emulation of the token manager that JavaCC generates for SANY's grammar, javacc/tla+.jj, as
//! `src/sany/lexer.ts` emulates it: the tokens it produces, their kinds in TLAplusParserConstants
//! order, and their positions. It reads the source a UTF-16 code unit at a time, as Java does.

use std::collections::{HashMap, HashSet};
use std::sync::OnceLock;

pub struct Token {
    pub kind: usize,
    pub image: String,
    pub begin_line: i64,
    pub begin_column: i64,
    pub next: Option<usize>,
}

const INFIX_1: &[&str] = &[
    "\\approx",
    "\\asymp",
    "\\bigcirc",
    "\\bullet",
    "\\cap",
    "\\cdot",
    "\\circ",
    "\\cong",
    "\\cup",
    "\\div",
    "\\doteq",
    "\\equiv",
    "\\geq",
    "\\gg",
];

const INFIX_2: &[&str] = &[
    "\\intersect",
    "\\union",
    "\\land",
    "\\leq",
    "\\ll",
    "\\lor",
    "\\o",
    "\\odot",
    "\\ominus",
    "\\oplus",
    "\\oslash",
    "\\otimes",
    "\\prec",
    "\\preceq",
    "\\propto",
    "\\sim",
    "\\simeq",
    "\\sqcap",
    "\\sqcup",
    "\\sqsubset",
    "\\sqsupset",
    "\\sqsubseteq",
    "\\sqsupseteq",
    "\\star",
    "\\subset",
    "\\subseteq",
    "\\succ",
    "\\succeq",
    "\\supset",
    "\\supseteq",
    "\\uplus",
    "\\wr",
    "\\",
    "~>",
    "=>",
    "=<",
    "=|",
];

const INFIX_3: &[&str] = &["##", "#", "^^", "^", "--", "-|", "-+->"];

const INFIX_4: &[&str] = &[
    "**", "*", "++", "+", "<=>", "<:", "<=", "<", ">=", ">", "...", "..", "||", "|", "|-", "|=",
    "&&", "&", "$$", "$", "??", "%%", "%", "@@", "!!", ":>", ":=", "::=", "(+)", "(-)", "(.)",
    "(/)", "(\\X)", "\\notin",
];

const INFIX_SYMBOLS: &str = "≈≔≍◯⩴●∩⋅∘≅∪÷≐‥…≡‼≥≫⇔⇒⫤↝≤≪⊣≠∉⊙⊖⊕⊘⊗⇸≺⪯∝⁇⊨⊢∼≃⊓⊔⊏⊑⊐⊒⋆⊂⊆≻⪰⊃⊇×⊎‖≀";

/// The token kinds before the infix operators, each with the literal images that produce it.
const KINDS_HEAD: &[(&str, &[&str])] = &[
    ("EOF", &[]),
    ("BEGIN_PRAGMA", &["--->"]),
    ("_BM1", &[]),
    ("NUMBER", &[]),
    ("_BM2", &[]),
    ("_BM0", &[]),
    ("SEPARATOR", &[]),
    ("END_MODULE", &[]),
    ("ACTION", &["ACTION", "ACTIONS"]),
    ("ASSUME", &["ASSUME"]),
    ("BOXASSUME", &["[]ASSUME"]),
    ("ASSUMPTION", &["ASSUMPTION", "AXIOM"]),
    ("CASE", &["CASE"]),
    ("CHOOSE", &["CHOOSE"]),
    ("CONSTANT", &["CONSTANT", "CONSTANTS"]),
    ("ELSE", &["ELSE"]),
    ("EXCEPT", &["EXCEPT"]),
    ("EXISTS", &["\\E", "\\exists", "∃"]),
    ("EXTENDS", &["EXTENDS"]),
    ("FORALL", &["\\A", "\\forall", "∀"]),
    ("IF", &["IF"]),
    ("INSTANCE", &["INSTANCE"]),
    ("LET", &["LET"]),
    ("LETIN", &["IN"]),
    ("LOCAL", &["LOCAL"]),
    ("MODULE", &["MODULE"]),
    ("NEW", &["NEW"]),
    ("OTHER", &["OTHER"]),
    ("PROPOSITION", &["PROPOSITION", "LEMMA", "COROLLARY"]),
    ("SF", &["SF_"]),
    ("T_EXISTS", &["\\EE"]),
    ("T_FORALL", &["\\AA"]),
    ("THEN", &["THEN"]),
    ("BY", &["BY"]),
    ("ONLY", &["ONLY"]),
    ("DEFINE", &["DEFINE"]),
    ("DF", &["DEF", "DEFS"]),
    ("THEOREM", &["THEOREM"]),
    ("USE", &["USE"]),
    ("HIDE", &["HIDE"]),
    ("HAVE", &["HAVE"]),
    ("OBVIOUS", &["OBVIOUS"]),
    ("OMITTED", &["OMITTED"]),
    ("LAMBDA", &["LAMBDA"]),
    ("TAKE", &["TAKE"]),
    ("PROOF", &["PROOF"]),
    ("PROVE", &["PROVE"]),
    ("BOXPROVE", &["[]PROVE"]),
    ("QED", &["QED"]),
    ("RECURSIVE", &["RECURSIVE"]),
    ("STATE", &["STATE"]),
    ("TEMPORAL", &["TEMPORAL", "TEMPORALS"]),
    ("PICK", &["PICK"]),
    ("WITNESS", &["WITNESS"]),
    ("SUFFICES", &["SUFFICES"]),
    ("VARIABLE", &["VARIABLE", "VARIABLES"]),
    ("WF", &["WF_"]),
    ("WITH", &["WITH"]),
    ("COMMA", &[","]),
    ("COLON", &[":"]),
    ("COLONCOLON", &["::", "∷"]),
    ("DOT", &["."]),
    ("US", &["_"]),
    ("DEF", &["==", "≜"]),
    ("LBR", &["("]),
    ("RBR", &[")"]),
    ("DEFBREAK", &["-|-"]),
    ("LSB", &["["]),
    ("ARSB", &["]_"]),
    ("RSB", &["]"]),
    ("LBC", &["{"]),
    ("RBC", &["}"]),
    ("LAB", &["<<", "⟨"]),
    ("ARAB", &[">>_", "⟩_"]),
    ("RAB", &[">>", "⟩"]),
    ("BANG", &["!"]),
    ("ARROW", &["->", "→"]),
    ("SUBSTITUTE", &["<-", "←"]),
    ("MAPTO", &["|->", "↦"]),
    ("NUMBER_LITERAL", &[]),
    ("STRING_LITERAL", &[]),
    ("BAND", &[]),
    ("BOR", &[]),
    ("op_57", &["'"]),
    ("op_68", &["^+", "⁺"]),
    ("op_69", &["^*"]),
    ("op_70", &["^#"]),
    ("op_76", &["-."]),
    ("op_26", &["\\lnot", "¬"]),
    ("op_29", &["\\neg"]),
    ("op_58", &["~"]),
    ("CASESEP", &["[]", "□"]),
    ("op_61", &["<>", "◇"]),
    ("op_112", &["ENABLED"]),
    ("op_113", &["UNCHANGED"]),
    ("op_114", &["SUBSET"]),
    ("op_115", &["UNION"]),
    ("op_116", &["DOMAIN"]),
    ("op_1", &["//"]),
    ("AND", &["/\\", "∧"]),
    ("op_3", &["/="]),
    ("op_4", &["/"]),
    ("OR", &["\\/", "∨"]),
];

const KINDS_TAIL: &[&str] = &[
    "op_119",
    "IDENTIFIER",
    "ProofStepLexeme",
    "ProofImplicitStepLexeme",
    "ProofStepDotLexeme",
    "BareLevelLexeme",
    "UnnumberedStepLexeme",
];

struct Tables {
    names: Vec<&'static str>,
    indexes: HashMap<&'static str, usize>,
    literals: HashMap<Vec<u16>, usize>,
    longest_literal: usize,
    literal_prefixes: HashSet<Vec<u16>>,
}

/// The token kinds, in the order of TLAplusParserConstants, each with the literal images that
/// produce it. JavaCC breaks a tie between matches of the same length by this order.
fn get_tables() -> &'static Tables {
    static TABLES: OnceLock<Tables> = OnceLock::new();
    TABLES.get_or_init(|| {
        let mut kinds: Vec<(&'static str, Vec<String>)> = KINDS_HEAD
            .iter()
            .map(|(name, images)| {
                (
                    *name,
                    images.iter().map(|image| image.to_string()).collect(),
                )
            })
            .collect();
        let infix = |images: &[&str]| -> Vec<(&'static str, Vec<String>)> {
            images
                .iter()
                .map(|image| ("infix", vec![image.to_string()]))
                .collect()
        };
        kinds.extend(infix(INFIX_1));
        kinds.push(("IN", vec!["\\in".to_owned(), "∈".to_owned()]));
        kinds.extend(infix(INFIX_2));
        kinds.push(("EQUALS", vec!["=".to_owned()]));
        kinds.extend(infix(INFIX_3));
        kinds.push(("op_77", vec!["-".to_owned()]));
        kinds.extend(infix(INFIX_4));
        kinds.extend(
            INFIX_SYMBOLS
                .chars()
                .map(|symbol| ("infix", vec![symbol.to_string()])),
        );
        kinds.push(("infix", vec!["\\times".to_owned()]));
        kinds.push(("op_119", vec!["\\X".to_owned()]));
        kinds.extend(KINDS_TAIL[1..].iter().map(|name| (*name, Vec::new())));
        let names: Vec<&'static str> = kinds.iter().map(|kind| kind.0).collect();
        let mut indexes = HashMap::new();
        for (kind, name) in names.iter().enumerate().rev() {
            indexes.insert(*name, kind);
        }
        let mut literals = HashMap::new();
        for (kind, (_, images)) in kinds.iter().enumerate() {
            for image in images {
                literals.insert(image.encode_utf16().collect::<Vec<u16>>(), kind);
            }
        }
        let longest_literal = literals.keys().map(Vec::len).max().unwrap_or(0);
        let literal_prefixes = literals
            .keys()
            .flat_map(|image| (1..image.len()).map(|length| image[..length].to_vec()))
            .collect();
        Tables {
            names,
            indexes,
            literals,
            longest_literal,
            literal_prefixes,
        }
    })
}

/// The kind of a name. The anonymous infix operators share the name "infix", which no caller
/// looks up.
pub fn get_kind(name: &str) -> usize {
    get_tables().indexes[name]
}

pub fn get_kind_name(kind: usize) -> &'static str {
    get_tables().names[kind]
}

pub const KIND_COUNT: usize = 265;

fn unit(source: &[u16], offset: usize) -> Option<u16> {
    source.get(offset).copied()
}

fn is_unit(source: &[u16], offset: usize, test: impl Fn(u8) -> bool) -> bool {
    unit(source, offset).is_some_and(|unit| unit < 0x80 && test(unit as u8))
}

fn is_word(source: &[u16], offset: usize) -> bool {
    is_unit(source, offset, |byte| {
        byte.is_ascii_alphanumeric() || byte == b'_'
    })
}

fn count_while(source: &[u16], offset: usize, test: impl Fn(&[u16], usize) -> bool) -> usize {
    let mut end = offset;
    while test(source, end) {
        end += 1;
    }
    end - offset
}

fn starts_with(source: &[u16], offset: usize, text: &str) -> bool {
    let units: Vec<u16> = text.encode_utf16().collect();
    source
        .get(offset..)
        .is_some_and(|rest| rest.starts_with(&units))
}

type Pattern = fn(&[u16], usize) -> usize;

/// `----+ *MODULE`.
fn begin_module(source: &[u16], offset: usize) -> usize {
    let dashes = count_while(source, offset, |source, at| unit(source, at) == Some(0x2d));
    if dashes < 4 {
        return 0;
    }
    let spaces = count_while(source, offset + dashes, |source, at| {
        unit(source, at) == Some(0x20)
    });
    if starts_with(source, offset + dashes + spaces, "MODULE") {
        dashes + spaces + 6
    } else {
        0
    }
}

fn repeated(source: &[u16], offset: usize, character: u16) -> usize {
    let count = count_while(source, offset, |source, at| {
        unit(source, at) == Some(character)
    });
    if count >= 4 { count } else { 0 }
}

fn separator(source: &[u16], offset: usize) -> usize {
    repeated(source, offset, u16::from(b'-'))
}

fn end_module(source: &[u16], offset: usize) -> usize {
    repeated(source, offset, u16::from(b'='))
}

/// `[0-9]+|\\[oO][0-7]+|\\[bB][01]+|\\[hH][0-9a-fA-F]+`.
fn number_literal(source: &[u16], offset: usize) -> usize {
    let digits = count_while(source, offset, |source, at| {
        is_unit(source, at, |byte| byte.is_ascii_digit())
    });
    if digits > 0 {
        return digits;
    }
    if unit(source, offset) != Some(u16::from(b'\\')) {
        return 0;
    }
    let test: fn(u8) -> bool = match unit(source, offset + 1).map(|unit| unit as u8 as char) {
        Some('o' | 'O') => |byte| (b'0'..=b'7').contains(&byte),
        Some('b' | 'B') => |byte| byte == b'0' || byte == b'1',
        Some('h' | 'H') => |byte| byte.is_ascii_hexdigit(),
        _ => return 0,
    };
    if unit(source, offset + 1).is_some_and(|unit| unit >= 0x80) {
        return 0;
    }
    let count = count_while(source, offset + 2, |source, at| is_unit(source, at, test));
    if count > 0 { count + 2 } else { 0 }
}

/// The length of `"(?:[^"\n\r\\]|\\[ntrf\\"])*` at offset, and whether a backslash that starts
/// no escape follows it.
fn scan_string(source: &[u16], offset: usize) -> Option<(usize, bool)> {
    if unit(source, offset) != Some(u16::from(b'"')) {
        return None;
    }
    let mut at = offset + 1;
    loop {
        match unit(source, at) {
            Some(0x5c) => {
                if is_unit(source, at + 1, |byte| b"ntrf\\\"".contains(&byte)) {
                    at += 2;
                } else {
                    return Some((at - offset, true));
                }
            }
            Some(0x22 | 0x0a | 0x0d) | None => return Some((at - offset, false)),
            Some(_) => at += 1,
        }
    }
}

/// `"(?:[^"\n\r\\]|\\[ntrf\\"])*"`.
fn string_literal(source: &[u16], offset: usize) -> usize {
    match scan_string(source, offset) {
        Some((length, false)) if unit(source, offset + length) == Some(0x22) => length + 1,
        _ => 0,
    }
}

/// `"(?:[^"\n\r\\]|\\[ntrf\\"])*\\?`: the characters of a string literal that a string literal
/// could still continue.
fn string_prefix(source: &[u16], offset: usize) -> usize {
    match scan_string(source, offset) {
        Some((length, has_backslash)) => length + usize::from(has_backslash),
        None => 0,
    }
}

fn alphanumeric_run(source: &[u16], offset: usize) -> usize {
    count_while(source, offset, |source, at| {
        is_unit(source, at, |byte| byte.is_ascii_alphanumeric())
    })
}

/// A junction after `[0-9][A-Za-z0-9]*`, `[WS][a-zA-EG-Z0-9][A-Za-z0-9]*` or
/// `[a-zA-RT-VX-Z][A-Za-z0-9]*`, the longest of the three.
fn junction(source: &[u16], offset: usize, junction: &str) -> usize {
    let with_junction = |length: usize| {
        if starts_with(source, offset + length, junction) {
            length + junction.len()
        } else {
            0
        }
    };
    let first = unit(source, offset)
        .filter(|unit| *unit < 0x80)
        .map(|unit| unit as u8);
    let mut best = 0;
    if first.is_some_and(|byte| byte.is_ascii_digit()) {
        best = best.max(with_junction(1 + alphanumeric_run(source, offset + 1)));
    }
    if matches!(first, Some(b'W' | b'S'))
        && is_unit(source, offset + 1, |byte| {
            byte.is_ascii_alphanumeric() && byte != b'F'
        })
    {
        best = best.max(with_junction(2 + alphanumeric_run(source, offset + 2)));
    }
    if first.is_some_and(|byte| byte.is_ascii_alphabetic() && byte != b'S' && byte != b'W') {
        best = best.max(with_junction(1 + alphanumeric_run(source, offset + 1)));
    }
    best
}

/// A conjunction bullet glued to the word before it: `./\`.
fn band(source: &[u16], offset: usize) -> usize {
    junction(source, offset, "./\\")
}

/// A disjunction bullet glued to the word before it: `.\/`.
fn bor(source: &[u16], offset: usize) -> usize {
    junction(source, offset, ".\\/")
}

fn word_run(source: &[u16], offset: usize) -> usize {
    count_while(source, offset, is_word)
}

/// The identifier patterns, the longest of them.
fn identifier(source: &[u16], offset: usize) -> usize {
    let Some(first) = unit(source, offset) else {
        return 0;
    };
    if [0x40, 0x2115, 0x2124, 0x211d].contains(&first) {
        return 1;
    }
    if first >= 0x80 {
        return 0;
    }
    let first = first as u8;
    let run = word_run(source, offset + 1);
    let has_letter = (offset + 1..offset + 1 + run)
        .any(|at| is_unit(source, at, |byte| byte.is_ascii_alphabetic()));
    let mut best = 0;
    // `_\w*[A-Za-z]\w*` and `[0-9]\w*[A-Za-z]\w*`.
    if (first == b'_' || first.is_ascii_digit()) && has_letter {
        best = best.max(1 + run);
    }
    if first == b'W' || first == b'S' {
        // `[WS](?:[a-zA-EG-Z_0-9]\w*)?`.
        let is_continued = is_unit(source, offset + 1, |byte| {
            (byte.is_ascii_alphanumeric() || byte == b'_') && byte != b'F'
        });
        best = best.max(if is_continued { 1 + run } else { 1 });
        // `[WS]F(?:[A-Za-z0-9]\w*)?`.
        if unit(source, offset + 1) == Some(u16::from(b'F')) {
            let is_continued = is_unit(source, offset + 2, |byte| byte.is_ascii_alphanumeric());
            best = best.max(if is_continued {
                2 + word_run(source, offset + 2)
            } else {
                2
            });
        }
    }
    // `[a-zA-RT-VX-Z]\w*`.
    if first.is_ascii_alphabetic() && first != b'S' && first != b'W' {
        best = best.max(1 + run);
    }
    best
}

/// `<(?:[0-9]+|\+|\*)>`.
fn step(source: &[u16], offset: usize) -> usize {
    if unit(source, offset) != Some(u16::from(b'<')) {
        return 0;
    }
    let digits = count_while(source, offset + 1, |source, at| {
        is_unit(source, at, |byte| byte.is_ascii_digit())
    });
    let inner = if digits > 0 {
        digits
    } else if is_unit(source, offset + 1, |byte| byte == b'+' || byte == b'*') {
        1
    } else {
        return 0;
    };
    if unit(source, offset + 1 + inner) == Some(u16::from(b'>')) {
        inner + 2
    } else {
        0
    }
}

/// `<[0-9]+>\w+`.
fn proof_step(source: &[u16], offset: usize) -> usize {
    let length = step(source, offset);
    if length < 3 || !is_unit(source, offset + 1, |byte| byte.is_ascii_digit()) {
        return 0;
    }
    let run = word_run(source, offset + length);
    if run > 0 { length + run } else { 0 }
}

/// `<[+*]>[A-Za-z0-9]+`.
fn proof_implicit_step(source: &[u16], offset: usize) -> usize {
    let length = step(source, offset);
    if length != 3 || !is_unit(source, offset + 1, |byte| byte == b'+' || byte == b'*') {
        return 0;
    }
    let run = alphanumeric_run(source, offset + 3);
    if run > 0 { 3 + run } else { 0 }
}

fn dots(source: &[u16], offset: usize) -> usize {
    count_while(source, offset, |source, at| {
        unit(source, at) == Some(u16::from(b'.'))
    })
}

/// `<step>\w+\.+`.
fn proof_step_dot(source: &[u16], offset: usize) -> usize {
    let length = step(source, offset);
    if length == 0 {
        return 0;
    }
    let run = word_run(source, offset + length);
    let dot_count = dots(source, offset + length + run);
    if run > 0 && dot_count > 0 {
        length + run + dot_count
    } else {
        0
    }
}

/// `<step>(?:\*\.*|-\.*|\.+)`.
fn unnumbered_step(source: &[u16], offset: usize) -> usize {
    let length = step(source, offset);
    if length == 0 {
        return 0;
    }
    let at = offset + length;
    match unit(source, at) {
        Some(0x2a | 0x2d) => length + 1 + dots(source, at + 1),
        _ => {
            let dot_count = dots(source, at);
            if dot_count > 0 { length + dot_count } else { 0 }
        }
    }
}

fn pragma_number(source: &[u16], offset: usize) -> usize {
    count_while(source, offset, |source, at| {
        is_unit(source, at, |byte| byte.is_ascii_digit())
    })
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    Default,
    Pragma,
    Spec,
}

fn get_patterns(mode: Mode) -> Vec<(usize, Vec<Pattern>)> {
    let named = |name: &str, patterns: Vec<Pattern>| (get_kind(name), patterns);
    match mode {
        Mode::Spec => vec![
            named("_BM0", vec![begin_module]),
            named("SEPARATOR", vec![separator]),
            named("END_MODULE", vec![end_module]),
            named("NUMBER_LITERAL", vec![number_literal]),
            named("STRING_LITERAL", vec![string_literal]),
            named("BAND", vec![band]),
            named("BOR", vec![bor]),
            named("IDENTIFIER", vec![identifier]),
            named("ProofStepLexeme", vec![proof_step]),
            named("ProofImplicitStepLexeme", vec![proof_implicit_step]),
            named("ProofStepDotLexeme", vec![proof_step_dot]),
            named("BareLevelLexeme", vec![step]),
            named("UnnumberedStepLexeme", vec![unnumbered_step]),
        ],
        Mode::Default => vec![
            named(
                "BEGIN_PRAGMA",
                vec![|source, offset| {
                    if starts_with(source, offset, "--->") {
                        4
                    } else {
                        0
                    }
                }],
            ),
            named("_BM1", vec![begin_module]),
        ],
        Mode::Pragma => vec![
            named("NUMBER", vec![pragma_number]),
            named("_BM2", vec![begin_module]),
            named("BAND", vec![band]),
            named("BOR", vec![bor]),
            named("IDENTIFIER", vec![identifier]),
        ],
    }
}

/// The longest match at offset, the earliest kind among matches of that length.
fn match_patterns(
    patterns: &[(usize, Vec<Pattern>)],
    source: &[u16],
    offset: usize,
) -> (usize, usize) {
    let mut best: (Option<usize>, usize) = (None, 0);
    for (kind, regexes) in patterns {
        let length = regexes
            .iter()
            .map(|pattern| pattern(source, offset))
            .max()
            .unwrap_or(0);
        if length > best.1 || (length == best.1 && best.0.is_some_and(|best| *kind < best)) {
            best = (Some(*kind), length);
        }
    }
    (best.0.unwrap_or(usize::MAX), best.1)
}

fn slice_units(source: &[u16], start: usize, end: usize) -> &[u16] {
    let end = end.min(source.len());
    &source[start.min(end)..end]
}

/// SimpleCharStream.UpdateLineColumn: the line and column of each code unit, with tabs stopping
/// at multiples of 8.
fn get_positions(source: &str) -> (Vec<i64>, Vec<i64>) {
    let mut lines = Vec::new();
    let mut columns = Vec::new();
    let (mut line, mut column, mut is_after_cr, mut is_after_lf) = (1i64, 0i64, false, false);
    for character in source.chars() {
        for _ in 0..character.len_utf16() {
            column += 1;
            if is_after_lf {
                is_after_lf = false;
                line += 1;
                column = 1;
            } else if is_after_cr {
                is_after_cr = false;
                if character == '\n' {
                    is_after_lf = true;
                } else {
                    line += 1;
                    column = 1;
                }
            }
            match character {
                '\r' => is_after_cr = true,
                '\n' => is_after_lf = true,
                '\t' => column = get_tab_stop(column - 1),
                _ => {}
            }
            lines.push(line);
            columns.push(column);
        }
    }
    (lines, columns)
}

pub fn get_tab_stop(column: i64) -> i64 {
    column + 8 - column.rem_euclid(8)
}

/// JavaCC's TokenMgrError.addEscapes, a UTF-16 code unit at a time, so that it escapes a lone
/// surrogate as Java does.
fn escape_units(units: &[u16]) -> String {
    let mut escaped = String::new();
    for unit in units {
        match unit {
            0 => {}
            0x08 => escaped.push_str("\\b"),
            0x09 => escaped.push_str("\\t"),
            0x0a => escaped.push_str("\\n"),
            0x0c => escaped.push_str("\\f"),
            0x0d => escaped.push_str("\\r"),
            0x22 => escaped.push_str("\\\""),
            0x27 => escaped.push_str("\\'"),
            0x5c => escaped.push_str("\\\\"),
            0x01..=0x1f | 0x7f.. => escaped.push_str(&format!("\\u{unit:04x}")),
            _ => escaped.push(char::from(*unit as u8)),
        }
    }
    escaped
}

/// TokenMgrError.LexicalError: the character the lexer stopped at, or the end of the file, and
/// the characters of the token it had read.
pub fn format_lexical_error(
    line: i64,
    column: i64,
    character: Option<u16>,
    after: &[u16],
) -> String {
    let encountered = match character {
        None => "<EOF> ".to_owned(),
        Some(unit) => format!("\"{}\" ({unit}), ", escape_units(&[unit])),
    };
    format!(
        "Lexical error at line {line}, column {column}.  Encountered: {encountered}after : \"{}\"",
        escape_units(after)
    )
}

/// A lazy token stream over a source, which returns SANY's message for the TokenMgrError
/// JavaCC's token manager throws at a character no token continues with, or at the end of the
/// file in a comment.
pub struct Lexer {
    source: Vec<u16>,
    lines: Vec<i64>,
    columns: Vec<i64>,
    offset: usize,
    mode: Mode,
    patterns: [Vec<(usize, Vec<Pattern>)>; 3],
}

impl Lexer {
    pub fn new(source: &str) -> Lexer {
        let (lines, columns) = get_positions(source);
        Lexer {
            source: source.encode_utf16().collect(),
            lines,
            columns,
            offset: 0,
            mode: Mode::Default,
            patterns: [
                get_patterns(Mode::Default),
                get_patterns(Mode::Pragma),
                get_patterns(Mode::Spec),
            ],
        }
    }

    fn create_token(&self, kind: usize, start: usize, length: usize) -> Token {
        Token {
            kind,
            image: String::from_utf16_lossy(slice_units(&self.source, start, start + length)),
            begin_line: self.lines.get(start).copied().unwrap_or(0),
            begin_column: self.columns.get(start).copied().unwrap_or(0),
            next: None,
        }
    }

    /// JavaCC places the end of the file at the file's last character.
    fn get_end_of_file(&self) -> Token {
        match self.source.len().checked_sub(1) {
            Some(last) => self.create_token(get_kind("EOF"), last, 0),
            None => Token {
                kind: get_kind("EOF"),
                image: String::new(),
                begin_line: 0,
                begin_column: 0,
                next: None,
            },
        }
    }

    /// The lexer read the characters from start to end, and TLAplusParser.parse reports the end
    /// of the file in a token that starts on an earlier line as an open comment.
    fn get_lexical_error(&self, start: usize, end: usize, after: &[u16]) -> String {
        let index = end - 1;
        let line = self.lines[index];
        let column = self.columns[index];
        if end < self.source.len() {
            return format_lexical_error(line, column, Some(self.source[index]), after);
        }
        if self.lines[start] != line {
            return format!(
                "Lexical {{error: EOF reached, possibly open comment starting around line {}",
                self.lines[start]
            );
        }
        if self.source[index] == 0x0a || self.source[index] == 0x0d {
            format_lexical_error(line + 1, 0, None, after)
        } else {
            format_lexical_error(line, column + 1, None, after)
        }
    }

    /// A comment is a chain of MORE matches, which restarts after each nested comment bracket,
    /// and the end of the file right after a bracket ends the token stream.
    fn skip_comment(&mut self) -> Option<String> {
        let source = &self.source;
        let start = self.offset;
        if starts_with(source, start, "\\*") {
            let end = source[start..]
                .iter()
                .position(|unit| *unit == 0x0a || *unit == 0x0d);
            let Some(end) = end else {
                return Some(self.get_lexical_error(start, source.len(), &[]));
            };
            self.offset += end + 1;
            return None;
        }
        let mut depth = 0;
        let mut chain_start = start;
        let mut offset = start;
        while offset < source.len() {
            if starts_with(source, offset, "(*") {
                depth += 1;
                offset += 2;
                if depth > 1 {
                    chain_start = offset;
                }
            } else if starts_with(source, offset, "*)") {
                depth -= 1;
                offset += 2;
                chain_start = offset;
                if depth == 0 {
                    self.offset = offset;
                    return None;
                }
            } else {
                offset += 1;
            }
        }
        self.offset = offset;
        if chain_start == self.source.len() {
            None
        } else {
            Some(self.get_lexical_error(chain_start, offset, &[]))
        }
    }

    fn get_skipping_token(&mut self, mode: usize) -> Token {
        while self.offset < self.source.len() {
            let (kind, length) = match_patterns(&self.patterns[mode], &self.source, self.offset);
            if length > 0 {
                let token = self.create_token(kind, self.offset, length);
                self.offset += length;
                let name = get_kind_name(kind);
                if name.starts_with("_BM") {
                    self.mode = Mode::Spec;
                }
                if name == "BEGIN_PRAGMA" {
                    self.mode = Mode::Pragma;
                }
                return token;
            }
            self.offset += 1;
        }
        self.get_end_of_file()
    }

    /// The longest literal or pattern at offset, the earliest kind among those of that length.
    fn match_spec_token(&self, offset: usize) -> (usize, usize) {
        let tables = get_tables();
        let source = &self.source;
        // A slice past the end of the source is cut short, as JavaScript's slice is.
        let literal_length = (1..=tables.longest_literal).rev().find(|length| {
            tables
                .literals
                .contains_key(slice_units(source, offset, offset + length))
        });
        let pattern = match_patterns(&self.patterns[2], source, offset);
        let Some(literal_length) = literal_length else {
            return pattern;
        };
        let literal = (
            tables.literals[slice_units(source, offset, offset + literal_length)],
            literal_length,
        );
        if literal.1 > pattern.1 || (literal.1 == pattern.1 && literal.0 < pattern.0) {
            literal
        } else {
            pattern
        }
    }

    /// The characters JavaCC's token manager reads at offset while some token could still
    /// continue.
    fn get_token_prefix(&self, offset: usize) -> usize {
        let tables = get_tables();
        let mut length = 0;
        while offset + length < self.source.len()
            && tables.literal_prefixes.contains(slice_units(
                &self.source,
                offset,
                offset + length + 1,
            ))
        {
            length += 1;
        }
        length.max(string_prefix(&self.source, offset))
    }

    pub fn next_token(&mut self) -> Result<Token, String> {
        match self.mode {
            Mode::Default => return Ok(self.get_skipping_token(0)),
            Mode::Pragma => return Ok(self.get_skipping_token(1)),
            Mode::Spec => {}
        }
        while self.offset < self.source.len() {
            let offset = self.offset;
            let current = self.source[offset];
            if [0x20, 0x09, 0x0a, 0x0d].contains(&current) {
                self.offset += 1;
            } else if starts_with(&self.source, offset, "(*")
                || starts_with(&self.source, offset, "\\*")
            {
                if let Some(error) = self.skip_comment() {
                    return Err(error);
                }
            } else {
                let (kind, length) = self.match_spec_token(offset);
                if length == 0 {
                    // JavaCC reads on while a token could continue, and one more character.
                    let prefix_length = self.get_token_prefix(offset);
                    let end = (offset + prefix_length + 1).min(self.source.len());
                    let read = slice_units(&self.source, offset, end);
                    let prefix = slice_units(&self.source, offset, offset + prefix_length);
                    let after = if end < self.source.len() {
                        prefix
                    } else if read.len() > 1 {
                        read
                    } else {
                        &[]
                    };
                    return Err(self.get_lexical_error(offset, end, after));
                }
                let token = self.create_token(kind, offset, length);
                self.offset += length;
                return Ok(token);
            }
        }
        Ok(self.get_end_of_file())
    }
}

/// TLC 1.7.4's lexer, which JavaCC generated without UNICODE_INPUT, reads a character past U+00FF
/// outside a comment by its low byte, and stops at one whose low byte is below 0x80.
pub fn get_sany_174_lexical_error(source: &str) -> Option<String> {
    let mut lexer = Lexer::new(source);
    while let Ok(token) = lexer.next_token() {
        if token.kind == get_kind("EOF") {
            return None;
        }
        let units: Vec<u16> = token.image.encode_utf16().collect();
        let Some(index) = units
            .iter()
            .position(|unit| *unit > 0xff && (unit & 0xff) < 0x80)
        else {
            continue;
        };
        let column = units[1..index + 1]
            .iter()
            .fold(token.begin_column, |previous, unit| {
                if *unit == 0x09 {
                    get_tab_stop(previous)
                } else {
                    previous + 1
                }
            });
        return Some(format_lexical_error(
            token.begin_line,
            column,
            Some(units[index]),
            &units[..index],
        ));
    }
    None
}
