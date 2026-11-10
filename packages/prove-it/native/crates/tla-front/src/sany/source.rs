//! A port of `src/sany/source.ts`: the tokens of one file, to find the locations SANY gives to
//! names, brackets and parentheses that the syntax tree leaves out, and the comments SANY attaches
//! to definitions.
//!
//! The TypeScript offsets count UTF-16 code units; those here are byte offsets of the same
//! characters, found as the TypeScript finds them, so the texts sliced at them are the same.

use std::rc::Rc;

use crate::TlcVersion;
use crate::ast::{Expression, Module, Position, SourceRange};
use crate::errors::SyntaxError;
use crate::hash::FastMap;
use crate::lexer::{Token, TokenKind, read_at_as_identifier, tokenize};
use crate::parser::parse_sany_module;
use crate::sany::nodes::{Name, SanyLocation};
use crate::sany_parse_error::get_sany_parse_error;

/// `SourceFile`. `line_offsets` holds the offset of each line, from line 1 at index 1.
#[derive(Clone, Debug)]
pub struct SourceFile {
    pub name: Name,
    pub source: String,
    pub tokens: Vec<Token>,
    pub line_offsets: Vec<usize>,
    token_indexes: FastMap<(u32, u32), usize>,
}

const OPENERS: [(&str, &str); 4] = [("(", ")"), ("[", "]"), ("{", "}"), ("<<", ">>")];

/// `createSourceFile`, given the tokens of `source`.
pub fn create_source_file(name: Name, source: &str, tokens: &[Token]) -> SourceFile {
    let tokens: Vec<Token> = tokens
        .iter()
        .filter(|token| token.kind != TokenKind::End)
        .cloned()
        .map(read_at_as_identifier)
        .collect();
    let line_offsets = [0, 0]
        .into_iter()
        .chain(source.match_indices('\n').map(|(index, _)| index + 1))
        .collect();
    let token_indexes = tokens
        .iter()
        .enumerate()
        .map(|(index, token)| ((token.line, token.column), index))
        .collect();
    SourceFile {
        name,
        source: source.to_owned(),
        tokens,
        line_offsets,
        token_indexes,
    }
}

/// `isToken`.
pub fn is_token(file: &SourceFile, index: usize, text: &str) -> bool {
    file.tokens
        .get(index)
        .is_some_and(|token| &*token.text == text && token.kind != TokenKind::String)
}

/// `countTokensBefore`: the number of tokens, in source order, before a position, or at or before
/// it when `is_at_counted`.
fn count_tokens_before(file: &SourceFile, position: Position, is_at_counted: bool) -> usize {
    file.tokens.partition_point(|token| {
        token.line < position.line
            || (token.line == position.line
                && if is_at_counted {
                    token.column <= position.column
                } else {
                    token.column < position.column
                })
    })
}

/// `getTokenIndex`: the index of the first token at or after a position.
pub fn get_token_index(file: &SourceFile, position: Position) -> usize {
    file.token_indexes
        .get(&(position.line, position.column))
        .copied()
        .unwrap_or_else(|| {
            count_tokens_before(file, position, false).min(file.tokens.len().saturating_sub(1))
        })
}

/// `getEndTokenIndex`: the index of the last token at or before a position.
fn get_end_token_index(file: &SourceFile, position: Position) -> usize {
    count_tokens_before(file, position, true).saturating_sub(1)
}

/// `getMatchingIndex`.
pub fn get_matching_index(file: &SourceFile, open_index: usize) -> usize {
    let opener = &*file.tokens[open_index].text;
    let Some(&(_, closer)) = OPENERS.iter().find(|entry| entry.0 == opener) else {
        return open_index;
    };
    let mut depth = 0;
    for index in open_index..file.tokens.len() {
        if is_token(file, index, opener) {
            depth += 1;
        } else if is_token(file, index, closer) {
            depth -= 1;
            if depth == 0 {
                return index;
            }
        }
    }
    open_index
}

/// `TokenSpan`: the indexes of a span's first and last tokens.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TokenSpan {
    pub start: usize,
    pub end: usize,
}

/// `getRangeSpan`.
pub fn get_range_span(file: &SourceFile, range: &SourceRange) -> TokenSpan {
    TokenSpan {
        start: get_token_index(file, range.start),
        end: get_end_token_index(file, range.end),
    }
}

/// `getExpressionSpan`: the tokens of an expression. Some nodes, such as a tuple in a subscript,
/// have no range, so their span runs from their first token to the bracket that closes it.
pub fn get_expression_span(file: &SourceFile, expression: &Expression) -> TokenSpan {
    if let Some(range) = &expression.location.range {
        return get_range_span(file, range);
    }
    let start = get_token_index(file, expression.location.position());
    TokenSpan {
        start,
        end: get_matching_index(file, start),
    }
}

/// `getParenthesizedSpan`: the span with the parentheses around it, as SANY locates a
/// parenthesized operand by its parentheses.
pub fn get_parenthesized_span(file: &SourceFile, span: TokenSpan) -> TokenSpan {
    let Some(start) = span.start.checked_sub(1) else {
        return span;
    };
    let end = span.end + 1;
    if is_token(file, start, "(")
        && is_token(file, end, ")")
        && get_matching_index(file, start) == end
    {
        return get_parenthesized_span(file, TokenSpan { start, end });
    }
    span
}

/// `getArgumentSpan`: SANY's parser keeps the parentheses around an argument of an operator, which
/// the span of the argument's expression leaves out. Those of the operator's own arguments follow
/// its name.
pub fn get_argument_span(file: &SourceFile, span: TokenSpan) -> TokenSpan {
    let Some(start) = span.start.checked_sub(1) else {
        return span;
    };
    let end = span.end + 1;
    let is_parenthesized = is_token(file, start, "(")
        && get_matching_index(file, start) == end
        && start
            .checked_sub(1)
            .is_some_and(|before| is_token(file, before, "(") || is_token(file, before, ","));
    if is_parenthesized {
        get_argument_span(file, TokenSpan { start, end })
    } else {
        span
    }
}

/// `getSpanLocation`.
pub fn get_span_location(file: &SourceFile, span: TokenSpan) -> SanyLocation {
    SanyLocation {
        file: file.name.clone(),
        begin_line: file.tokens[span.start].line,
        begin_column: file.tokens[span.start].column,
        end_line: file.tokens[span.end].line,
        end_column: file.tokens[span.end].end_column,
    }
}

/// `getTokenLocation`.
pub fn get_token_location(file: &SourceFile, index: usize) -> SanyLocation {
    get_span_location(
        file,
        TokenSpan {
            start: index,
            end: index,
        },
    )
}

/// `getTabStop` of `src/sany/lexer.ts`.
fn get_tab_stop(column: u32) -> u32 {
    column + 8 - column % 8
}

/// `getOffset`: the offset of the character at a line and column, with tabs stopping at
/// multiples of 8.
fn get_offset(file: &SourceFile, line: u32, column: u32) -> usize {
    let start = file.line_offsets[line as usize];
    let mut width = 0;
    for (index, character) in file.source[start..].char_indices() {
        width = if character == '\t' {
            get_tab_stop(width)
        } else {
            width + character.len_utf16() as u32
        };
        if width >= column {
            return start + index;
        }
    }
    file.source.len()
}

/// `getOffset(...) + 1`: the offset after the character at a line and column.
fn get_offset_after(file: &SourceFile, line: u32, column: u32) -> usize {
    let offset = get_offset(file, line, column);
    offset
        + file.source[offset..]
            .chars()
            .next()
            .map_or(0, char::len_utf8)
}

/// `getTokenSource`: the token as the source spells it, where the token's text is the name of the
/// operator.
pub fn get_token_source(file: &SourceFile, index: usize) -> &str {
    let token = &file.tokens[index];
    let start = get_offset(file, token.line, token.column);
    &file.source[start..get_offset_after(file, token.line, token.end_column)]
}

/// `isBoxToken`: SANY lexes []ASSUME and []PROVE as single tokens.
pub fn is_box_token(file: &SourceFile, index: usize) -> bool {
    let (Some(token), Some(next)) = (file.tokens.get(index), file.tokens.get(index + 1)) else {
        return false;
    };
    token.kind == TokenKind::Operator
        && &*token.text == "[]"
        && next.kind == TokenKind::Keyword
        && matches!(&*next.text, "ASSUME" | "PROVE")
        && next.line == token.line
        && next.column == token.end_column + 1
}

/// `getUnboxedSource`. HACK: the parser has no []ASSUME or []PROVE, so it parses the source with
/// the two UTF-16 code units at each such [] blanked out, which keeps every other token where it
/// was. SANY's parser takes them only in an ASSUME/PROVE, which unboxing hides. Such a [] comes
/// right before its keyword, so a source that never spells one has nothing to blank out.
pub fn get_unboxed_source(source: &str) -> Result<String, SyntaxError> {
    let is_spelled = ["[]ASSUME", "[]PROVE", "□ASSUME", "□PROVE"]
        .iter()
        .any(|spelling| source.contains(spelling));
    if !is_spelled {
        return Ok(source.to_owned());
    }
    let file = create_source_file(Rc::from(""), source, &tokenize(source)?);
    let mut unboxed = String::with_capacity(source.len());
    let mut copied = 0;
    for (index, token) in file.tokens.iter().enumerate() {
        if !is_box_token(&file, index) {
            continue;
        }
        let offset = get_offset(&file, token.line, token.column);
        let mut units = 0;
        let end = source[offset..]
            .char_indices()
            .find_map(|(position, character)| {
                units += character.len_utf16();
                (units >= 2).then(|| offset + position + character.len_utf8())
            })
            .unwrap_or(source.len());
        unboxed.push_str(&source[copied..offset]);
        unboxed.push_str("  ");
        copied = end;
    }
    unboxed.push_str(&source[copied..]);
    if unboxed != source && get_sany_parse_error(source, TlcVersion::Master).is_some() {
        return Err(SyntaxError::new(
            "SANY rejects a []ASSUME or []PROVE outside an ASSUME/PROVE",
        ));
    }
    Ok(unboxed)
}

/// `SanyReading`: what SANY's parser reads from a module's text: the text's tokens and its module,
/// or the syntax error that stops the parser. `is_unboxed` tells whether the parser read the text
/// without the boxes of []ASSUME and []PROVE, so the module is not the one of the text's tokens.
#[derive(Debug)]
pub struct SanyReading {
    pub tokens: Vec<Token>,
    pub module: Result<Rc<Module>, SyntaxError>,
    pub is_unboxed: bool,
}

/// The readings of the texts a run reads, by text.
pub type SanyReadings = FastMap<String, Rc<SanyReading>>;

/// `readSanyText`: each text is read once. The parser reports a syntax error by returning it, and
/// every reader of the text gets it.
pub fn read_sany_text(readings: &mut SanyReadings, text: &str) -> Rc<SanyReading> {
    if let Some(known) = readings.get(text) {
        return known.clone();
    }
    let read = || -> Result<SanyReading, SyntaxError> {
        let tokens = tokenize(text)?;
        let unboxed = get_unboxed_source(text)?;
        let is_unboxed = unboxed != text;
        let module = parse_sany_module(
            &unboxed,
            (!is_unboxed).then_some(&tokens[..]),
            TlcVersion::Master,
        )?;
        Ok(SanyReading {
            tokens,
            module: Ok(Rc::new(module)),
            is_unboxed,
        })
    };
    let reading = Rc::new(read().unwrap_or_else(|error| SanyReading {
        tokens: Vec::new(),
        module: Err(error),
        is_unboxed: false,
    }));
    readings.insert(text.to_owned(), reading.clone());
    reading
}

/// `getPreComments`: the comments between a token and the one before it, which SANY's parser
/// attaches to the token.
pub fn get_pre_comments(file: &SourceFile, index: usize) -> Vec<String> {
    let token = &file.tokens[index];
    let start = index.checked_sub(1).map_or(0, |previous| {
        let previous = &file.tokens[previous];
        get_offset_after(file, previous.line, previous.end_column)
    });
    let end = get_offset(file, token.line, token.column);
    let gap = file.source.get(start..end).unwrap_or("");
    let mut comments = Vec::new();
    let mut offset = 0;
    let next = |offset: usize| offset + gap[offset..].chars().next().map_or(1, char::len_utf8);
    while offset < gap.len() {
        if gap[offset..].starts_with("\\*") {
            let end = gap[offset..]
                .find('\n')
                .map_or(gap.len(), |line_end| offset + line_end + 1);
            comments.push(gap[offset..end].to_owned());
            offset = end;
        } else if gap[offset..].starts_with("(*") {
            // SANY's lexer ends a comment token at each (* and *) nested in a block comment.
            let mut depth = 1;
            let mut segment_start = offset;
            let mut end = offset + 2;
            while depth > 0 && end < gap.len() {
                let is_open = gap[end..].starts_with("(*");
                if is_open || gap[end..].starts_with("*)") {
                    depth += if is_open { 1 } else { -1 };
                    end += 2;
                    comments.push(gap[segment_start..end].to_owned());
                    segment_start = end;
                } else {
                    end = next(end);
                }
            }
            if segment_start < end {
                comments.push(gap[segment_start..end].to_owned());
            }
            offset = end;
        } else {
            offset = next(offset);
        }
    }
    comments
}

/// `findNameTokens`: the indexes of the identifiers `names`, in order, from `start` to before
/// `end`.
pub fn find_name_tokens(file: &SourceFile, start: usize, end: usize, names: &[Name]) -> Vec<usize> {
    let mut found = Vec::new();
    for (index, token) in file.tokens.iter().enumerate().take(end).skip(start) {
        if found.len() == names.len() {
            break;
        }
        if token.kind == TokenKind::Identifier && token.text == names[found.len()] {
            found.push(index);
        }
    }
    found
}

/// `findToken`, whose -1 is `None`: the first token `text` from `start` to `end`.
pub fn find_token(file: &SourceFile, start: usize, end: usize, text: &str) -> Option<usize> {
    (start..=end).find(|&index| is_token(file, index, text))
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use super::{
        SanyReadings, create_source_file, get_pre_comments, get_token_source, get_unboxed_source,
        read_sany_text,
    };
    use crate::lexer::tokenize;

    // The expected values are what `src/sany/source.ts` gives for the same texts.

    #[test]
    fn pre_comments_split_nested_comments_as_sany_does() {
        let text = "---- MODULE M ----\n(* a (* nested *) comment *)\n\\* line één\nx == 1 \\* trailing\n\t(* tab\té *) y == 2\n(* 𝔸 two (* deep (* er *) *) out *)\nz == x ⊕ y\n====\n";
        let file = create_source_file(Rc::from("M"), text, &tokenize(text).unwrap());
        let found: Vec<(usize, Vec<String>)> = (0..file.tokens.len())
            .map(|index| (index, get_pre_comments(&file, index)))
            .filter(|(_, comments)| !comments.is_empty())
            .collect();
        let expected: Vec<(usize, Vec<&str>)> = vec![
            (
                4,
                vec!["(* a (*", " nested *)", " comment *)", "\\* line één\n"],
            ),
            (7, vec!["\\* trailing\n", "(* tab\té *)"]),
            (
                10,
                vec!["(* 𝔸 two (*", " deep (*", " er *)", " *)", " out *)"],
            ),
        ];
        assert_eq!(
            found,
            expected
                .into_iter()
                .map(|(index, comments)| (index, comments.into_iter().map(String::from).collect()))
                .collect::<Vec<_>>()
        );
        assert_eq!(&*file.tokens[13].text, "\\oplus");
        assert_eq!(get_token_source(&file, 13), "⊕");
    }

    #[test]
    fn unboxes_a_boxed_assume() {
        let text = "---- MODULE M ----\nTHEOREM T == ASSUME NEW x, []ASSUME TRUE PROVE TRUE PROVE TRUE\n====\n";
        assert_eq!(
            get_unboxed_source(text).unwrap(),
            "---- MODULE M ----\nTHEOREM T == ASSUME NEW x,   ASSUME TRUE PROVE TRUE PROVE TRUE\n====\n"
        );
        let reading = read_sany_text(&mut SanyReadings::default(), text);
        assert!(reading.is_unboxed);
        assert!(reading.module.is_ok());
    }

    #[test]
    fn blanks_two_code_units_of_a_box_symbol() {
        // The [] of □ASSUME is one code unit, so the blanking takes the A of ASSUME too.
        let text = "---- MODULE M ----\nTHEOREM T == ASSUME NEW x, □ASSUME TRUE PROVE TRUE PROVE TRUE\n====\n";
        assert_eq!(
            get_unboxed_source(text).unwrap_err().message,
            "SANY rejects a []ASSUME or []PROVE outside an ASSUME/PROVE"
        );
        let reading = read_sany_text(&mut SanyReadings::default(), text);
        assert!(!reading.is_unboxed);
        assert!(reading.module.is_err());
    }
}
