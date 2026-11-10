// Ported from OCaml: LGPL-2.1 with OCaml's linking exception, not MIT (THIRD_PARTY_NOTICES.md).
//! A port of OCaml's Format module, which tlapm uses to lay out obligations. Only the parts tlapm
//! reaches are ported: boxes, breaks, forced newlines and text. The Rust port of
//! `src/obligations/format.ts`.
//!
//! Numbers are `f64`, as the TypeScript's are, so a malformed directive's NaN lays out as it does
//! there. Where the TypeScript throws (a negative repeat count, an argument `format` was not given)
//! `render_doc` returns an error, and a directive missing its `>`, on which the TypeScript loops
//! forever, makes a doc that fails to render.

use crate::errors::{ObligationError, Result};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum BoxKind {
    H,
    V,
    Hv,
    Hov,
    B,
    Fits,
    /// A name `BOX_KINDS` lacks, which is `undefined` in the TypeScript.
    Unknown,
}

#[derive(Clone, Copy, Debug)]
enum Token<'doc> {
    Text(&'doc str),
    Break { width: f64, offset: f64 },
    Begin { indent: f64, box_kind: BoxKind },
    End,
    Newline,
}

#[derive(Clone, Copy, Debug)]
struct QueueElement<'doc> {
    size: f64,
    token: Token<'doc>,
    length: f64,
}

/// `element` indexes the formatter's elements, which the queue and the scan stack share.
#[derive(Clone, Copy, Debug)]
struct ScanElement {
    left_total: f64,
    element: usize,
}

#[derive(Clone, Copy, Debug)]
struct FormatElement {
    box_kind: BoxKind,
    width: f64,
}

/// The TypeScript's queue and scan stack share mutable element objects; here both hold indices
/// into `elements`, which only grows, so an element the queue has dropped can still be resized.
struct Formatter<'doc> {
    elements: Vec<QueueElement<'doc>>,
    queue: Vec<usize>,
    queue_start: usize,
    scan_stack: Vec<ScanElement>,
    format_stack: Vec<FormatElement>,
    margin: f64,
    max_indent: f64,
    space_left: f64,
    current_indent: f64,
    is_new_line: bool,
    left_total: f64,
    right_total: f64,
    depth: usize,
    output: String,
}

const INFINITY: f64 = 1_000_000_010.0;

const UNKNOWN: f64 = -1.0;

/// `Math.min`, which is NaN when either side is.
fn js_min(left: f64, right: f64) -> f64 {
    if left.is_nan() || right.is_nan() {
        return f64::NAN;
    }
    left.min(right)
}

/// `" ".repeat(count)`, which throws a RangeError on a negative or infinite count.
fn get_spaces(count: f64) -> Result<String> {
    if count.is_nan() {
        return Ok(String::new());
    }
    let whole = count.trunc();
    if whole < 0.0 || whole.is_infinite() {
        return Err(ObligationError::bug(format!(
            "RangeError: Invalid count value: {count}"
        )));
    }
    // The count is a whole, non-negative, finite number.
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    Ok(" ".repeat(whole as usize))
}

impl<'doc> Formatter<'doc> {
    fn new(max_indent: f64) -> Self {
        let system_box = QueueElement {
            size: UNKNOWN,
            token: Token::Begin {
                indent: 0.0,
                box_kind: BoxKind::Hov,
            },
            length: 0.0,
        };
        let mut formatter = Self {
            elements: vec![system_box],
            queue: vec![0],
            queue_start: 0,
            scan_stack: Vec::new(),
            format_stack: Vec::new(),
            margin: 78.0,
            max_indent,
            space_left: 78.0,
            current_indent: 0.0,
            is_new_line: true,
            left_total: 1.0,
            right_total: 1.0,
            depth: 1,
            output: String::new(),
        };
        let sentinel = formatter.get_sentinel();
        formatter.scan_stack = vec![
            sentinel,
            ScanElement {
                left_total: 1.0,
                element: 0,
            },
        ];
        formatter
    }

    fn get_sentinel(&mut self) -> ScanElement {
        self.elements.push(QueueElement {
            size: UNKNOWN,
            token: Token::Text(""),
            length: 0.0,
        });
        ScanElement {
            left_total: -1.0,
            element: self.elements.len() - 1,
        }
    }

    fn enqueue(&mut self, element: QueueElement<'doc>) -> usize {
        self.right_total += element.length;
        self.elements.push(element);
        self.queue.push(self.elements.len() - 1);
        self.elements.len() - 1
    }

    fn break_new_line(&mut self, offset: f64, width: f64) -> Result<()> {
        self.output.push('\n');
        self.is_new_line = true;
        self.current_indent = js_min(self.max_indent, self.margin - width + offset);
        self.space_left = self.margin - self.current_indent;
        self.output.push_str(&get_spaces(self.current_indent)?);
        Ok(())
    }

    fn break_same_line(&mut self, width: f64) -> Result<()> {
        self.space_left -= width;
        self.output.push_str(&get_spaces(width)?);
        Ok(())
    }

    fn force_break_line(&mut self) -> Result<()> {
        let Some(top) = self.format_stack.last().copied() else {
            self.output.push('\n');
            return Ok(());
        };
        if top.width > self.space_left
            && top.box_kind != BoxKind::Fits
            && top.box_kind != BoxKind::H
        {
            self.break_new_line(0.0, top.width)?;
        }
        Ok(())
    }

    fn format_token(&mut self, size: f64, token: Token<'doc>) -> Result<()> {
        match token {
            Token::Text(text) => {
                self.space_left -= size;
                self.output.push_str(text);
                self.is_new_line = false;
            }
            Token::Begin { indent, box_kind } => {
                if self.margin - self.space_left > self.max_indent {
                    self.force_break_line()?;
                }
                let width = self.space_left - indent;
                let box_kind = if box_kind == BoxKind::V || size > self.space_left {
                    box_kind
                } else {
                    BoxKind::Fits
                };
                self.format_stack.push(FormatElement { box_kind, width });
            }
            Token::End => {
                self.format_stack.pop();
            }
            Token::Newline => match self.format_stack.last().copied() {
                Some(top) => self.break_new_line(0.0, top.width)?,
                None => self.output.push('\n'),
            },
            Token::Break {
                width: break_width,
                offset,
            } => {
                let Some(top) = self.format_stack.last().copied() else {
                    return Ok(());
                };
                let width = top.width;
                match top.box_kind {
                    BoxKind::Hov => {
                        if size > self.space_left {
                            self.break_new_line(offset, width)?;
                        } else {
                            self.break_same_line(break_width)?;
                        }
                    }
                    BoxKind::B => {
                        if self.is_new_line {
                            self.break_same_line(break_width)?;
                        } else if size > self.space_left
                            || self.current_indent > self.margin - width + offset
                        {
                            self.break_new_line(offset, width)?;
                        } else {
                            self.break_same_line(break_width)?;
                        }
                    }
                    BoxKind::Hv | BoxKind::V => self.break_new_line(offset, width)?,
                    BoxKind::Fits | BoxKind::H => self.break_same_line(break_width)?,
                    BoxKind::Unknown => {}
                }
            }
        }
        Ok(())
    }

    fn advance_left(&mut self) -> Result<()> {
        while self.queue_start < self.queue.len() {
            let element = self.elements[self.queue[self.queue_start]];
            let is_known = element.size >= 0.0;
            if !is_known && self.right_total - self.left_total < self.space_left {
                return Ok(());
            }
            self.queue_start += 1;
            self.format_token(
                if is_known { element.size } else { INFINITY },
                element.token,
            )?;
            self.left_total += element.length;
        }
        self.queue.clear();
        self.queue_start = 0;
        Ok(())
    }

    fn enqueue_advance(&mut self, element: QueueElement<'doc>) -> Result<()> {
        self.enqueue(element);
        self.advance_left()
    }

    fn set_size(&mut self, is_break: bool) {
        let Some(top) = self.scan_stack.last().copied() else {
            return;
        };
        if top.left_total < self.left_total {
            self.scan_stack = vec![self.get_sentinel()];
            return;
        }
        let element = &mut self.elements[top.element];
        let is_kind = match element.token {
            Token::Break { .. } => is_break,
            Token::Begin { .. } => !is_break,
            _ => false,
        };
        if is_kind {
            element.size += self.right_total;
            self.scan_stack.pop();
        }
    }

    fn scan_push(&mut self, is_break: bool, element: QueueElement<'doc>) {
        let index = self.enqueue(element);
        if is_break {
            self.set_size(true);
        }
        self.scan_stack.push(ScanElement {
            left_total: self.right_total,
            element: index,
        });
    }

    fn open_box(&mut self, box_kind: BoxKind, indent: f64) {
        self.depth += 1;
        self.scan_push(
            false,
            QueueElement {
                size: -self.right_total,
                token: Token::Begin { indent, box_kind },
                length: 0.0,
            },
        );
    }

    fn close_box(&mut self) {
        if self.depth <= 1 {
            return;
        }
        self.enqueue(QueueElement {
            size: 0.0,
            token: Token::End,
            length: 0.0,
        });
        self.set_size(true);
        self.set_size(false);
        self.depth -= 1;
    }

    fn print_as(&mut self, size: f64, text: &'doc str) -> Result<()> {
        self.enqueue_advance(QueueElement {
            size,
            token: Token::Text(text),
            length: size,
        })
    }

    fn print_break(&mut self, width: f64, offset: f64) {
        self.scan_push(
            true,
            QueueElement {
                size: -self.right_total,
                token: Token::Break { width, offset },
                length: width,
            },
        );
    }

    fn force_newline(&mut self) -> Result<()> {
        self.enqueue_advance(QueueElement {
            size: 0.0,
            token: Token::Newline,
            length: 0.0,
        })
    }

    fn flush(&mut self) -> Result<()> {
        while self.depth > 1 {
            self.close_box();
        }
        self.right_total = INFINITY;
        self.advance_left()
    }

    /// pp_print_newline: flush, print a newline, and start over with no open boxes.
    fn flush_newline(&mut self) -> Result<()> {
        self.flush()?;
        let mut output = std::mem::take(&mut self.output);
        output.push('\n');
        *self = Self::new(self.max_indent);
        self.output = output;
        Ok(())
    }
}

// Printers build a document of layout commands first and render it once, so names resolve while
// the printer still knows the context they were bound in.
#[derive(Clone, Debug, PartialEq)]
enum Command {
    Open { box_kind: BoxKind, indent: f64 },
    Close,
    Text { text: String, size: f64 },
    Break { width: f64, offset: f64 },
    Newline,
    Flush,
}

#[derive(Clone, Debug, PartialEq)]
enum Entry {
    Command(Command),
    Doc(Doc),
    /// A `%s` or `%a` with no argument left, which the TypeScript pushes as `undefined`.
    Undefined,
    /// A directive with no closing `>`.
    Malformed,
}

/// A document of layout commands and nested documents. `Doc::from(vec![...])` stands for the
/// TypeScript's array literal of docs.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Doc(Vec<Entry>);

impl From<Vec<Doc>> for Doc {
    fn from(docs: Vec<Doc>) -> Self {
        Self(docs.into_iter().map(Entry::Doc).collect())
    }
}

/// An argument of `format`: a string for `%s` or a doc for `%a`.
#[derive(Clone, Debug, PartialEq)]
pub enum FormatArg {
    Text(String),
    Doc(Doc),
}

impl From<&str> for FormatArg {
    fn from(value: &str) -> Self {
        Self::Text(value.to_owned())
    }
}

impl From<String> for FormatArg {
    fn from(value: String) -> Self {
        Self::Text(value)
    }
}

impl From<Doc> for FormatArg {
    fn from(value: Doc) -> Self {
        Self::Doc(value)
    }
}

/// `getLength`: the UTF-8 length, which is the string's length when it is ASCII.
fn get_text(value: String) -> Command {
    #[allow(clippy::cast_precision_loss)]
    let size = value.len() as f64;
    Command::Text { text: value, size }
}

/// Prints a string as is, where format would read @ and % in it as directives.
pub fn text(value: &str) -> Doc {
    if value.is_empty() {
        return Doc::default();
    }
    Doc(vec![Entry::Command(get_text(value.to_owned()))])
}

const SPACE: Command = Command::Break {
    width: 1.0,
    offset: 0.0,
};

const CUT: Command = Command::Break {
    width: 0.0,
    offset: 0.0,
};

/// `String(value)` of a doc, an array whose commands are objects.
fn get_doc_string(doc: &Doc) -> String {
    doc.0
        .iter()
        .map(|entry| match entry {
            Entry::Command(_) => "[object Object]".to_owned(),
            Entry::Doc(inner_doc) => get_doc_string(inner_doc),
            Entry::Undefined | Entry::Malformed => String::new(),
        })
        .collect::<Vec<_>>()
        .join(",")
}

fn is_js_whitespace(character: char) -> bool {
    matches!(
        character,
        '\t' | '\n' | '\u{b}' | '\u{c}' | '\r' | ' ' | '\u{a0}' | '\u{1680}' | '\u{2000}'
            ..='\u{200a}'
                | '\u{2028}'
                | '\u{2029}'
                | '\u{202f}'
                | '\u{205f}'
                | '\u{3000}'
                | '\u{feff}'
    )
}

fn is_decimal_literal(text: &str) -> bool {
    let unsigned = text.strip_prefix(['+', '-']).unwrap_or(text);
    let (mantissa, exponent) = match unsigned.find(['e', 'E']) {
        Some(split) => (&unsigned[..split], Some(&unsigned[split + 1..])),
        None => (unsigned, None),
    };
    let (whole, fraction) = mantissa.split_once('.').unwrap_or((mantissa, ""));
    let is_digits = |part: &str| part.bytes().all(|byte| byte.is_ascii_digit());
    let is_exponent = exponent.is_none_or(|exponent| {
        let digits = exponent.strip_prefix(['+', '-']).unwrap_or(exponent);
        !digits.is_empty() && is_digits(digits)
    });
    is_digits(whole) && is_digits(fraction) && whole.len() + fraction.len() > 0 && is_exponent
}

/// `Number(text)` of a string.
fn get_number(units: &[u16]) -> f64 {
    let decoded = String::from_utf16_lossy(units);
    let trimmed = decoded.trim_matches(is_js_whitespace);
    if trimmed.is_empty() {
        return 0.0;
    }
    match trimmed {
        "Infinity" | "+Infinity" => return f64::INFINITY,
        "-Infinity" => return f64::NEG_INFINITY,
        _ => {}
    }
    let radix = match trimmed.get(..2) {
        Some("0x" | "0X") => 16,
        Some("0o" | "0O") => 8,
        Some("0b" | "0B") => 2,
        _ => 0,
    };
    if radix != 0 {
        let digits = &trimmed[2..];
        if digits.is_empty() {
            return f64::NAN;
        }
        return digits
            .chars()
            .try_fold(0.0, |value, character| {
                character
                    .to_digit(radix)
                    .map(|digit| value * f64::from(radix) + f64::from(digit))
            })
            .unwrap_or(f64::NAN);
    }
    if !is_decimal_literal(trimmed) {
        return f64::NAN;
    }
    trimmed.parse().unwrap_or(f64::NAN)
}

fn parse_open(directive: &[u16]) -> Command {
    let split = directive
        .iter()
        .position(|unit| (u16::from(b'0')..=u16::from(b'9')).contains(unit))
        .unwrap_or(directive.len());
    let box_kind = match String::from_utf16_lossy(&directive[..split]).as_str() {
        "h" => BoxKind::H,
        "v" => BoxKind::V,
        "hv" => BoxKind::Hv,
        "hov" => BoxKind::Hov,
        "b" => BoxKind::B,
        _ => BoxKind::Unknown,
    };
    Command::Open {
        box_kind,
        indent: get_number(&directive[split..]),
    }
}

/// `pattern.slice(start, end)`, which is empty when start passes end.
fn get_slice(units: &[u16], start: usize, end: usize) -> &[u16] {
    units.get(start.min(units.len())..end).unwrap_or(&[])
}

/// Interprets the subset of OCaml format strings that tlapm's printers use, so ported printers read
/// like the OCaml they come from. Each %s or %a consumes one argument.
pub fn format(pattern: &str, args: Vec<FormatArg>) -> Doc {
    let units: Vec<u16> = pattern.encode_utf16().collect();
    let find_close = |from: usize| {
        units[from..]
            .iter()
            .position(|&unit| unit == u16::from(b'>'))
            .map(|offset| from + offset)
    };
    let mut doc = Vec::new();
    let mut args = args.into_iter();
    let mut pending: Vec<u16> = Vec::new();
    let flush_text = |doc: &mut Vec<Entry>, pending: &mut Vec<u16>| {
        if pending.is_empty() {
            return;
        }
        doc.push(Entry::Command(get_text(String::from_utf16_lossy(pending))));
        pending.clear();
    };
    let mut index = 0;
    while index < units.len() {
        let character = units[index];
        if character == u16::from(b'%') {
            flush_text(&mut doc, &mut pending);
            match args.next() {
                Some(FormatArg::Doc(argument)) => doc.push(Entry::Doc(argument)),
                Some(FormatArg::Text(argument)) if !argument.is_empty() => {
                    doc.push(Entry::Command(get_text(argument)));
                }
                Some(FormatArg::Text(_)) => {}
                None => doc.push(Entry::Undefined),
            }
            index += 2;
            continue;
        }
        if character != u16::from(b'@') {
            pending.push(character);
            index += 1;
            continue;
        }
        flush_text(&mut doc, &mut pending);
        match units
            .get(index + 1)
            .and_then(|&unit| u8::try_from(unit).ok())
        {
            Some(b'[') => {
                if units.get(index + 2) != Some(&u16::from(b'<')) {
                    doc.push(Entry::Command(Command::Open {
                        box_kind: BoxKind::B,
                        indent: 0.0,
                    }));
                    index += 1;
                } else {
                    let Some(end) = find_close(index) else {
                        doc.push(Entry::Malformed);
                        break;
                    };
                    doc.push(Entry::Command(parse_open(get_slice(
                        &units,
                        index + 3,
                        end,
                    ))));
                    index = end;
                }
            }
            Some(b']') => {
                doc.push(Entry::Command(Command::Close));
                index += 1;
            }
            Some(b' ') => {
                doc.push(Entry::Command(SPACE));
                index += 1;
            }
            Some(b',') => {
                doc.push(Entry::Command(CUT));
                index += 1;
            }
            Some(b'\n') => {
                doc.push(Entry::Command(Command::Newline));
                index += 1;
            }
            Some(b'.') => {
                doc.push(Entry::Command(Command::Flush));
                index += 1;
            }
            Some(b';') => {
                let Some(end) = find_close(index) else {
                    doc.push(Entry::Malformed);
                    break;
                };
                let values: Vec<&[u16]> = get_slice(&units, index + 3, end)
                    .split(|&unit| unit == u16::from(b' '))
                    .collect();
                doc.push(Entry::Command(Command::Break {
                    width: values.first().map_or(f64::NAN, |value| get_number(value)),
                    offset: values.get(1).map_or(f64::NAN, |value| get_number(value)),
                }));
                index = end;
            }
            Some(b'<') => {
                let Some(end) = find_close(index) else {
                    doc.push(Entry::Malformed);
                    break;
                };
                let text = match args.next() {
                    Some(FormatArg::Text(argument)) => argument,
                    Some(FormatArg::Doc(argument)) => get_doc_string(&argument),
                    None => "undefined".to_owned(),
                };
                doc.push(Entry::Command(Command::Text {
                    text,
                    size: get_number(get_slice(&units, index + 2, end)),
                }));
                index = end + 2;
            }
            _ => {}
        }
        index += 1;
    }
    flush_text(&mut doc, &mut pending);
    Doc(doc)
}

/// The items' docs between separators; `separator` defaults to `,@ `.
pub fn format_delimited<Item>(
    items: &[Item],
    mut format_item: impl FnMut(&Item) -> Result<Doc>,
    separator: Option<Doc>,
) -> Result<Doc> {
    let separator = separator.unwrap_or_else(|| {
        Doc(vec![
            Entry::Command(get_text(",".to_owned())),
            Entry::Command(SPACE),
        ])
    });
    let mut docs = Vec::new();
    for (index, item) in items.iter().enumerate() {
        if index != 0 {
            docs.push(Entry::Doc(separator.clone()));
        }
        docs.push(Entry::Doc(format_item(item)?));
    }
    Ok(Doc(docs))
}

fn render_into<'doc>(formatter: &mut Formatter<'doc>, doc: &'doc Doc) -> Result<()> {
    for entry in &doc.0 {
        match entry {
            Entry::Doc(inner_doc) => render_into(formatter, inner_doc)?,
            Entry::Command(Command::Open { box_kind, indent }) => {
                formatter.open_box(*box_kind, *indent);
            }
            Entry::Command(Command::Close) => formatter.close_box(),
            Entry::Command(Command::Text { text, size }) => formatter.print_as(*size, text)?,
            Entry::Command(Command::Break { width, offset }) => {
                formatter.print_break(*width, *offset);
            }
            Entry::Command(Command::Newline) => formatter.force_newline()?,
            Entry::Command(Command::Flush) => formatter.flush_newline()?,
            Entry::Undefined => {
                return Err(ObligationError::bug(
                    "TypeError: undefined is not an object (evaluating 'entry.kind')",
                ));
            }
            Entry::Malformed => {
                return Err(ObligationError::bug("Malformed format directive"));
            }
        }
    }
    Ok(())
}

/// 68 is Format's default maximum indent; tlapm's stderr formatter allows 35.
pub fn render_doc(doc: &Doc, max_indent: u32) -> Result<String> {
    let mut formatter = Formatter::new(f64::from(max_indent));
    render_into(&mut formatter, doc)?;
    formatter.flush()?;
    Ok(formatter.output)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn delimited(items: Vec<Doc>, separator: Option<Doc>) -> Doc {
        format_delimited(&items, |item| Ok(item.clone()), separator).expect("identity items")
    }

    /// Expected layouts from rendering the same docs with `src/obligations/format.ts` under Bun:
    /// hand-picked cases, then random ones. `None` is a render the TypeScript throws on.
    #[test]
    fn renders_as_the_typescript_does() {
        let cases: Vec<(Doc, u32, Option<&str>)> = vec![
        (format("", vec![]), 68, Some("")),
        (format("hello", vec![]), 68, Some("hello")),
        (format("@[<h>a@ b@ c@]", vec![]), 68, Some("a b c")),
        (format("@[<v2>a@ b@ c@]", vec![]), 68, Some("a\n  b\n  c")),
        (format("@[<v0>a@,b@,c@]", vec![]), 68, Some("a\nb\nc")),
        (format("@[<hv2>a@ b@ c@]", vec![]), 68, Some("a b c")),
        (format("@[<hv2>wwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwww@ xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx@ c@]", vec![]), 68, Some("wwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwww\n  xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx\n  c")),
        (format("@[<hov2>wwwwwwwwwwwwwwwwwwwwwwwwwwwwww@ xxxxxxxxxxxxxxxxxxxxxxxxxxxxxx@ yyyyyyyyyyyyyyyyyyyyyyyyyyyyyy@ zzzzzzzzzzzzzzzzzzzzzzzzzzzzzz@]", vec![]), 68, Some("wwwwwwwwwwwwwwwwwwwwwwwwwwwwww xxxxxxxxxxxxxxxxxxxxxxxxxxxxxx\n  yyyyyyyyyyyyyyyyyyyyyyyyyyyyyy zzzzzzzzzzzzzzzzzzzzzzzzzzzzzz")),
        (format("@[<b2>wwwwwwwwwwwwwwwwwwwwwwwwwwwwww@ xxxxxxxxxxxxxxxxxxxxxxxxxxxxxx@ yyyyyyyyyyyyyyyyyyyyyyyyyyyyyy@ zzzzzzzzzzzzzzzzzzzzzzzzzzzzzz@]", vec![]), 68, Some("wwwwwwwwwwwwwwwwwwwwwwwwwwwwww xxxxxxxxxxxxxxxxxxxxxxxxxxxxxx\n  yyyyyyyyyyyyyyyyyyyyyyyyyyyyyy zzzzzzzzzzzzzzzzzzzzzzzzzzzzzz")),
        (format("@[wwwwwwwwwwwwwwwwwwwwwwwwwwwwww@ xxxxxxxxxxxxxxxxxxxxxxxxxxxxxx@ yyyyyyyyyyyyyyyyyyyyyyyyyyyyyy@]", vec![]), 68, Some("wwwwwwwwwwwwwwwwwwwwwwwwwwwwww xxxxxxxxxxxxxxxxxxxxxxxxxxxxxx\nyyyyyyyyyyyyyyyyyyyyyyyyyyyyyy")),
        (format("@[<h>wwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwww@ xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx@ yyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyy@]", vec![]), 68, Some("wwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwww xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx yyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyy")),
        (format("@[<hov4>wwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwww@ b@ xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx@]", vec![]), 68, Some("wwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwww\n    b\n    xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx")),
        (format("@[<v2>a@;<3 5>b@;<0 -1>c@]", vec![]), 68, Some("a\n       b\n c")),
        (format("@[<hov2>a@;<3 5>b@;<0 1>c@]", vec![]), 68, Some("a   bc")),
        (format("first@\nsecond@\nthird", vec![]), 68, Some("first\nsecond\nthird")),
        (format("@[<v2>first@\nsecond@]@\nthird", vec![]), 68, Some("first\n  second\nthird")),
        (format("a@.b@.c", vec![]), 68, Some("a\nb\nc")),
        (format("@[<v2>a@ b@.c@ d@]", vec![]), 68, Some("a\n  b\nc\nd")),
        (format("@[<hov2>%s@ %a@]", vec!["name".into(), format("@[<b1>(%s)@]", vec!["x".into()]).into()]), 68, Some("name (x)")),
        (format("@[<h>@<1>%s%a@<1>%s@]", vec!["<[".into(), format("e", vec![]).into(), "]>".into()]), 68, Some("<[e]>")),
        (format("@[<h>@<1>%s@]", vec!["\u{3b1}\u{3b2}\u{3b3}\u{3b4}".into()]), 68, Some("\u{3b1}\u{3b2}\u{3b3}\u{3b4}")),
        (format("@<5>%s|", vec!["x".into()]), 68, Some("x|")),
        (format("\u{2200} x \u{2208} S : \u{3b1}\u{3b2}\u{3b3}@ \u{2203} y", vec![]), 68, Some("\u{2200} x \u{2208} S : \u{3b1}\u{3b2}\u{3b3}\n\u{2203} y")),
        (format("@[<hov2>\u{2200}\u{2200}\u{2200}\u{2200}\u{2200}\u{2200}\u{2200}\u{2200}\u{2200}\u{2200}\u{2200}\u{2200}\u{2200}\u{2200}\u{2200}\u{2200}\u{2200}\u{2200}\u{2200}\u{2200}@ \u{3b1}\u{3b1}\u{3b1}\u{3b1}\u{3b1}\u{3b1}\u{3b1}\u{3b1}\u{3b1}\u{3b1}\u{3b1}\u{3b1}\u{3b1}\u{3b1}\u{3b1}\u{3b1}\u{3b1}\u{3b1}\u{3b1}\u{3b1}@ \u{3b2}\u{3b2}\u{3b2}\u{3b2}\u{3b2}\u{3b2}\u{3b2}\u{3b2}\u{3b2}\u{3b2}\u{3b2}\u{3b2}\u{3b2}\u{3b2}\u{3b2}\u{3b2}\u{3b2}\u{3b2}\u{3b2}\u{3b2}@]", vec![]), 68, Some("\u{2200}\u{2200}\u{2200}\u{2200}\u{2200}\u{2200}\u{2200}\u{2200}\u{2200}\u{2200}\u{2200}\u{2200}\u{2200}\u{2200}\u{2200}\u{2200}\u{2200}\u{2200}\u{2200}\u{2200}\n  \u{3b1}\u{3b1}\u{3b1}\u{3b1}\u{3b1}\u{3b1}\u{3b1}\u{3b1}\u{3b1}\u{3b1}\u{3b1}\u{3b1}\u{3b1}\u{3b1}\u{3b1}\u{3b1}\u{3b1}\u{3b1}\u{3b1}\u{3b1}\n  \u{3b2}\u{3b2}\u{3b2}\u{3b2}\u{3b2}\u{3b2}\u{3b2}\u{3b2}\u{3b2}\u{3b2}\u{3b2}\u{3b2}\u{3b2}\u{3b2}\u{3b2}\u{3b2}\u{3b2}\u{3b2}\u{3b2}\u{3b2}")),
        (format("100%% done %s", vec!["now".into(), "x".into()]), 68, Some("100now done x")),
        (format("%s%s%s", vec!["".into(), "a".into(), "".into()]), 68, Some("a")),
        (format("no@ box@ at@ all", vec![]), 68, Some("no box at\nall")),
        (format("@]@]extra closes@]", vec![]), 68, Some("extra closes")),
        (format("@[<v2>@[<v2>@[<v2>open@ only", vec![]), 68, Some("open\n  only")),
        (format("trailing @", vec![]), 68, Some("trailing ")),
        (format("@x@y@z", vec![]), 68, Some("xyz")),
        (format("@[<xyz2>a@ b@ c@]", vec![]), 68, Some("a b c")),
        (format("@[<xyz2>wwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwww@ xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx@ c@]", vec![]), 68, Some("wwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxc")),
        (format("@[<hov>a@ b@]", vec![]), 68, Some("a b")),
        (format("@[<hov 0x1f>a@ b@]", vec![]), 68, Some("a b")),
        (format("@[<b0x10>wwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwww@ xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx@]", vec![]), 68, Some("wwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwww\n                xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx")),
        (format("@[<v2>a@;<0x2 1e0>b@;< 2  1>c@; >d@]", vec![]), 68, Some("a\n   b\n    c\nd")),
        (format("@[<v2>a@;<1>b@]", vec![]), 68, Some("a\nb")),
        (format("@[<hov2>a@;<1>wwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwww@]", vec![]), 68, Some("a\nwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwww")),
        (format("@[<v2>a@;<1.5 2.5>b@]", vec![]), 68, Some("a\n    b")),
        (format("@[<v2>a@;<+1 -0>b@;<Infinity 1>c@]", vec![]), 68, Some("a\n  b\n   c")),
        (format("@[<h>a@;<-1 0>b@]", vec![]), 68, None /* RangeError: String.prototype.repeat argument must be greater than or equal to 0 and not be Infinity */),
        (format("@[<v0>a@;<1 -5>b@]", vec![]), 68, None /* RangeError: String.prototype.repeat argument must be greater than or equal to 0 and not be Infinity */),
        (format("@<x>%s", vec!["y".into()]), 68, Some("y")),
        (format("@<2>%s", vec![format("a@ b", vec![]).into()]), 68, Some("[object Object],[object Object],[object Object]")),
        (format("@<2>%s", vec![Doc::from(vec![Doc::from(vec![]), format("a", vec![])]).into()]), 68, Some(",[object Object]")),
        (format("@<2>%s", vec![]), 68, Some("undefined")),
        (format("a%sb", vec![]), 68, None /* TypeError: undefined is not an object (evaluating 'entry.kind') */),
        (format("@[<v2>a@ %a@]", vec![]), 68, None /* TypeError: undefined is not an object (evaluating 'entry.kind') */),
        (format("@[<v2>a@ %a@]", vec![text("").into()]), 68, Some("a\n  ")),
        (Doc::from(vec![format("@[<v2>", vec![]), format("a@ b", vec![]), Doc::from(vec![format("c@ d", vec![]), format("@]", vec![])]), format("@ tail", vec![])]), 68, Some("a\n  bc\n  d\ntail")),
        (Doc::from(vec![]), 68, Some("")),
        (text(""), 68, Some("")),
        (text("@ % not directives"), 68, Some("@ % not directives")),
        (delimited(vec![format("a", vec![]), format("b", vec![]), format("c", vec![])], None), 68, Some("a, b,\nc")),
        (format("@[<b1>(%a)@]", vec![delimited(vec![format("wwwwwwwwwwwwwwwwwwwwwwwwwwwwww", vec![]), format("xxxxxxxxxxxxxxxxxxxxxxxxxxxxxx", vec![]), format("yyyyyyyyyyyyyyyyyyyyyyyyyyyyyy", vec![])], None).into()]), 68, Some("(wwwwwwwwwwwwwwwwwwwwwwwwwwwwww, xxxxxxxxxxxxxxxxxxxxxxxxxxxxxx,\n yyyyyyyyyyyyyyyyyyyyyyyyyyyyyy)")),
        (format("@[<hov0>%a@]", vec![delimited(vec![format("a", vec![]), format("b", vec![])], Some(format(" \\/@ ", vec![]))).into()]), 68, Some("a \\/ b")),
        (delimited(vec![], None), 68, Some("")),
        (delimited(vec![format("only", vec![])], None), 68, Some("only")),
        (format("@[<v2>wwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwww@ @[<v2>wwwwwwwwww@ @[<v2>wwwwwwwwww@ @[<v2>wwwwwwwwww@ deep@]@]@]@]", vec![]), 68, Some("wwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwww\n  wwwwwwwwww\n    wwwwwwwwww\n      wwwwwwwwww\n        deep")),
        (format("@[<v2>wwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwww@ @[<v2>wwwwwwwwww@ @[<v2>wwwwwwwwww@ @[<v2>wwwwwwwwww@ deep@]@]@]@]", vec![]), 35, Some("wwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwww\n  wwwwwwwwww\n    wwwwwwwwww\n      wwwwwwwwww\n        deep")),
        (format("@[<v2>wwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwww@ @[<v2>wwwwwwwwww@ @[<v2>wwwwwwwwww@ deep@]@]@]", vec![]), 0, Some("wwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwww\nwwwwwwwwww\nwwwwwwwwww\ndeep")),
        (format("@[<hov2>wwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwww@ @[<hov2>wwwwwwwwwwwwwwwwwwww@ wwwwwwwwwwwwwwwwwwww@ wwwwwwwwwwwwwwwwwwww@]@]", vec![]), 35, Some("wwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwww\n  wwwwwwwwwwwwwwwwwwww wwwwwwwwwwwwwwwwwwww wwwwwwwwwwwwwwwwwwww")),
        (format("[ERROR]: @[<v2>Could not prove or check:@,%a@]", vec![format("@[<b0>wwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwww@ xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx@]", vec![]).into()]), 35, Some("[ERROR]: Could not prove or check:\n           wwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwww\n           xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx")),
        (format(";; obligation #%s@\n%a", vec!["3".into(), format("@[<hv2>a@ b@]", vec![]).into()]), 68, Some(";; obligation #3\na b")),
        (format("wwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwww@ x", vec![]), 68, Some("wwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwww\nx")),
        (format("@[<hov0>wwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwww@ x@]", vec![]), 68, Some("wwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwww\nx")),
        (format("@[<hov0>wwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwww@ x@]", vec![]), 68, Some("wwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwww\nx")),
        (format("@[<hov0>wwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwww@ x@ y@]", vec![]), 68, Some("wwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwww\nx y")),
        (format("@[<b2>wwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwww@[<b2>@ wwwww@ wwwww@]@]", vec![]), 68, Some("wwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwww\n   wwwww wwwww")),
        (format("wwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwww@[<v2>a@ b@]", vec![]), 68, Some("wwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwww\na\n  b")),
        (format("wwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwww@[<hov2>a@ b@ c@ d@]", vec![]), 68, Some("wwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwww\na b c d")),
        (format("@[<h>wwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwww@]@ @[<v2>a@ b@]", vec![]), 68, Some("wwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwww\na\n  b")),
        (format("@[<v2>a@ b@.@[<hov2>c@ d@]@.e", vec![]), 35, Some("a\n  b\nc d\ne")),
        (format("@.@.@.", vec![]), 68, Some("\n\n\n")),
        (format("@\n@\n", vec![]), 68, Some("\n\n")),
        (format("<<a, b>>@[<h4>@[<hov1>@]\\ATRUE@\nCardinality(S)@ <<a, b>>%a@]TRUE@\nTRUE@[@;<0 3>@ @[<v2>@ %sCardinality(S)foo_bar@ \u{2200}@,@\n@[<h2>@ @,@[<hv4>@]@]", vec![format("@ @\nfoo_bar@ @, @ ", vec![]).into(), "x".into()]), 10, Some("<<a, b>>\\ATRUE\n          Cardinality(S) <<a, b>> \n          foo_bar   TRUE\nTRUE \n       xCardinality(S)foo_bar\n       \u{2200}\n       \n        ")),
        (format("@[<v4>@[<hov4>@ Cardinality(S)@.@]@]", vec![]), 68, Some(" Cardinality(S)\n")),
        (format("\u{2200}@\n\\A@\n@ @ Cardinality(S)@\n@\n @;<3 1>\u{3b1}\u{3b2}\u{3b3}@[<hov2>@[<hov0>@;<0 3>@ =>@ abc@,%s@]@]\u{2200}=>=>abcCardinality(S)@[<v2>%a@]Cardinality(S)@,@[<v0>@]\u{2200}@ @ @[<hv1>@ @ @;<1 4>", vec!["\u{3b1}\u{3b2}\u{3b3}".into(), format("=> \u{3b1}\u{3b2}\u{3b3} foo_bar", vec![]).into()]), 10, Some("\u{2200}\n\\A\n  Cardinality(S)\n\n \n \u{3b1}\u{3b2}\u{3b3} => abc\u{3b1}\u{3b2}\u{3b3}\u{2200}=>=>abcCardinality(S)\n=> \u{3b1}\u{3b2}\u{3b3} foo_barCardinality(S)\n\u{2200} \n   ")),
        (format("%a%s@\n@ @[<v3>@;<2 2>Cardinality(S)foo_bar@]@\n%s\\A%a@\n@ y'@\nCardinality(S)%a<<a, b>>@\n", vec![format("=>%s@ @ foo_bar", vec!["x".into()]).into(), "<<a, b>>".into(), "TRUE".into(), format("TRUE@\n@[<h4>@]@\nabc\u{2200}@ \\in%a@[<h2>@]", vec![format("y'@ @[<h4>@ @]", vec![]).into()]).into(), format("@  @[<hov2>@,@[<v1>TRUE@]@]", vec![]).into()]), 35, Some("=>x  foo_bar<<a, b>>\n \n      Cardinality(S)foo_bar\nTRUE\\ATRUE\n\nabc\u{2200} \\iny'  \n y'\nCardinality(S)\n TRUE<<a, b>>\n")),
        (format("@\n@\n@\n @[<h3>@ @[<b2>abc=>@ \u{2200}@[<hov3>@ x=>@.@[<h0>@;<2 3>foo_barabcabc@ %a@[<hv1>@]foo_bar@ @ @ zzzzzzzzzzzzzzz@,%s<<a, b>>@]@ %s@ @[<hv2>@[<h2>%a=>\\A@ @[<hov3>@]", vec![format("@[<hv0>Cardinality(S)", vec![]).into(), "\\A".into(), "abc".into(), format("%a@\n%s@ @\n@;<3 4>%s@[<hv0>@\naaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaazzzzzzzzzzzzzzzzzzzzzzzzzzzzzz", vec![format("@ foo_bar@ @\n@ @ ", vec![]).into(), "=>".into(), "\\in".into()]).into()]), 10, Some("\n\n\n  abc=> \u{2200} x=>\n  foo_barabcabc Cardinality(S)foo_bar   zzzzzzzzzzzzzzz\\A<<a, b>> abc  foo_bar \n            \n          => \n             \\in\n          aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaazzzzzzzzzzzzzzzzzzzzzzzzzzzzzz=>\\A\n          ")),
        (format("@\nfoo_bar@ \u{3b1}\u{3b2}\u{3b3}@\n@\n@ @\n@;<0 4>bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\u{2200}@;<3 2>x@;<0 1>aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa @;<3 2>", vec![]), 0, Some("\nfoo_bar \u{3b1}\u{3b2}\u{3b3}\n\n \nbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\u{2200}   x\naaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa \n")),
        (format("@\n@ @ TRUE\\A@[<hv0>TRUE@]", vec![]), 68, Some("\n \nTRUE\\ATRUE")),
        (format("@\n@\n@[<h4>y'=>%a@]\u{2200}@  %s%s@\n%a\\A%aCardinality(S)@\n@ %a@\naaaaaaaaaaaaaaa@;<1 3>@\n@ @[<h3>abc@]", vec![format("foo_bar%a<<a, b>>@\nCardinality(S)@\n@ @[<<a, b>>", vec![format("@\n@\n<<a, b>>@\nabcTRUE@ @[<v3>@;<1 2>@]", vec![]).into()]).into(), "x".into(), "\\in".into(), format("@ \\in@[<v1>@[<hov1>@ %a=>@ @ ", vec![format("@\n@,\\in@ @ TRUE%a<<a, b>>TRUE<<a, b>>@\n@\n", vec![format("@\n@\n\u{3b1}\u{3b2}\u{3b3}@[<h2>@ @]", vec![]).into()]).into()]).into(), format("@,@\n@,%saaaaaaaaaaaaaaaaaaa@\n=>@[<hov2>%s@ @]", vec!["=>".into(), "\\in".into()]).into(), format("%a@[<h2>@;<0 2>@,@\n@]bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbCardinality(S)@[<hov4>@,abc\u{2200}@]", vec![format("@,%a@,\\in@;<1 1>\\in%azzzzzzzzzzx@;<3 0>", vec![format("@\n%s@ \\Afoo_bar@\n=>Cardinality(S)\u{2200}Cardinality(S)", vec!["aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".into()]).into(), format("@;<3 2>@;<0 2>x", vec![]).into()]).into()]).into()]), 0, Some("\n\ny'=>foo_bar\n\n<<a, b>>\nabcTRUE \n<<a, b>>\nCardinality(S)\n >\u{2200}  x\\in\n \\in \n\\in  TRUE\n\n\u{3b1}\u{3b2}\u{3b3}\n <<a, b>>TRUE<<a, b>>\n\n=>  \\A\n=>aaaaaaaaaaaaaaaaaaa\n=>\\in Cardinality(S)\n \naaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n\\Afoo_bar\n=>Cardinality(S)\u{2200}Cardinality(S)\\in \\in   xzzzzzzzzzzx\n\nbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbCardinality(S)\nabc\u{2200}\naaaaaaaaaaaaaaa \n abc")),
        (format("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa@ \\in@\n@ %s\u{2200}@ TRUE<<a, b>>@ \\A@;<1 3>TRUEx", vec!["\u{3b1}\u{3b2}\u{3b3}".into()]), 35, Some("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa \\in\n \u{3b1}\u{3b2}\u{3b3}\u{2200} TRUE<<a, b>> \\A\n   TRUEx")),
        (format("%sabc@\n%s\u{2200}@\n@[@;<3 2>@ %a@]@\nfoo_bar@[@;<1 4>\\in@[<b1>@]@]", vec!["<<a, b>>".into(), "\\in".into(), format("x@\n\\in%a@;<3 3>", vec![format("@ \\A\u{3b1}\u{3b2}\u{3b3}@ foo_bar@[<h0>x%a ", vec![format("@\nzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz@ y'", vec![]).into()]).into()]).into()]), 10, Some("<<a, b>>abc\n\\in\u{2200}\n    x\n\\in \\A\u{3b1}\u{3b2}\u{3b3}\nfoo_barx\n       zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz y'    \nfoo_bar \\in")),
        (format("%s\\in\\A%s<<a, b>>\\in@;<1 2>@,aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\u{3b1}\u{3b2}\u{3b3}@[<hv3>@[@[<hv2>%a@;<2 2>=>\u{3b1}\u{3b2}\u{3b3}y'@;<2 1>@,@]@[<hv2>@]abc@ %a@[<v4>%s@]@]@]", vec!["=>".into(), "\\in".into(), format("@ @[y'@ x@;<3 4>@ TRUE@[<hv2>@]@]", vec![]).into(), format("zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz\\in@\n%a%aCardinality(S)\\A=>", vec![format("TRUE@;<2 2>\u{2200}@[<v0>TRUE@ @.@]", vec![]).into(), format("@ abc@ \\in%s@[@,", vec!["foo_bar".into()]).into()]).into(), "\u{2200}".into()]), 35, Some("=>\\in\\A\\in<<a, b>>\\in \naaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\u{3b1}\u{3b2}\u{3b3}\n y' x    TRUE  =>\u{3b1}\u{3b2}\u{3b3}y'  abc zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz\\in\nTRUE  \u{2200}TRUE\n         \n abc\n\\infoo_barCardinality(S)\\A=>\u{2200}")),
        (format("@,@\n@ \u{2200}@[<hov4>\u{2200}@]@.@;<0 2>\\in%s=>%s@ abc@.%a@[<h1>%s@,TRUE@,@]@ foo_bar%s@,aaaaaaaaaaaaaaay'x@[<b3>=>%sx@,@;<1 4>\u{2200}@ @[\u{3b1}\u{3b2}\u{3b3}@]@]", vec!["=>".into(), "=>".into(), format("@;<3 4>y'", vec![]).into(), "x".into(), "Cardinality(S)".into(), "y'".into()]), 0, Some("\n\n\u{2200}\n\u{2200}\n\\in=>=>=>\nabc\n   y'\nxTRUE foo_barCardinality(S)\naaaaaaaaaaaaaaay'x\n=>y'x \u{2200} \u{3b1}\u{3b2}\u{3b3}")),
        (format("x@,x@[<v2>@[%ax@.%ay'abcx@[<h4>\\ATRUE@[<hv2>@ @;<0 0>@ @ =>@ \\inx@\n foo_bar@]zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz@,%aabc@[<hv2>=>@;<1 0>@ <<a, b>>@]@]@]@]", vec![format("@\n@[<b0>@ @,@[<hov3>@]@]", vec![]).into(), format("abcTRUE@\n@\n@ @\naaaaaaaaaaaa@\n\\Azzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz", vec![]).into(), format("@ <<a, b>>@\n@\n=><<a, b>>@\n @\n@[<v4>abc@ @]", vec![]).into()]), 0, Some("x\nx\n\n x\nabcTRUE\n\n\n\naaaaaaaaaaaa\n\\Azzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzy'abcx\n\\ATRUE   => \\inx\n foo_barzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz <<a, b>>\n\n=><<a, b>>\n \nabc\nabc=>  <<a, b>>")),
        (format("x\\A@ %a@\n@ @ @;<3 4>@[<v2>@[y'@[<hov2>@ y'@]@]Cardinality(S)@]@ ", vec![format("xCardinality(S)@ @ \\A@\n@[<v2>\\A@]\\in", vec![]).into()]), 68, Some("x\\A xCardinality(S)  \\A\n\\A\\in\n     y' y'Cardinality(S)\n")),
        (format("%a@ @\n@ aaaaaaaaaaaaaaaa@ Cardinality(S)@\n@\n@\n<<a, b>>x@[<hov1>", vec![format(" @;<2 0>@[<v4><<a, b>>@]", vec![]).into()]), 0, Some("   \n<<a, b>> \n aaaaaaaaaaaaaaaa\nCardinality(S)\n\n\n<<a, b>>x\n")),
        (format("@\n@[<hv2>@;<1 3>Cardinality(S)@;<1 1>@.@ %a@]@ abc@ @.TRUEx%a=>abc%a%a@\n@ @ @\nfoo_bar%sCardinality(S)x%a@\n%s@ @ @ @,@[<h4>\\inCardinality(S)\u{3b1}\u{3b2}\u{3b3}=>y'@;<0 0>x@ ", vec![format("@\n@[<h0>foo_bar@[<h3>@[<v1>%a\\A@]<<a, b>>=>@ @]@]", vec![format("@[<v3>@  =>@[@]@]", vec![]).into()]).into(), format(" %ay'@ @ ", vec![format("@\n\u{2200}@ abcx", vec![]).into()]).into(), format("=>TRUEfoo_bar@,@ ", vec![]).into(), format("@;<0 2>%ax@.@ @ %s", vec![format("abcfoo_bar%s\\in%a%sfoo_bary'\\A@[<b2>foo_bar\\Ay'", vec!["x".into(), format("<<a, b>>@ @\n@[<hov0>TRUE@ \\in@ y'@[<hov3>abc", vec![]).into(), "<<a, b>>".into()]).into(), "abc".into()]).into(), "x".into(), format("@,=>x@,@ @ Cardinality(S)@\n@[<h3>@]@;<3 2>%s", vec!["<<a, b>>".into()]).into(), "foo_bar".into()]), 68, Some("\n Cardinality(S) \n \nfoo_bar\n           =>\\A<<a, b>>=>  abc\n\nTRUEx \n\u{2200} abcxy'  =>abc=>TRUEfoo_bar abcfoo_barx\\in<<a, b>>\n\nTRUE \\in y'abc<<a, b>>foo_bary'\\Afoo_bar\\Ay'x\n  abc\n  \nfoo_barxCardinality(S)x=>x  Cardinality(S)\n   <<a, b>>\nfoo_bar   \n\\inCardinality(S)\u{3b1}\u{3b2}\u{3b3}=>y'x ")),
        (format("@[@]%s@ \u{2200}@ Cardinality(S)@;<2 4>@.Cardinality(S)x@ @[<h2>aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa%ax@;<2 2>\u{2200}y'%s\\A@ %s @]@[<b4>bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb@;<1 2><<a, b>>%a@[<b4>@ @ @;<0 2>%a@ @,@ @,@]", vec!["Cardinality(S)".into(), format("@[<hov4>@ @;<2 1>bbbbbbbbbbbbbbbbbbbbbbbbb@]", vec![]).into(), "\\A".into(), "Cardinality(S)".into(), format("\\in@\n\u{3b1}\u{3b2}\u{3b3}@;<2 3>@\ny'@\n@,@,@;<0 1>TRUE", vec![]).into(), format("@ =>%a@ @,=>@ \u{3b1}\u{3b2}\u{3b3}@ @,Cardinality(S)", vec![format("<<a, b>>@\nfoo_bar@.=>@, @\n@\n@\n@,zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz", vec![]).into()]).into()]), 10, Some("Cardinality(S) \u{2200} Cardinality(S)\n    \nCardinality(S)x\naaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa   bbbbbbbbbbbbbbbbbbbbbbbbbx  \u{2200}y'\\A\\A Cardinality(S) \nbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\n      <<a, b>>\\in\n    \u{3b1}\u{3b2}\u{3b3}  \n    y'\n    TRUE   =><<a, b>>\n          foo_bar\n=> \n\n\nzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz => \u{3b1}\u{3b2}\u{3b3} Cardinality(S)  \n")),
        (format("@[<v0>y' \\A@;<0 2> %a\\in@]", vec![format("\\A@ @;<3 0>@[<hov0>bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb@[@]\\A%a@]", vec![format("@\n zzzzzzzzzzzzzzzzzzzzz", vec![]).into()]).into()]), 68, Some("y' \\A\n   \\A\n\nbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\n\\A\n zzzzzzzzzzzzzzzzzzzzz\\in")),
        (format("\\in@ %a%a@ @\nabc@,\\Azzzzzzzzzzzzzzzzzzfoo_bar@[@,@]@,\\Aabc@\n@ @\n\\in@ @ @ @\n @\n@ @ ", vec![format("y'%s@[<b4>@[<hov2>@ @]@ @]@;<2 1>@\n", vec!["aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".into()]).into(), format("@,@;<2 1>@[@;<0 3>@]", vec![]).into()]), 10, Some("\\in y'aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n    \n   \nabc\\Azzzzzzzzzzzzzzzzzzfoo_bar\n\\Aabc\n \n\\in   \n \n \n")),
        (format("\u{2200}@\n=>x@.@;<3 0> @\n", vec![]), 10, Some("\u{2200}\n=>x\n\n \n")),
        (format("Cardinality(S)@\n@, @[<hv2>abc@[<hov0>y'foo_bar@ @, @,bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb<<a, b>>@ @[@ @ @[<b2>@[@[<b0>@,@] @]@]@]@]x@,%s@[<b3>@] @]aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa@,", vec!["\u{2200}".into()]), 0, Some("Cardinality(S)\n\n \nabc\ny'foo_bar  bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb<<a, b>> \n   x\n\u{2200}\n aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n")),
        (format("@[foo_bar@]%a\\A@\nTRUE\\Ay'Cardinality(S)@ @[<h1>@ %s@ @[<hov0>@[<b2>zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz=>%a%a@]@]abcxabcaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa@]", vec![format("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa%sTRUE@ @\naaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa \u{3b1}\u{3b2}\u{3b3}", vec!["=>".into()]).into(), "<<a, b>>".into(), format("y'%s@,", vec!["zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz".into()]).into(), format("%s%s\\A%s@,@[<v3>%a@]", vec!["\\A".into(), "\\in".into(), "\u{2200}".into(), format("@ %a\\in@ @\n@\n", vec![format("foo_bar@,bbbbbbbbbbbbb%s@\n", vec!["\u{2200}".into()]).into()]).into()]).into()]), 68, Some("foo_baraaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa=>TRUE\n\naaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa \u{3b1}\u{3b2}\u{3b3}\\A\nTRUE\\Ay'Cardinality(S)\n <<a, b>> zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz=>y'zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz\n            \\A\\in\\A\u{2200}\n                         foo_bar\n                         bbbbbbbbbbbbb\u{2200}\n                         \\in\n                         \n                         \n                         abcxabcaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")),
        (format("\u{2200}@\n<<a, b>>@[<hv1>abc bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb%a<<a, b>>TRUEy'Cardinality(S)abc@ %a@ @, \\in@[@[<b4>@ @ <<a, b>>@ TRUE%a @]", vec![format("@\n=>%a@\n<<a, b>>@;<1 3> \\A@.abcabc", vec![format("@[<b3>@ %s@,@ \\in\\in@;<2 0>@]@ ", vec!["TRUE".into()]).into()]).into(), format("@,@\n<<a, b>>@,@\n@;<0 0>@;<1 1>@\n@\n@[<hov1>@,%a@ @]", vec![format("@[<b0>@\nabc @]", vec![]).into()]).into(), format("\u{3b1}\u{3b2}\u{3b3}%s\\in@\n@ %s", vec!["y'".into(), "\u{2200}".into()]).into()]), 68, Some("\u{2200}\n<<a, b>>abc bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\n         => TRUE \\in\\in  \n         \n         <<a, b>>\n             \\A\nabcabc<<a, b>>TRUEy'Cardinality(S)abc \n<<a, b>>\n \n\n\nabc   \n \\in  <<a, b>> TRUE\u{3b1}\u{3b2}\u{3b3}y'\\in\n         \u{2200} ")),
        (format("foo_bar\\in@, TRUE%s@[<hv3>TRUE@\n\u{2200}TRUE@ @;<2 4>=>@]zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz\\in@ abc%aabcfoo_bar@ foo_bar<<a, b>>abc@\n@[<b0>@\n", vec!["Cardinality(S)".into(), format("@;<1 4>@;<1 3>@\n@;<3 0>", vec![]).into()]), 0, Some("foo_bar\\in\n TRUECardinality(S)\nTRUE\n\u{2200}TRUE   =>zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz\\in\nabc  \n   abcfoo_bar\nfoo_bar<<a, b>>abc\n\n")),
        (format("@ @;<2 2>\\in\u{2200}@ @,@ @\n@ @[@]@\n@[<hv1>%a@\n%s<<a, b>>%s@;<0 2>TRUE<<a, b>>%a@ @,@ @[<v4>%s@ @ @[", vec![format("=>@ =>\\in@  %a@\ny'@ @ y'", vec![format("@ @ %s@ @;<3 4>", vec!["foo_bar".into()]).into()]).into(), "\u{3b1}\u{3b2}\u{3b3}".into(), "abc".into(), format("@[<hv0>Cardinality(S)@ @]", vec![]).into(), "=>".into()]), 0, Some("   \\in\u{2200}  \n\n\n=>\n=>\\in\n \n\nfoo_bar\n\n\ny'\n\ny'\n\u{3b1}\u{3b2}\u{3b3}<<a, b>>abc\nTRUE<<a, b>>\nCardinality(S) \n\n\n=>\n\n")),
        (format("@[<hv2>@,\\A@]<<a, b>>@[<hv3>@ @]@[@ %ay'@[<b0>@]@] <<a, b>>@[@[<v3>@]@]", vec![format("@ @ @\n", vec![]).into()]), 68, Some("\\A<<a, b>>    \n           y' <<a, b>>")),
        (format("@ @;<0 3>\u{2200}@[<hv0>@;<0 1>\u{3b1}\u{3b2}\u{3b3}abc%abbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbTRUE@[<b0>%s%a\u{3b1}\u{3b2}\u{3b3}%s@[<h2>@,@[<b4>@]", vec![format("\\in<<a, b>>@\n<<a, b>>%a@,", vec![format(" \\in@;<3 0>@[<b4>@.\u{3b1}\u{3b2}\u{3b3}abc@ %s%s@ @.@]", vec!["Cardinality(S)".into(), "\\in".into()]).into()]).into(), "\u{3b1}\u{3b2}\u{3b3}".into(), format("\\ATRUE@\n@[<v4>@,@]", vec![]).into(), "y'".into()]), 0, Some(" \n\u{2200}\n\u{3b1}\u{3b2}\u{3b3}abc\\in<<a, b>>\n<<a, b>> \\in   \n\u{3b1}\u{3b2}\u{3b3}abc Cardinality(S)\\in\n\n\nbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbTRUE\n\u{3b1}\u{3b2}\u{3b3}\\ATRUE\n\n\u{3b1}\u{3b2}\u{3b3}y'\n")),
        (format("@ @\n@[<hv3>abc@ <<a, b>>@;<2 1>@[<hov3>%s@[<hv1>=>%a@ aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa<<a, b>>\u{2200}%sfoo_bar@]@]@]", vec!["\u{2200}".into(), format("@,@[<hv2>\\A@;<3 3>@;<2 0>\\A@]", vec![]).into(), "<<a, b>>".into()]), 68, Some("\n\nabc\n   <<a, b>>\n    \u{2200}=>\n        \\A     \\A\n        aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa<<a, b>>\u{2200}<<a, b>>foo_bar")),
        (format("Cardinality(S)@ @;<0 2>abc@\nfoo_bar@ @;<0 2>@,@ @.=>foo_bar@;<3 0>@ Cardinality(S)@\ny'%aTRUECardinality(S)@,abc@[ @ %a@;<0 4>y'@,%a@]<<a, b>>@ ", vec![format("@ @[<v1>%s%a@[<hov0>@[<hov3>@,@]@[<h2>@]@]@]", vec!["TRUE".into(), format("@ @,@ =>@ \u{3b1}\u{3b2}\u{3b3}", vec![]).into()]).into(), format("Cardinality(S)y'@,@,=>@\n", vec![]).into(), format("%s@ @ @[<hv3>@;<3 3>@  \u{3b1}\u{3b2}\u{3b3}@]", vec!["x".into()]).into()]), 10, Some("Cardinality(S) abc\nfoo_bar \n\n=>foo_bar    Cardinality(S)\ny' TRUE\n    \n    \n    =>\n    \u{3b1}\u{3b2}\u{3b3}TRUECardinality(S)abc\n  Cardinality(S)y'=>\ny'x       \u{3b1}\u{3b2}\u{3b3}<<a, b>>\n")),
        (format("@\n%s@ \\A\u{2200}Cardinality(S)%a@;<0 3>@, TRUE@[<h4>@]@,abcabc\u{3b1}\u{3b2}\u{3b3}@\n", vec!["x".into(), format("@[<hv0>\u{3b1}\u{3b2}\u{3b3}@]@ @[<h0>%a@ y'@]@ foo_bar ", vec![format("@\n<<a, b>>@\n@[<v3>%a@ %s@\n\u{3b1}\u{3b2}\u{3b3}@ %aCardinality(S)@]", vec![format("x@\nx@\n", vec![]).into(), "bbbbbbbbbbb".into(), format("xTRUE\u{2200}@[<h4>foo_barzzzzzzzzzzzzzzzzzzzzzTRUE", vec![]).into()]).into()]).into()]), 0, Some("\nx \\A\u{2200}Cardinality(S)\n\u{3b1}\u{3b2}\u{3b3}\n\n<<a, b>>\nx\nx\n\nbbbbbbbbbbb\n\u{3b1}\u{3b2}\u{3b3}\nxTRUE\u{2200}\nfoo_barzzzzzzzzzzzzzzzzzzzzzTRUECardinality(S)\ny' foo_bar  TRUEabcabc\u{3b1}\u{3b2}\u{3b3}\n")),
        (format("@\n@[<hov1>@[<v4>%a@;<0 2>@]<<a, b>>@;<0 1>abc@ \\in\\A\\in", vec![format("%s\u{3b1}\u{3b2}\u{3b3}@.%s%a", vec!["x".into(), "abc".into(), format("@,%aabc%s", vec![format("abc%sCardinality(S)bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb@\nfoo_bar@[<v1>@]", vec!["TRUE".into()]).into(), "=>".into()]).into()]).into()]), 68, Some("\nx\u{3b1}\u{3b2}\u{3b3}\nabc\nabcTRUECardinality(S)bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\nfoo_barabc=><<a, b>>abc\n\\in\\A\\in")),
        (format("@ y'@ <<a, b>>@ =>@,@\n\\in@[<hov1>@.@]%a@,@ @\nTRUE@\n@[@ <<a, b>>y'@ abc", vec![format("@\n@[<hv2>@ bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbby'%s\u{3b1}\u{3b2}\u{3b3}@[<hov0>%szzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb@]@]", vec!["abc".into(), "Cardinality(S)".into()]).into()]), 35, Some(" y' <<a, b>> =>\n\n\\in\n\n\n  bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbby'abc\u{3b1}\u{3b2}\u{3b3}\n  Cardinality(S)zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\n\n\nTRUE\n <<a, b>>y' abc")),
        (format("\\A@ bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbTRUE%a@[<h2>zzzzzzzzzzzzzzzzzzzzzzzzzzzzzz@ @\nCardinality(S)@[<v4>@.y'Cardinality(S)@[@ =>@[<hv0>@]@]@]", vec![format(" @[<b4>@ zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz@.\u{3b1}\u{3b2}\u{3b3}@[<hv2>@;<0 0>@]", vec![]).into()]), 68, Some("\\A\nbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbTRUE \n                                               zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz\n\u{3b1}\u{3b2}\u{3b3}zzzzzzzzzzzzzzzzzzzzzzzzzzzzzz \n        Cardinality(S)\ny'Cardinality(S) =>")),
        (format("TRUE%s@[<h2>\u{2200}%s%a@]", vec!["y'".into(), "\u{3b1}\u{3b2}\u{3b3}".into(), format("@ y'=>", vec![]).into()]), 35, Some("TRUEy'\u{2200}\u{3b1}\u{3b2}\u{3b3} y'=>")),
        (format("%s@[<b4>abcy'@ %sCardinality(S)@;<0 2> %s<<a, b>>\u{3b1}\u{3b2}\u{3b3}@;<2 0><<a, b>>@]zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz@ @;<1 4>@ Cardinality(S)abcCardinality(S)TRUE@,<<a, b>>\u{3b1}\u{3b2}\u{3b3}@.@\n@\n@[<hv3> @]@\n\\in@ bbbbbbbbbbbbbbbbbbbbb@;<2 1>@ x@,\u{3b1}\u{3b2}\u{3b3} %a", vec!["\u{3b1}\u{3b2}\u{3b3}".into(), "\u{2200}".into(), "\u{3b1}\u{3b2}\u{3b3}".into(), format("@[<hv1>\\A%a%a@[<v0>@]=>y'@[%a@,\u{2200} @]@]", vec![format(" %a%sTRUE", vec![format("@[<h0>abc\\A@[<v1>%s@[<b4>Cardinality(S)abc%s@ @]@]@]", vec!["<<a, b>>".into(), "\\in".into()]).into(), "TRUE".into()]).into(), format("@[<b0>@]@\nCardinality(S)aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa@ @\n", vec![]).into(), format("@\n@[<hov1>@,@ \u{3b1}\u{3b2}\u{3b3}y'\\A\\in@]<<a, b>>@\n \u{3b1}\u{3b2}\u{3b3}", vec![]).into()]).into()]), 68, Some("\u{3b1}\u{3b2}\u{3b3}abcy' \u{2200}Cardinality(S) \u{3b1}\u{3b2}\u{3b3}<<a, b>>\u{3b1}\u{3b2}\u{3b3}  <<a, b>>zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz\n  Cardinality(S)abcCardinality(S)TRUE\n<<a, b>>\u{3b1}\u{3b2}\u{3b3}\n\n\n \n\\in bbbbbbbbbbbbbbbbbbbbb   x\n\u{3b1}\u{3b2}\u{3b3} \\A abc\\A<<a, b>>Cardinality(S)abc\\in TRUETRUE\n        Cardinality(S)aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n        \n        =>y'\n             \u{3b1}\u{3b2}\u{3b3}y'\\A\\in<<a, b>>\n             \u{3b1}\u{3b2}\u{3b3}\u{2200} ")),
        (format("@\n@;<0 1>foo_bar@[<hv4>@[<v3>%a@ TRUE\\A@[<hv4>@ @,<<a, b>>foo_bar@[<hv0>@]@]\u{2200}xy'\\A\u{2200}%s@ %a@ @]%s\\A@,%a@[<v0>@[%s@[<hv1>%a@]@[<hv2>\u{3b1}\u{3b2}\u{3b3}=>@]@]@]@]", vec![format("@ @\n@[<hov3>%a <<a, b>>@[<v2> @]", vec![format("@ @[<v0>@[\u{2200}@,@ abc@.@ @]@]", vec![]).into()]).into(), "bbbbbbbbbbbbbbbbbbbbbbb".into(), format("%sabc \u{3b1}\u{3b2}\u{3b3}@[<v1>@[@]@]", vec!["\\A".into()]).into(), "x".into(), format("@ abc %s@[<hv0>=>@ @]@ =>@[<hov1>@]", vec!["Cardinality(S)".into()]).into(), "x".into(), format("\\inCardinality(S)@;<2 0>", vec![]).into()]), 35, Some("\n\n foo_bar\n           \n            \u{2200} abc\n  <<a, b>>  TRUE\\A <<a, b>>foo_bar\u{2200}xy'\\A\u{2200}bbbbbbbbbbbbbbbbbbbbbbb\n\\Aabc \u{3b1}\u{3b2}\u{3b3} x\\A abc Cardinality(S)=> \n=>x\\inCardinality(S)  \u{3b1}\u{3b2}\u{3b3}=>")),
        (format("@ x@ x%a%aabc y'@;<2 2>%a \\A\\in", vec![format("@[<v3><<a, b>>=>\\Ax@ \u{2200}@]", vec![]).into(), format("\u{3b1}\u{3b2}\u{3b3}@,@ ", vec![]).into(), format("\u{2200}%a@\n", vec![format("@[<hov3>x\\A\\in\\Afoo_bar<<a, b>>aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa@[<h4>\u{2200}@[<v3> ", vec![]).into()]).into()]), 68, Some(" x x<<a, b>>=>\\Ax\n       \u{2200}\u{3b1}\u{3b2}\u{3b3} abc y'\n  \u{2200}x\\A\\in\\Afoo_bar<<a, b>>aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\u{2200} \n                                                                     \\A\\in")),
        (format("@,@\n@\nxx%s<<a, b>>@\n@\n<<a, b>>aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaay'@ \u{3b1}\u{3b2}\u{3b3} @[<b3>\\A\u{3b1}\u{3b2}\u{3b3}abc@;<3 4>%sCardinality(S)@]@[<hv0>@[<hv3>\\in@[<v3>\\in\u{3b1}\u{3b2}\u{3b3}@[<hov4>@]%sfoo_bar@[<hov3>%s%s@ @;<2 3>bbbbbbbbbbbbbbbbbbbbbb@[<v0>@[@]@ @ ", vec!["TRUE".into(), "y'".into(), "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".into(), "<<a, b>>".into(), "TRUE".into()]), 68, Some("\n\n\nxxTRUE<<a, b>>\n\n<<a, b>>aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaay'\n\u{3b1}\u{3b2}\u{3b3} \\A\u{3b1}\u{3b2}\u{3b3}abc   y'Cardinality(S)\\in\\in\u{3b1}\u{3b2}\u{3b3}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaafoo_bar\n                                           <<a, b>>TRUE \n                                                 bbbbbbbbbbbbbbbbbbbbbb\n                                              \n                                              \n                                              ")),
        (format("@[y'zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz%s\u{2200}x TRUE%a@]foo_bar", vec!["\\A".into(), format("@[<hov4>%a@;<2 4>TRUEy'x\u{3b1}\u{3b2}\u{3b3}@]\u{2200}", vec![format("Cardinality(S)@[@]", vec![]).into()]).into()]), 68, Some("y'zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz\\A\u{2200}x TRUE\nCardinality(S)  TRUEy'x\u{3b1}\u{3b2}\u{3b3}\u{2200}foo_bar")),
        (format("@,@ @\nxzzzzzzzzzzzzzzzzzzzzzzzzzzzz@ xx@ @[<b1>@] abc\u{3b1}\u{3b2}\u{3b3}Cardinality(S)=>@\n@[<hv0>\\A%s\u{2200}@, TRUE@]\u{3b1}\u{3b2}\u{3b3}@[<h3>@ %a@;<2 4> %s@[<h1>\\A%a@.@]@]\\A@\n@[<h4>@,<<a, b>>@]", vec!["\u{2200}".into(), format("\\A@[@ @\n@ %s\u{3b1}\u{3b2}\u{3b3}@]=>TRUE", vec!["Cardinality(S)".into()]).into(), "abc".into(), format("@[<hov4>@]", vec![]).into()]), 0, Some(" \nxzzzzzzzzzzzzzzzzzzzzzzzzzzzz xx\n abc\u{3b1}\u{3b2}\u{3b3}Cardinality(S)=>\n\\A\u{2200}\u{2200} TRUE\u{3b1}\u{3b2}\u{3b3}\n \\A \n Cardinality(S)\u{3b1}\u{3b2}\u{3b3}=>TRUE   abc\\A\n\\A\n<<a, b>>")),
        (format("%a@[<hv4>@]@,bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb<<a, b>> ", vec![format("=>@ Cardinality(S)\u{3b1}\u{3b2}\u{3b3}@.x \\in@ \u{2200}", vec![]).into()]), 68, Some("=>\nCardinality(S)\u{3b1}\u{3b2}\u{3b3}\nx \\in \u{2200}\nbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb<<a, b>> ")),
        (format("%s=>@ =>\\iny' @,abc@[<h0>@,\u{3b1}\u{3b2}\u{3b3}=>\u{2200}@[<v1>@[<hov4>\\in@ @]@]@]", vec!["Cardinality(S)".into()]), 35, Some("Cardinality(S)=> =>\\iny' \nabc\u{3b1}\u{3b2}\u{3b3}=>\u{2200}\\in ")),
        (format("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaTRUE@\n@\n@ aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa@ y'abc@;<1 4>@\ny'@;<1 1>@[<hv3>@ @]@.", vec![]), 0, Some("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaTRUE\n\n aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa y'abc \ny'\n \n")),
        (format("bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbfoo_bar\\A%s@\n@[@]@\n@\nTRUE\\A@ @[@]", vec!["TRUE".into()]), 68, Some("bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbfoo_bar\\ATRUE\n\n\nTRUE\\A\n")),
        (format("@[<h4>@[<hv0>@ \\A@ @ @ \\A@]@ %a@ @[<v1>\\A%s@.@]@;<0 0>@,@[@ @]@ @ y'<<a, b>>@;<1 0>@.@;<3 0>@]", vec![format("foo_bar@[<h2>@[<hv4>@;<0 2>%afoo_bar", vec![format("\u{2200}@\n@[%a@]", vec![format("@[@]\u{2200}@;<0 4>%s@\n@\n%s@,\u{3b1}\u{3b2}\u{3b3}", vec!["aaaaaaaaaaaaaaaaa".into(), "foo_bar".into()]).into()]).into()]).into(), "foo_bar".into()]), 68, Some(" \\A   \\A foo_bar\u{2200}\n                    \u{2200}aaaaaaaaaaaaaaaaa\n                    \n                    foo_bar\u{3b1}\u{3b2}\u{3b3}foo_bar \\Afoo_bar\n   y'<<a, b>>\n\n\n")),
        (format("@ @ @,%a@,y'@ @\n@[<hv0>@\n@]@[<v3>\\in@;<0 0> @ @ @[<h4>@ @]@]", vec![format("\u{2200}@\n@[<v2>@[<b2>=>%a@[@ @,@]@]", vec![format("@;<3 4>@ @\n%saaaaaaaaaaaaaaaaaaa", vec!["TRUE".into()]).into()]).into()]), 35, Some("  \n\u{2200}\n=>    \n  TRUEaaaaaaaaaaaaaaaaaaa \n  y'\n  \n  \n  \\in\n      \n     \n      ")),
        (format("@,%s%s@\n@[TRUE @ @;<0 2>@,abc@]\u{3b1}\u{3b2}\u{3b3}%a@,Cardinality(S)zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzabc%a<<a, b>>@[<h2>@ @ \\Ay'<<a, b>>@ \\in@ @ %a@[<hov2>@]\u{3b1}\u{3b2}\u{3b3}@[<hov1>@;<3 0>@ %s@]@]", vec!["<<a, b>>".into(), "y'".into(), format("x@ @.@[<v3>%a@ Cardinality(S)@[<b3>", vec![format("@[<h3>@;<3 1>@[<hv3>@]@]", vec![]).into()]).into(), format("\\in%a@ ", vec![format("\\A%a%s@\n", vec![format("@\n@ TRUE@ zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz@\nfoo_barx@ ", vec![]).into(), "x".into()]).into()]).into(), format("Cardinality(S)@ ", vec![]).into(), "\\in".into()]), 10, Some("<<a, b>>y'\nTRUE  abc\u{3b1}\u{3b2}\u{3b3}x\n\n   \n   Cardinality(S)\n   Cardinality(S)zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzabc\\in\\A\n       TRUE zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz\n      foo_barx x\n       <<a, b>>\n        \\Ay'<<a, b>> \\in  Cardinality(S) \u{3b1}\u{3b2}\u{3b3}    \\in")),
        (format("\u{2200}%a\\A@[<hov0>zzzzzzzzzzzzzzzzzzz@]@\n@ abc@[<hv3>%a%s@[<b4>%aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa@,x %s@,\u{3b1}\u{3b2}\u{3b3}@]@ \\AxTRUE@ @ \u{2200}@]\\inx\u{3b1}\u{3b2}\u{3b3}", vec![format("y'@, x@ ", vec![]).into(), format("@\nbbbbbbbbbbbbbbbbb@ ", vec![]).into(), "Cardinality(S)".into(), format("@\n%s=>\\in@\n", vec!["aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".into()]).into(), "=>".into()]), 68, Some("\u{2200}y' x \\Azzzzzzzzzzzzzzzzzzz\n\nabc\n      bbbbbbbbbbbbbbbbb\n      Cardinality(S)\n                        aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa=>\\in\n                        aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaax =>\n                        \u{3b1}\u{3b2}\u{3b3}\n      \\AxTRUE\n      \n      \u{2200}\\inx\u{3b1}\u{3b2}\u{3b3}")),
        (format("@\n%s@ %s@ \\A\u{2200}@ @,%a@\n@[@]@ @\nfoo_bar@ Cardinality(S)@\n@[<h1>@ bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb@ %s@;<2 2>@]foo_barabcCardinality(S)@ \u{3b1}\u{3b2}\u{3b3}", vec!["foo_bar".into(), "abc".into(), format("=>@\n@,@;<3 4>@;<2 2>@[<h3>@;<2 4>\u{2200}%s%a@]", vec!["abc".into(), format("<<a, b>>%a@[<b3>\u{3b1}\u{3b2}\u{3b3}x@,@[<hov0>abcfoo_bar@;<3 3>@]@[<h2>", vec![format("%s@\n@ @[<b0>\u{3b1}\u{3b2}\u{3b3}x =>Cardinality(S)<<a, b>>@]", vec!["x".into()]).into()]).into()]).into(), "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".into()]), 35, Some("\nfoo_bar abc \\A\u{2200} =>\n   \n    \u{2200}abc<<a, b>>x\n      \u{3b1}\u{3b2}\u{3b3}x =>Cardinality(S)<<a, b>>\u{3b1}\u{3b2}\u{3b3}x\n                                   abcfoo_bar   \n                                   \n                                    \n                                   foo_bar\n                                   Cardinality(S)\n                                    bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa  foo_barabcCardinality(S)\n                                   \u{3b1}\u{3b2}\u{3b3}")),
        (format("@  @[<hv0>@ @ @[<v3>@]@\n<<a, b>>abc@,@[<hv3>Cardinality(S)@.@ @]@]", vec![]), 68, Some("\n   \n <<a, b>>abcCardinality(S)\n\n")),
        (format("@[<v0>@ @ bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb%a\\iny'x@,foo_bar<<a, b>>@[<hov2>bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\u{3b1}\u{3b2}\u{3b3}@]@]@;<3 3>@[@ @]", vec![format("x@[<v4>@[ x %a%a@]", vec![format("@ %szzzzzzzzzzzzzzz\\A@\n@\n\\A@ @\n@[<hv1>@]", vec!["TRUE".into()]).into(), format("@;<1 2>TRUE", vec![]).into()]).into()]), 68, Some("\n\nbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbx\n x  TRUEzzzzzzzzzzzzzzz\\A\n\n\\A \n TRUE\\iny'x\n    foo_bar<<a, b>>bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\u{3b1}\u{3b2}\u{3b3}\n    ")),
        (format("@ @[<hov2>xzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz%s\u{2200}@]@\nzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz@\n@\n@[<h3> TRUE%a@]@\nx=>@ @ @[<b3>%aTRUE@;<1 3>abc@[<hv1>\\in%a\\in@]@]x@[<b4>@]Cardinality(S)%a@,@\nfoo_bar", vec!["\\A".into(), format("@ @[<hov4>\u{3b1}\u{3b2}\u{3b3}@ @]abc@ @,y'TRUE\u{3b1}\u{3b2}\u{3b3}\\in\u{2200}", vec![]).into(), format("Cardinality(S)@[@]@\n\\in", vec![]).into(), format("@[<<a, b>>\\in\\A%sCardinality(S)@;<2 1>TRUE@\n%s@]@[<hv2>y'@]", vec!["y'".into(), "=>".into()]).into(), format("@[<hov0>%a@]@ bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\\A=><<a, b>><<a, b>>\u{3b1}\u{3b2}\u{3b3}abc =>", vec![format("@\naaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", vec![]).into()]).into()]), 0, Some("\nxzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz\\A\u{2200}\nzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz\n\n TRUE \u{3b1}\u{3b2}\u{3b3} abc y'TRUE\u{3b1}\u{3b2}\u{3b3}\\in\u{2200}\nx=> \nCardinality(S)\n\\inTRUE abc\\in>\\in\\Ay'Cardinality(S)  TRUE\n=>y'\\inx\nCardinality(S)\n\naaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\nbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\\A=><<a, b>><<a, b>>\u{3b1}\u{3b2}\u{3b3}abc =>\n\nfoo_bar")),
        (format("\u{2200}@[<b0>bbbbbbbbbbbbbbbbbbbbbbb@ aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaafoo_bar@[<v4>@]@.@ <<a, b>>@,abcCardinality(S)@;<1 2>%s\\A@\n@[<h3>@[<v2>@ %s@,", vec!["y'".into(), "bbbbbbbbbbbbbbbbbbbbbbbbbbbb".into()]), 35, Some("\u{2200}bbbbbbbbbbbbbbbbbbbbbbb\n   aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaafoo_bar\n   \n <<a, b>>abcCardinality(S)\n  y'\\A\n\n  bbbbbbbbbbbbbbbbbbbbbbbbbbbb\n  ")),
        (format("<<a, b>>@\nx\\in@\nabc@ @\n%s@\n@ @ foo_bar=>@[<b1>@]", vec!["y'".into()]), 10, Some("<<a, b>>\nx\\in\nabc \ny'\n \nfoo_bar=>")),
        (format("@ %s@[<hv2>@,<<a, b>>@  @]", vec!["foo_bar".into()]), 10, Some("\nfoo_bar<<a, b>>  ")),
        (format("%a=>@,@,=>\u{2200}\u{3b1}\u{3b2}\u{3b3}@;<0 4>foo_bar@,", vec![format("\\inzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz<<a, b>>@ y'@ @[<hv1>@;<1 3>aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa@ @.@]", vec![]).into()]), 68, Some("\\inzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz<<a, b>>\ny'\n aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa \n=>=>\u{2200}\u{3b1}\u{3b2}\u{3b3}foo_bar\n")),
        (format(" TRUE\u{3b1}\u{3b2}\u{3b3}\\A@[<v4>@ \\AxTRUECardinality(S)\\A=>@ @]%s=>@[%sbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb<<a, b>>Cardinality(S)@[<h2>abc@;<0 0>xx\\A\u{2200}@]@;<1 0>@ @\n@ %s@ @[<h3>@ %a%a@;<2 2> =>TRUE\u{3b1}\u{3b2}\u{3b3}@]@]", vec!["<<a, b>>".into(), "\\A".into(), "zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz".into(), format("%a@ @ @;<1 2>@\n<<a, b>>@ ", vec![format("\\iny' @[<hv1>@]@\n@\nfoo_bar @ <<a, b>>@ ", vec![]).into()]).into(), format("\\in@\n@;<2 0>\\in", vec![]).into()]), 35, Some(" TRUE\u{3b1}\u{3b2}\u{3b3}\\A\n                 \\AxTRUECardinality(S)\\A=>\n                 <<a, b>>=>\\Abbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb<<a, b>>Cardinality(S)\n                           abcxx\\A\u{2200}  \n                            zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz\n                            \\iny' \n                              \n                              foo_bar  <<a, b>>    \n                              <<a, b>> \\in\n                                \\in   =>TRUE\u{3b1}\u{3b2}\u{3b3}")),
        (format("@.%s\u{3b1}\u{3b2}\u{3b3}@[TRUE@[<h0>@ x@ aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa@ @ @]abc@]\u{3b1}\u{3b2}\u{3b3}Cardinality(S)foo_bar@ @[<hv0>%a@ @[<h0>\\A@ @]@]", vec!["x".into(), format("@;<3 2>%a@\n<<a, b>>@\n @[<b2>\u{3b1}\u{3b2}\u{3b3}Cardinality(S)@[<hv3><<a, b>>@]", vec![format("abc %a%a@ @ @[%a@]", vec![format("@ <<a, b>>", vec![]).into(), format("@ @;<1 1>\\A@ @ %s@[<v4>@]@ %s@ @\n", vec!["foo_bar".into(), "foo_bar".into()]).into(), format("@,%saaaaaaaaaaaaaaaaaaaaaaa", vec!["\u{3b1}\u{3b2}\u{3b3}".into()]).into()]).into()]).into()]), 35, Some("\nx\u{3b1}\u{3b2}\u{3b3}TRUE x aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa  abc\u{3b1}\u{3b2}\u{3b3}Cardinality(S)foo_bar\n\n  abc \n<<a, b>>\n\n \\A\n\nfoo_bar\nfoo_bar\n\n\n\n\u{3b1}\u{3b2}\u{3b3}aaaaaaaaaaaaaaaaaaaaaaa\n<<a, b>>\n \u{3b1}\u{3b2}\u{3b3}Cardinality(S)<<a, b>> \\A ")),
        (format("%a@\n@\n@;<0 4>@;<1 1>aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa@[<h2>%a@[<h4>%afoo_bar%a@ @ abc@[<v1>TRUE%sCardinality(S)@,\u{2200}foo_bar@[<hov0>\\in\u{3b1}\u{3b2}\u{3b3}@;<3 0>@]@]@]@]", vec![format("\u{3b1}\u{3b2}\u{3b3}@,<<a, b>>\\A%a%a%a%abbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb", vec![format("%a@[<b1>@ zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz@]@ @;<1 4> %a@,", vec![format("@[<hov1>@ @]@\n@ @ ", vec![]).into(), format("%s@ @.@ zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz@ \\A@ @\n@ @\n", vec!["foo_bar".into()]).into()]).into(), format("@ foo_bar\\A@,<<a, b>><<a, b>>@ Cardinality(S)abc", vec![]).into(), format("%s@[<hov0>@]", vec!["abc".into()]).into(), format("@[<b0>y'abc@ @;<2 2>y'@ %sbbbbbbbbbbbbbbbbbbbbbbbbbbbbb@ @]", vec!["x".into()]).into()]).into(), format("%aCardinality(S)%saaaaaaaaaaaaaaaaaaaaa@ ", vec![format("@[<h4>foo_bary'%a@]%s", vec![format("<<a, b>>x<<a, b>>@\n @;<0 0>x\\A%s", vec!["abc".into()]).into(), "x".into()]).into(), "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb".into()]).into(), format("@\n@ ", vec![]).into(), format("bbbbbbbbbb%s\\in<<a, b>>%sabc @,%s", vec!["Cardinality(S)".into(), "<<a, b>>".into(), "=>".into()]).into(), "=>".into()]), 68, Some("\u{3b1}\u{3b2}\u{3b3}<<a, b>>\\A \n   zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz   foo_bar\n\n zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz \\A \n \n foo_bar\\A<<a, b>><<a, b>>\nCardinality(S)abcabcy'abc   y' xbbbbbbbbbbbbbbbbbbbbbbbbbbbbb bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\n\n\n aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaafoo_bary'<<a, b>>x<<a, b>>\n                                                            x\\AabcxCardinality(S)bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbaaaaaaaaaaaaaaaaaaaaa \n                                                                     foo_barbbbbbbbbbbCardinality(S)\\in<<a, b>><<a, b>>abc =>  abcTRUE=>Cardinality(S)\n                                                                    \u{2200}foo_bar\\in\u{3b1}\u{3b2}\u{3b3}\n                                                                    ")),
        (format("@\n@[<h4>\\A@,@]\\A%sCardinality(S)@ foo_bar@.%s%a<<a, b>>foo_barCardinality(S)=>%s\u{3b1}\u{3b2}\u{3b3}%sbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb@ @\ny'@\n", vec!["aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".into(), "\\A".into(), format("\\inabc", vec![]).into(), "\u{2200}".into(), "<<a, b>>".into()]), 0, Some("\n\\A\\AaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaCardinality(S)\nfoo_bar\n\\A\\inabc<<a, b>>foo_barCardinality(S)=>\u{2200}\u{3b1}\u{3b2}\u{3b3}<<a, b>>bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\n\ny'\n")),
        (format("TRUE@[<h2>@[<b1>@ @[<b3>%a@[<v1>abc@]@[<b3>zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz@[<b2>@ @]", vec![format("@\nx@\n@[<h2>%s@;<1 3>@]\\in@ TRUE", vec!["x".into()]).into()]), 68, Some("TRUE \n        x\n        x \\in TRUEabczzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz ")),
        (format("@;<3 2> @\n@,\u{2200}@;<3 2>\u{3b1}\u{3b2}\u{3b3}<<a, b>>\u{3b1}\u{3b2}\u{3b3}Cardinality(S)Cardinality(S)@ @[<h4>@ <<a, b>> xCardinality(S)<<a, b>>\\A@,@]foo_bar@,@\ny'abc\\A@[<h1>abc\u{2200}=>@]foo_bar@;<0 0>@;<0 4>@ ", vec![]), 68, Some("    \n\u{2200}   \u{3b1}\u{3b2}\u{3b3}<<a, b>>\u{3b1}\u{3b2}\u{3b3}Cardinality(S)Cardinality(S)\n <<a, b>> xCardinality(S)<<a, b>>\\Afoo_bar\ny'abc\\Aabc\u{2200}=>foo_bar\n")),
        (format("@ Cardinality(S)@,@ %a@,@ \u{2200}@ @[<b3>@ @ <<a, b>>foo_bar@ @ @] @ %a@\n@[<v4>%a", vec![format("@\n@\n\\in@,@ \u{3b1}\u{3b2}\u{3b3}", vec![]).into(), format("%a\\in", vec![format("\u{3b1}\u{3b2}\u{3b3}x%a@\n", vec![format("@[@]", vec![]).into()]).into()]).into(), format("\u{2200}@\naaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\\in%s", vec!["\\in".into()]).into()]), 0, Some(" Cardinality(S) \n\n\\in \u{3b1}\u{3b2}\u{3b3} \u{2200} \n  <<a, b>>foo_bar   \n\u{3b1}\u{3b2}\u{3b3}x\n\n\\in\n\u{2200}\naaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\\in\\in")),
        (format("@\n@;<2 1>Cardinality(S)@ @ =>@ @;<3 1>@[<b4>@ \\ATRUE@]TRUE=>\u{3b1}\u{3b2}\u{3b3}@\n@\n\\in@[<v3>@ <<a, b>>@]@ @\n", vec![]), 68, Some("\n  Cardinality(S)  =>     \\ATRUETRUE=>\u{3b1}\u{3b2}\u{3b3}\n\n\\in\n      <<a, b>>\n\n")),
        (format("\\in@[@;<3 0> @[<v4>@]xfoo_barx@ @;<2 1>@ %a  @[@,Cardinality(S)foo_barTRUE@]\u{3b1}\u{3b2}\u{3b3}\u{3b1}\u{3b2}\u{3b3}%a@ @;<0 4>@[<v4>@[<v0>%a%s@[aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaCardinality(S)foo_bar@]@]@]@]", vec![format("@\nTRUE@[<hv3>@;<0 2>@ @]", vec![]).into(), format("foo_barxfoo_bar@ ", vec![]).into(), format("@ @\n=>foo_bar\\in@[@[@]@]", vec![]).into(), "foo_bar".into()]), 68, Some("\\in    xfoo_barx   \n   \n   TRUE   Cardinality(S)foo_barTRUE\u{3b1}\u{3b2}\u{3b3}\u{3b1}\u{3b2}\u{3b3}foo_barxfoo_bar  \n       \n       \n       =>foo_bar\\infoo_baraaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaCardinality(S)foo_bar")),
        (format("@ %a\\in%s@\n\u{2200}foo_bar@[@[<v2>x@]@]", vec![format("@ @ abc@[<v2>@[%a@]@]", vec![format("@[<v3>aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaafoo_barabc@]", vec![]).into()]).into(), "TRUE".into()]), 68, Some("  \nabcaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaafoo_barabc\\inTRUE\n\u{2200}foo_barx")),
        (format("\\in@\n@[@ @ @\nTRUE@[<hov3>@;<2 0>x\u{3b1}\u{3b2}\u{3b3}@]@]@ xTRUE@ TRUE=>=>%a", vec![format("@ @\n@[<hv0>\\in%s@[@ @[<hv0><<a, b>>%s@]foo_bar@]@]", vec!["\\in".into(), "x".into()]).into()]), 35, Some("\\in\n  \nTRUE  x\u{3b1}\u{3b2}\u{3b3} xTRUE TRUE=>=>\n\n\\in\\in <<a, b>>xfoo_bar")),
        (format("@[<b4>TRUE@[<h0>@[@[<h2>@]TRUE\u{3b1}\u{3b2}\u{3b3}=>y'@[<hov2>@]@]Cardinality(S)bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbfoo_bar\\A@,x@ @[<h1>@,\u{3b1}\u{3b2}\u{3b3}%aCardinality(S)@ =><<a, b>>abcfoo_bar@;<0 1>@]@;<3 3>@]@]", vec![format("@ @,@\n%a\\A\\in", vec![format("@;<3 0> \\A@\n@ \u{3b1}\u{3b2}\u{3b3}@ ", vec![]).into()]).into()]), 68, Some("TRUETRUE\u{3b1}\u{3b2}\u{3b3}=>y'Cardinality(S)bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbfoo_bar\\Ax \u{3b1}\u{3b2}\u{3b3} \n                                                                        \\A\n                                                                     \u{3b1}\u{3b2}\u{3b3} \\A\\inCardinality(S) =><<a, b>>abcfoo_bar   ")),
        (format("@\n@ @\naaaaaaaaaaaaaaaaaaaaaaa@,@ @\n=>@.zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz@\n@\n@,<<a, b>>@ abcTRUE@[<b4>@ x\u{2200}=>@[<hov0>foo_barfoo_bar@]@]", vec![]), 0, Some("\n \naaaaaaaaaaaaaaaaaaaaaaa\n\n=>\nzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz\n\n<<a, b>>\nabcTRUE\n x\u{2200}=>foo_barfoo_bar")),
        (format("\u{3b1}\u{3b2}\u{3b3}@ =>@\n\\in@[<hov1>bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb=>Cardinality(S)@ ", vec![]), 68, Some("\u{3b1}\u{3b2}\u{3b3}\n=>\n\\inbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb=>Cardinality(S) ")),
        (format("\\in=>foo_bar@\n%s%a@[@ @;<0 4>@,<<a, b>>TRUE@]@\n@[<hv2>\u{2200}foo_bar@]", vec!["\\in".into(), format("@[<b2>@]@[<hov2>\\in%a@ TRUE<<a, b>>x", vec![format("@\n<<a, b>> y'@ \u{3b1}\u{3b2}\u{3b3}", vec![]).into()]).into()]), 10, Some("\\in=>foo_bar\n\\in\\in\n     <<a, b>> y' \u{3b1}\u{3b2}\u{3b3} TRUE<<a, b>>x <<a, b>>TRUE\n     \u{2200}foo_bar")),
        (format("@[<h2>@]\\Afoo_bar=><<a, b>>@ ", vec![]), 68, Some("\\Afoo_bar=><<a, b>>\n")),
        (format("@ <<a, b>>\u{2200}%a@ @,@\n=>zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz@\n%sy'\u{2200}@\n@;<3 1>@;<0 1>y'@ @\n@ @  foo_bar@ \u{3b1}\u{3b2}\u{3b3}x%s@ @,", vec![format("@ \u{3b1}\u{3b2}\u{3b3}@\n@\n\u{3b1}\u{3b2}\u{3b3}@ @\n=>%a@ ", vec![format("x@ @;<2 4>@[<hv0>\u{3b1}\u{3b2}\u{3b3}@]@ <<a, b>>\u{2200}<<a, b>>@[<h4> @]", vec![]).into()]).into(), "y'".into(), "=>".into()]), 0, Some(" <<a, b>>\u{2200} \u{3b1}\u{3b2}\u{3b3}\n\n\u{3b1}\u{3b2}\u{3b3} \n=>x   \n\u{3b1}\u{3b2}\u{3b3} <<a, b>>\u{2200}<<a, b>>\n   \n=>zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz\ny'y'\u{2200}\n   y' \n   foo_bar \u{3b1}\u{3b2}\u{3b3}x=> \n")),
        (format("%sfoo_bar@,@;<1 1>@ @\n@,\\A@,foo_barx@[bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb@ @,\u{2200}@ \\in @ \u{3b1}\u{3b2}\u{3b3}=>\\A@;<1 3>@;<0 3>\u{2200}@[<h4>@]%s@[<h2>TRUE\u{3b1}\u{3b2}\u{3b3}=>xCardinality(S)%a@\n\\in@]@]", vec!["abc".into(), "\\A".into(), format("@;<2 1>@[<hov4>@[<h2>\u{3b1}\u{3b2}\u{3b3}%afoo_bar@]y'Cardinality(S)@;<1 4>%a@]", vec![format("@,<<a, b>>@\n\\A@ @\n=>@[<hv0>", vec![]).into(), format("@,@\n\u{3b1}\u{3b2}\u{3b3}y'%s\u{3b1}\u{3b2}\u{3b3}%afoo_barTRUE", vec!["foo_bar".into(), format(" y'@[<h4>@ @ abc@;<0 2>%sy'%s@ @]", vec!["\\A".into(), "y'".into()]).into()]).into()]).into()]), 10, Some("abcfoo_bar  \n\\A\nfoo_barxbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\n        \u{2200} \\in  \u{3b1}\u{3b2}\u{3b3}=>\\A \n          \u{2200}\n        \\ATRUE\u{3b1}\u{3b2}\u{3b3}=>xCardinality(S)  \u{3b1}\u{3b2}\u{3b3}<<a, b>>\n          \\A \n          =>foo_bary'Cardinality(S) \n          \u{3b1}\u{3b2}\u{3b3}y'foo_bar\u{3b1}\u{3b2}\u{3b3} y'  abc\\Ay'y' foo_barTRUE\n          \\in")),
        (format("@ %s@\n@ @ Cardinality(S)@;<2 1>@ \u{2200}@\n@ x@\n@\n@ @\n%a%a", vec!["=>".into(), format("\u{2200}@ @[<hov1>@ %s%s@]@ @\n@ @[<h2>@]", vec!["x".into(), "\u{3b1}\u{3b2}\u{3b3}".into()]).into(), format("\u{3b1}\u{3b2}\u{3b3}@;<2 4>@[<hov2>%s@ \u{2200}@]", vec!["\u{3b1}\u{3b2}\u{3b3}".into()]).into()]), 35, Some(" =>\n  Cardinality(S)   \u{2200}\n x\n\n \n\u{2200}  x\u{3b1}\u{3b2}\u{3b3} \n \u{3b1}\u{3b2}\u{3b3}\n    \u{3b1}\u{3b2}\u{3b3} \u{2200}")),
        (format("@,\u{2200}@\nCardinality(S)@[<v4>@ @ @,=>@]@[<h1>@]@[<hv3>\u{3b1}\u{3b2}\u{3b3}zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz@,@ =>@ @,@ @ @,@ @]@\n  %s%s\u{3b1}\u{3b2}\u{3b3}\\inabc@\n@[<v4>%s@]", vec!["=>".into(), "\\in".into(), "=>".into()]), 35, Some("\n\u{2200}\nCardinality(S)\n                  \n                  \n                  =>\u{3b1}\u{3b2}\u{3b3}zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz\n                       \n                       =>\n                       \n                       \n                       \n                       \n                       \n                       \n  =>\\in\u{3b1}\u{3b2}\u{3b3}\\inabc\n=>")),
        (format("@\n@[<hv4>@;<0 1>@[<b0>@[<v0>@]@] @,<<a, b>>@\n@[<h0>abc@;<1 3>%s\u{2200}Cardinality(S)@]%sy'@[<h2>@;<0 4>\\in\\A@,%a@[<b0>@]@]@,x@.@]zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz@;<3 3>", vec!["\u{3b1}\u{3b2}\u{3b3}".into(), "\\in".into(), format("zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzfoo_bar@[@ %s@]@[<v2>@\n@ @]", vec!["\\A".into()]).into()]), 10, Some("\n\n      \n    <<a, b>>\n    abc \u{3b1}\u{3b2}\u{3b3}\u{2200}Cardinality(S)\\iny'\n    \\in\\Azzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzfoo_bar \\A\n          \n          \n    x\nzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz\n   ")),
        (format("@ abc\u{2200}@\n@;<1 0>%s\u{2200}@ Cardinality(S)@ @\n%s@[<hov1>@ TRUE@,@[<h3>y'=>@]foo_bar@] \\A%a@\nTRUE%s@[<hv1>TRUE%a\u{3b1}\u{3b2}\u{3b3}@[<v3>@]@]", vec!["<<a, b>>".into(), "<<a, b>>".into(), format("@\nx@ @ bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb%s%s @ @.TRUE", vec!["foo_bar".into(), "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".into()]).into(), "\u{3b1}\u{3b2}\u{3b3}".into(), format("@ @[@[<hov4>\\Afoo_bar@]@]", vec![]).into()]), 68, Some(" abc\u{2200}\n <<a, b>>\u{2200} Cardinality(S) \n<<a, b>> TRUEy'=>foo_bar \\A\nx \nbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbfoo_baraaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa \n\nTRUE\nTRUE\u{3b1}\u{3b2}\u{3b3}TRUE \\Afoo_bar\u{3b1}\u{3b2}\u{3b3}")),
        (format("foo_bar@\n\\in@\n%s@. @[<hv3>TRUE@,%a%ay'@]\\in@[<hv2>x@,@.<<a, b>>@[<b0>y'%afoo_bar @;<0 0> @[<hv1>foo_bar@]@]@]", vec!["x".into(), format("%a@.", vec![format("@;<1 1>y' @  @\n@ \\A@;<1 0>@[<hov3>@]@ ", vec![]).into()]).into(), format("%a@;<1 2>@ aaaaaaaaaaaaaaaa", vec![format("@;<0 3>y'@\n@[<b1>\u{3b1}\u{3b2}\u{3b3}", vec![]).into()]).into(), format("\u{3b1}\u{3b2}\u{3b3}xx%s@ Cardinality(S)\\in\\A@,%s", vec!["\\in".into(), "=>".into()]).into()]), 35, Some("foo_bar\n\\in\nx\n TRUE y'   \n     \\A  \n\n   y'\n\u{3b1}\u{3b2}\u{3b3}  aaaaaaaaaaaaaaaay'\\inx\n<<a, b>>y'\u{3b1}\u{3b2}\u{3b3}xx\\in Cardinality(S)\\in\\A=>foo_bar  foo_bar")),
        (format("x@\ny'@;<1 0>%a%s@;<2 1>@ @[@,@ @ %aCardinality(S)@[<v4>@;<1 3>@]Cardinality(S)%s@]", vec![format("%s@ @\nbbbbbbbbbbbbbbbbbbbbbbb@\nzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz@;<3 2>%a@\nTRUE<<a, b>>", vec!["foo_bar".into(), format("@ @ ", vec![]).into()]).into(), "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".into(), format(" %a@ %aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\\A@[<hov2>abcy'TRUE@[<b3>\\in@]@]", vec![format("@[\u{3b1}\u{3b2}\u{3b3}abc\\in<<a, b>>@;<0 3>\\inCardinality(S)@]@\n@[<hv4>Cardinality(S)@]", vec![]).into(), format("y'@ %a<<a, b>>\u{3b1}\u{3b2}\u{3b3}@;<3 1>", vec![format("@ @,", vec![]).into()]).into()]).into(), "Cardinality(S)".into()]), 68, Some("x\ny' foo_bar\n\nbbbbbbbbbbbbbbbbbbbbbbb\nzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz    \n\nTRUE<<a, b>>aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n \n   \u{3b1}\u{3b2}\u{3b3}abc\\in<<a, b>>\\inCardinality(S)\nCardinality(S) y'  <<a, b>>\u{3b1}\u{3b2}\u{3b3}\n aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\\Aabcy'TRUE\\inCardinality(S)\n\n       Cardinality(S)Cardinality(S)")),
        (format("@[<hv3>@ zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz@ @[<v4>@  %a\u{2200} <<a, b>>@;<2 3>@,<<a, b>>%afoo_bar foo_bar@]@ @ @ @ @,%s@ %sx@]@ y'@,\u{2200}%a\\A y'Cardinality(S)<<a, b>>", vec![format("@ =>\u{2200}", vec![]).into(), format("@,@ @;<3 2>%s@,@ ", vec!["\u{3b1}\u{3b2}\u{3b3}".into()]).into(), "\\A".into(), "TRUE".into(), format("%a@[<hov1>@,@]", vec![format("@\nfoo_bar@\n\u{3b1}\u{3b2}\u{3b3}\\ATRUE@;<3 1>", vec![]).into()]).into()]), 68, Some("\n   zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz\n   \n        \n       =>\u{2200}\u{2200} <<a, b>>\n          \n       <<a, b>>\n       \n       \n         \u{3b1}\u{3b2}\u{3b3}\n       \n       foo_bar foo_bar\n   \n   \n   \n   \n   \\A\n   TRUEx y'\u{2200}\nfoo_bar\n\u{3b1}\u{3b2}\u{3b3}\\ATRUE\n \\A y'Cardinality(S)<<a, b>>")),
        (format("@ abc@[<hov0>@;<3 1>@[<hv3>\u{3b1}\u{3b2}\u{3b3}@[<hov3>y'@]bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb@ @ <<a, b>>@,@[<h4>@\n @ bbbbbbbbbbbbbbbbbbbbbbbbb@  @,\\in%a@,@;<0 4>zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz", vec![format("@[<hov3>Cardinality(S)@]aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa@\n\\A@\n\\in@ @\n", vec![]).into()]), 68, Some("\nabc\n    \u{3b1}\u{3b2}\u{3b3}y'bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\n       \n       <<a, b>>\n       \n             bbbbbbbbbbbbbbbbbbbbbbbbb  \\inCardinality(S)aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n           \\A\n           \\in \n           zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz")),
        (format("%a  @;<2 1>\u{2200}@ ", vec![format("TRUE@\n@,TRUEfoo_bar @\n@ @ @ <<a, b>>@\n", vec![]).into()]), 0, Some("TRUE\nTRUEfoo_bar \n   <<a, b>>\n    \u{2200}\n")),
        (format("@[<hov0>Cardinality(S)<<a, b>><<a, b>>@ @[<v3>@,%a@[ \\in@[@;<3 2>xCardinality(S)x<<a, b>>y'@]@]foo_bar\\A@\n\u{2200}zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzabc@;<0 0>y'zzzzzzzzzzzzzzzzzz@ @ @ @ =>@ @ foo_bar@\n%aTRUE@]@,%s@ @]", vec![format("Cardinality(S)%s", vec!["\u{3b1}\u{3b2}\u{3b3}".into()]).into(), format("bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbby'@ aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa%a%s@[<hv0>@]", vec![format("@;<1 2>@ Cardinality(S)@ @.@\n@[<hv3>%a", vec![format(" abcy'@ <<a, b>>@[<v0>@,TRUE@ zzzzzzzzzzzzzzzzzzzzzzzzz@ @]", vec![]).into()]).into(), "\u{2200}".into()]).into(), "<<a, b>>".into()]), 68, Some("Cardinality(S)<<a, b>><<a, b>>\n\n   Cardinality(S)\u{3b1}\u{3b2}\u{3b3} \\in   xCardinality(S)x<<a, b>>y'foo_bar\\A\n   \u{2200}zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzabc\n   y'zzzzzzzzzzzzzzzzzz\n   \n   \n   \n   =>\n   \n   foo_bar\n   bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbby'\n   aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n     \n   Cardinality(S)\n   \n\n abcy' <<a, b>>\n               TRUE\n               zzzzzzzzzzzzzzzzzzzzzzzzz\n               \u{2200}TRUE<<a, b>>\n")),
        (format("@[<v1>\\A@ \u{2200}@ %a@]x%a", vec![format("%s@[<h2>x @ Cardinality(S)@]", vec!["\u{3b1}\u{3b2}\u{3b3}".into()]).into(), format("@[<v0>%a@]", vec![format("y'@ foo_bar@,@[<v1>", vec![]).into()]).into()]), 68, Some("\\A\n \u{2200}\n \u{3b1}\u{3b2}\u{3b3}x  Cardinality(S)xy'\n                         foo_bar\n                         ")),
        (format("@\n@ Cardinality(S)@[<v4>@,=>x@]y'\u{2200}x@\n@\n@,bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbx@[<h4>@]@ @\n@ %a\\in%s @[<hov3>@ %a%a@ @]\u{3b1}\u{3b2}\u{3b3}\\inTRUE@,@[<b1>y'=>@]@\n", vec![format("@\nxfoo_barx@\n@ @[<h3>\u{2200}@;<0 1>@ @]", vec![]).into(), "=>".into(), format("TRUE abc=>@,y'@\n\u{2200}x%sCardinality(S)%a@\n", vec!["x".into(), format("\\in@[=> @;<3 3>%s%sabcy'<<a, b>>\u{2200}Cardinality(S)abc@]", vec!["Cardinality(S)".into(), "Cardinality(S)".into()]).into()]).into(), format("@ bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb \u{2200}\\A@ TRUE@[<v4>@,y'TRUE<<a, b>>@]", vec![]).into()]), 0, Some("\n Cardinality(S)\n\n=>xy'\u{2200}x\n\nbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbx\n \n \nxfoo_barx\n\n\u{2200} \\in=> \n TRUE abc=>\ny'\n\u{2200}xxCardinality(S)\\in\n=>    Cardinality(S)Cardinality(S)abcy'<<a, b>>\u{2200}Cardinality(S)abc\n bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb \u{2200}\\A TRUE\n\ny'TRUE<<a, b>> \u{3b1}\u{3b2}\u{3b3}\\inTRUE\ny'=>\n")),
        (format("@ @ =>@ abc@ \\A@ @ %s@ @ @\n@ @,@ \\A", vec!["\\A".into()]), 10, Some("  => abc \\A  \\A  \n \n\\A")),
        (format("@ <<a, b>>@\n@ %a\u{3b1}\u{3b2}\u{3b3}@\n@ @\nabcy'bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb@ @\n@,x@\n @[<b4>%a@\n Cardinality(S) \\A@ @ @[@[%ay'@]@]\\Ay'aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa@]", vec![format("x@;<2 4>@\n@ ", vec![]).into(), format("@ foo_bar", vec![]).into(), format("@\n@[<v0>\u{3b1}\u{3b2}\u{3b3}@ @]", vec![]).into()]), 10, Some(" <<a, b>>\n x  \n \u{3b1}\u{3b2}\u{3b3}\n \nabcy'bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb \n\nx\n  foo_bar\n      Cardinality(S) \\A \n     \n     \u{3b1}\u{3b2}\u{3b3}\n     y'\\Ay'aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")),
        (format("@ %a@[<h0>@]Cardinality(S)@ @ \\in@[<b4>@]%sTRUE@\n\u{3b1}\u{3b2}\u{3b3} abc@;<2 4>\\in@\n@;<3 1>@ %a@ @,@[<hov4>foo_bar@[<h4> @ @,@[<h3>@]@[@ @;<0 3>@]@;<0 4><<a, b>>=>abc@ ", vec![format("foo_barTRUE@ <<a, b>>bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb@\n<<a, b>>xfoo_bar%s%aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", vec!["\u{2200}".into(), format("TRUE%s%a\u{2200}@ ", vec!["=>".into(), format("\\A@[@]%s", vec!["foo_bar".into()]).into()]).into()]).into(), "abc".into(), format("@\nTRUECardinality(S)@ \u{2200}", vec![]).into()]), 68, Some(" foo_barTRUE\n<<a, b>>bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\n<<a, b>>xfoo_bar\u{2200}TRUE=>\\Afoo_bar\u{2200}\naaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaCardinality(S) \n\\inabcTRUE\n\u{3b1}\u{3b2}\u{3b3} abc  \\in\n    \nTRUECardinality(S) \u{2200} \nfoo_bar   <<a, b>>=>abc ")),
        (format("y'%a\u{3b1}\u{3b2}\u{3b3}\\inTRUE=>bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb@[<b1>@[<h4>@[<hv0>@ =>\\A@]@]@[<hov2><<a, b>>@]", vec![format("@ @\n@, @[TRUE@]", vec![]).into()]), 10, Some("y' \n\n TRUE\u{3b1}\u{3b2}\u{3b3}\\inTRUE=>bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\n =>\\A<<a, b>>")),
        (format("foo_bar@;<3 2>@\n@\n@;<3 2>@\n@,@ <<a, b>>@[<hv3>@]=>\u{2200}\\in@;<3 0>", vec![]), 68, Some("foo_bar   \n\n   \n <<a, b>>=>\u{2200}\\in\n")),
        (format("@\n@\n\\A@[<b0>%sy'@,@]@ @\nfoo_bar@[<b0>@]aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaabcTRUE", vec!["\u{2200}".into()]), 68, Some("\n\n\\A\u{2200}y'\n\nfoo_baraaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaabcTRUE")),
        (format("@ TRUE@\n@ @[@ @;<2 0>zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz@]@\nCardinality(S)@\n@[<hv2>foo_barTRUE\\inCardinality(S)\u{2200}@]", vec![]), 0, Some(" TRUE\n\n   zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz\nCardinality(S)\nfoo_barTRUE\\inCardinality(S)\u{2200}")),
        (format("@[x@]@\n@\n%a%sx@[\\in@[@ @]\u{2200}@;<2 3>@[\\A@ Cardinality(S)%a@  @\n@,<<a, b>>@[<v2>%s@ y'%s@[<h4>@;<0 4>@]y'@ %a@]@]@]", vec![format("\u{3b1}\u{3b2}\u{3b3}@ ", vec![]).into(), "zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz".into(), format("\u{3b1}\u{3b2}\u{3b3}@ @ \\inaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaax@;<0 2>x", vec![]).into(), "zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz".into(), "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".into(), format("y'@[<hv3>@;<1 4>@[<h1>@ ", vec![]).into()]), 10, Some("x\n\n\u{3b1}\u{3b2}\u{3b3}\nzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzx\n\\in \u{2200}\n   \\A Cardinality(S)\u{3b1}\u{3b2}\u{3b3} \n   \\inaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaax\n     x\n    \n   <<a, b>>\n   zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz\n     y'aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n     y'\n     y'  ")),
        (format("TRUE@\n@[<hv1>%a@[<hov2>\\inabcabc@,\\in@[<hov1>@;<3 1>@]", vec![format("@[<h4>@ @ TRUEx@,@ @;<2 1>@[<v1>@ <<a, b>>\\A@]", vec![]).into()]), 10, Some("TRUE\n  TRUEx   \n          <<a, b>>\\A\\inabcabc\\in   ")),
        (format("%s@ @ =>%a@ \\in@\nfoo_bar\u{2200}@.%a@ @\n%s@[<hv1>abc\u{3b1}\u{3b2}\u{3b3}@]abcabc%a@  @;<3 4> @\n%a@ =>%a@ abcx@\n", vec!["Cardinality(S)".into(), format("@ @\ny'\\A\u{3b1}\u{3b2}\u{3b3}\\in", vec![]).into(), format("@;<3 4>@ \\A=><<a, b>>@,<<a, b>>zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz", vec![]).into(), "y'".into(), format("@[<hv2>@;<2 0>%a@;<0 4>%a@]@[<v1>\u{2200}@ @]", vec![format("\\AaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaTRUE@;<1 4>%a@ \\A\u{2200}@.", vec![format("Cardinality(S)@ @[<v1>bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbby'@]", vec![]).into()]).into(), format("@ \\A@\n@.@ @\n%s", vec!["\u{2200}".into()]).into()]).into(), format("foo_barCardinality(S)@\ny'", vec![]).into(), format("=>@ @[<b3>%a@[<hov1>abc%a@]@]", vec![format("@,TRUE@\nfoo_bar%aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa@[@]", vec![format("@[<hv1>@]", vec![]).into()]).into(), format("foo_bar%s@;<0 0>@\n@;<1 0>", vec!["<<a, b>>".into()]).into()]).into()]), 68, Some("Cardinality(S)  => \ny'\\A\u{3b1}\u{3b2}\u{3b3}\\in\n\\in\nfoo_bar\u{2200}\n    \\A=><<a, b>>\n<<a, b>>zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz\n\ny'abc\u{3b1}\u{3b2}\u{3b3}abcabc\n                   \\AaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaTRUE\n                       Cardinality(S)\n                   bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbby'\n                   \\A\u{2200}\n\n\\A\n\n \n\u{2200}\u{2200}\n          \nfoo_barCardinality(S)\ny' =>=>\nTRUE\n   foo_baraaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaabcfoo_bar<<a, b>>\n                                                                \n                                                                 \nabcx\n")),
        (format("@ @[<v0>@\n\\inabc@,@]<<a, b>>%a%a@ <<a, b>>@ <<a, b>>@ @\n@\n@;<1 0>@;<1 4>@\n@.@ @,@\n@[<hov3>@]@[<h1>@]@.x@[<b3>@ \\A@ \u{2200}@,abc@]\\A@[@,@ @]", vec![format("@ x@\n@\n@\nx@ ", vec![]).into(), format("\u{2200}@[<h0>@ @]", vec![]).into()]), 35, Some(" \n \\inabc\n <<a, b>> x\n\n\nx \u{2200}  <<a, b>> <<a, b>> \n\n \n    \n\n \n\n\nx \\A \u{2200}abc\\A ")),
        (format("@,%a \\inaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa@\n\\Ax@\n%s@ @[<hov2>@]@\n\u{3b1}\u{3b2}\u{3b3}@\n@ @\n%s@[<v2>zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzTRUE\\A=>%s@,\u{2200}@]", vec![format("y'@ @;<2 2>@\n@\n@\n@[<v2>@]", vec![]).into(), "\\in".into(), "\u{3b1}\u{3b2}\u{3b3}".into(), "foo_bar".into()]), 0, Some("y'   \n\n\n \\inaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n\\Ax\n\\in \n\n\u{3b1}\u{3b2}\u{3b3}\n\n\n\u{3b1}\u{3b2}\u{3b3}\nzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzTRUE\\A=>foo_bar\n\u{2200}")),
        (format("@ @\n\\ACardinality(S)@ @ @ ", vec![]), 68, Some(" \n\\ACardinality(S)  \n")),
        (format("@[<hv3>@[<hv2>@,\\A @ @[<hv3>@.TRUE@ @]<<a, b>>@]@]@;<1 4>\\in=>Cardinality(S)@\n@\n=>\u{3b1}\u{3b2}\u{3b3}TRUE=>\u{2200}@ @[<b3><<a, b>>@]@ @ \u{3b1}\u{3b2}\u{3b3}@\n@ @;<2 2>@ y'@ abc", vec![]), 68, Some("\\A  \nTRUE <<a, b>> \\in=>Cardinality(S)\n\n=>\u{3b1}\u{3b2}\u{3b3}TRUE=>\u{2200} <<a, b>>  \u{3b1}\u{3b2}\u{3b3}\n    y'\nabc")),
        (format("\\ACardinality(S)=>bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb@[<h0>@,\\A@[<hv1>@ =>@ @\n@ @]@]", vec![]), 68, Some("\\ACardinality(S)=>bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\\A => \n                                                          ")),
        (format("foo_bar@\n@[<b1>@.@ abc@[<v4>abc@ @ =>@[<hv2>@\n%a@[<b4>y'\\A@[<b2>@[Cardinality(S)@]=>%ay'@ zzzzzzzzzzzzzzzzzzzz@ @]@]@]@]@]", vec![format("@\n@ @[<v2>\\A\u{2200}\\A@;<0 0> @ ", vec![]).into(), format("@ =>", vec![]).into()]), 68, Some("foo_bar\n\n\nabcabc\n       \n       =>\n           \n            \\A\u{2200}\\A\n               \n              y'\\ACardinality(S)=> =>y' zzzzzzzzzzzzzzzzzzzz ")),
        (format("\u{3b1}\u{3b2}\u{3b3}@ \u{2200}x@ @[\u{2200}%a@[<hv0>%a@[<b1>\\in@ aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa@,<<a, b>>y'@[<v1>@]@ \\inTRUE@]", vec![format("TRUE@;<3 2>aaaaaaaaaaaaaaaaaaaaaaaaaaa\\in=>@ x@;<2 4>y'@ x", vec![]).into(), format("@[%a=>@ foo_bar@]", vec![format("@;<2 3>@\n<<a, b>>", vec![]).into()]).into()]), 35, Some("\u{3b1}\u{3b2}\u{3b3} \u{2200}x\n\u{2200}TRUE   aaaaaaaaaaaaaaaaaaaaaaaaaaa\\in=> x  y'\nx  \n <<a, b>>=> foo_bar\\in\n                    aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n                    <<a, b>>y' \\inTRUE")),
        (format("@\n<<a, b>>@[<hv2>\\A@ xfoo_bar@[<h2>@[<b3>@,@]@[<h3>@]%s@[<hv2>%s%afoo_bar@ @]%sxbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\\ATRUE\\in%a@;<3 3>@[<v1>%a\\in@]@]@]", vec!["\\in".into(), "\\in".into(), format("x=>%szzzzzzzzzzzzzx@,", vec!["=>".into()]).into(), "zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz".into(), format("@[<hov1>@[<b3>@;<3 1>bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb@,@ bbbbbbbbbbbbbbbbbbbbbbbbbbbbbfoo_bar@ @]", vec![]).into(), format("%a@\n@\n@\n@;<0 1>x@\n@;<3 1>@ @ @  ", vec![format("@\n@\n@ ", vec![]).into()]).into()]), 68, Some("\n<<a, b>>\\A\n          xfoo_bar\\in\\inx=>=>zzzzzzzzzzzzzxfoo_bar zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzxbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\\ATRUE\\in\n                                                                    bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\n                                                                     bbbbbbbbbbbbbbbbbbbbbbbbbbbbbfoo_bar\n                                                                    \n                                                                    \n                                                                    \n                                                                    \n                                                                    \n                                                                    \n                                                                    \n                                                                    \n                                                                    x\n                                                                    \n                                                                    \n                                                                    \n                                                                    \n                                                                     \\in")),
        (format("@[<b3>@]%s@,%s", vec!["=>".into(), "=>".into()]), 68, Some("=>\n=>")),
        (format("@\n@\n<<a, b>>\u{3b1}\u{3b2}\u{3b3}@ bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb<<a, b>>\\A@ %s\u{3b1}\u{3b2}\u{3b3}%sxTRUE<<a, b>>TRUEfoo_bar@\n\\in%s\u{3b1}\u{3b2}\u{3b3}@[<h4>abc\u{2200}@\n@;<3 0>@ <<a, b>>@]%a%s@.\\A", vec!["=>".into(), "=>".into(), "abc".into(), format("zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz@,<<a, b>>@\n @[<hov3>@;<2 2>=> @.%a@]@,", vec![format("x@[<hv1>xzzzzzzzzzzzzzzzzz%a@]@ @\n=>%a", vec![format("\\A\u{2200}zzzzzzzzzzzzzzzzzzzzz=>\u{3b1}\u{3b2}\u{3b3} @ =>@ @ @\n", vec![]).into(), format("x@\nCardinality(S)@ @;<0 2>\\Afoo_bar", vec![]).into()]).into()]).into(), "Cardinality(S)".into()]), 0, Some("\n\n<<a, b>>\u{3b1}\u{3b2}\u{3b3}\nbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb<<a, b>>\\A\n=>\u{3b1}\u{3b2}\u{3b3}=>xTRUE<<a, b>>TRUEfoo_bar\n\\inabc\u{3b1}\u{3b2}\u{3b3}\nabc\u{2200}\n    <<a, b>>zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz\n<<a, b>>\n \n  => \nx\nxzzzzzzzzzzzzzzzzz\\A\u{2200}zzzzzzzzzzzzzzzzzzzzz=>\u{3b1}\u{3b2}\u{3b3}  =>  \n \n=>x\nCardinality(S) \\Afoo_bar\nCardinality(S)\n\\A")),
        (format("@\n%a@[<h4>=>abcfoo_barTRUE@,@,@ @[<hov3>x@,@ \\Afoo_barbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbTRUE@]@[@ @;<2 2>x\u{2200}@[<v1>", vec![format("@[<v3><<a, b>>foo_bar%ay'%ay'%a@ zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz\\A@]", vec![format("\u{3b1}\u{3b2}\u{3b3}@ \u{2200}@ @;<1 3>", vec![]).into(), format("@\n@ @[<v2>\u{3b1}\u{3b2}\u{3b3}@\ny'@[<hv0>\\in@]@]@\nzzzzzzzzzzzzzzzzzzzz@\n", vec![]).into(), format("@\n@[<b0>Cardinality(S)@]foo_bar\\in@\nx%sfoo_bar%a@ @.", vec!["\\in".into(), format("@\n@;<2 4>@[<hov0>@,@[<v2>xCardinality(S)@;<2 0>@[@]@ @]@]", vec![]).into()]).into()]).into()]), 68, Some("\n<<a, b>>foo_bar\u{3b1}\u{3b2}\u{3b3}\n   \u{2200}\n   \n      y'\n   \n   \u{3b1}\u{3b2}\u{3b3}\n     y'\\in\n   zzzzzzzzzzzzzzzzzzzz\n   y'\n   Cardinality(S)foo_bar\\in\n   x\\infoo_bar\n   \n       xCardinality(S)\n         \n         \n   \n\nzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz\\A=>abcfoo_barTRUE x\n                                                                    \\Afoo_barbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbTRUE\n                                                                      x\u{2200}")),
        (format("@ abc=>\u{2200}foo_bar%s \\Aabc@\nx\\in@[<hv2>@,@,=>%a<<a, b>>@ @;<2 0>foo_bar\u{2200} TRUEabc%s@[<h1>%a%a%s@;<2 2>TRUE@]<<a, b>>zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz\u{3b1}\u{3b2}\u{3b3}\u{2200}@  @\n\u{3b1}\u{3b2}\u{3b3}%s@ @]", vec!["bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb".into(), format("@\n@\n@\n@ @;<3 4>=>y'y'", vec![]).into(), "Cardinality(S)".into(), format("xx@\n@,<<a, b>>@ @\n %aCardinality(S)", vec![format("@\nfoo_bar@ @\nabc@ @ @\n  @\nfoo_bar@,", vec![]).into()]).into(), format("y'abc\\A\u{3b1}\u{3b2}\u{3b3}@ @\n@[<<a, b>>@ @;<3 0>%s@]", vec!["\u{2200}".into()]).into(), "<<a, b>>".into(), "<<a, b>>".into()]), 35, Some("\nabc=>\u{2200}foo_barbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb \\Aabc\nx\\in\n      \n      =>\n      \n      \n      \n      \n          =>y'y'<<a, b>>\n      \n      foo_bar\u{2200} TRUEabcCardinality(S)\n      xx\n       <<a, b>> \n        \n       foo_bar \n       abc  \n         \n       foo_barCardinality(S)y'abc\\A\u{3b1}\u{3b2}\u{3b3} \n       >    \u{2200}<<a, b>>  TRUE<<a, b>>zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz\u{3b1}\u{3b2}\u{3b3}\u{2200}\n       \n      \u{3b1}\u{3b2}\u{3b3}<<a, b>>\n      ")),
        (format("=>bbbbbbbbbbbbbbbbbbbb@ %s@[@;<0 4>@ @ @\nx@\n<<a, b>>", vec!["zzzzzzzzzzzzzzzzzzzzzzzzzz".into()]), 68, Some("=>bbbbbbbbbbbbbbbbbbbb\nzzzzzzzzzzzzzzzzzzzzzzzzzz  \n                          x\n                          <<a, b>>")),
        (format("TRUE\u{3b1}\u{3b2}\u{3b3}%a@ <<a, b>>Cardinality(S)foo_bar%ay'@,@\n@[<v2>@[<v4>%s@ @ @ Cardinality(S)@ \u{3b1}\u{3b2}\u{3b3}%s@,\u{2200}@,@]@]", vec![format("@\n@,\u{2200}@[<hov2>@[@[<v3>@,Cardinality(S)@ @ ", vec![]).into(), format("@\n@  <<a, b>>", vec![]).into(), "x".into(), "foo_bar".into()]), 68, Some("TRUE\u{3b1}\u{3b2}\u{3b3}\n\n\u{2200}\n      Cardinality(S)\n      \n      \n      <<a, b>>Cardinality(S)foo_bar\n      \n       <<a, b>>y'\n      \n      x\n          \n          \n          Cardinality(S)\n          \u{3b1}\u{3b2}\u{3b3}foo_bar\n          \u{2200}\n          ")),
        (format("@\n@\nxCardinality(S)@\n@[<b2>\u{2200}@\n@ @[<v0>@;<1 3>bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb@, %a@\n\u{3b1}\u{3b2}\u{3b3}@,@]@;<1 3>@]@;<0 2>%a@ foo_bar\u{2200}@ @ =>@ @[<hv0>@[<hv1>%s@]@]", vec![format("@\nTRUE@\n\u{3b1}\u{3b2}\u{3b3}@ y'@ @[<<a, b>><<a, b>>abc@]", vec![]).into(), format("@[<v0>@;<0 4>\\A@]", vec![]).into(), "\\in".into()]), 35, Some("\n\nxCardinality(S)\n\u{2200}\n   \n      bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\n    \n   TRUE\n   \u{3b1}\u{3b2}\u{3b3}\n   y'\n   ><<a, b>>abc\n   \u{3b1}\u{3b2}\u{3b3}\n    \n        \\A foo_bar\u{2200}  =>\n\\in")),
        (format("@,@,Cardinality(S)%a\\inabc@ ", vec![format("\u{2200}\u{3b1}\u{3b2}\u{3b3}\u{2200}@[<hov4>@.@ @[<hov2>\\A@ foo_bar@]", vec![]).into()]), 35, Some("\nCardinality(S)\u{2200}\u{3b1}\u{3b2}\u{3b3}\u{2200}\n \\A foo_bar\\inabc\n")),
        (format("@ \u{3b1}\u{3b2}\u{3b3}@ =>@\n", vec![]), 0, Some(" \u{3b1}\u{3b2}\u{3b3}\n=>\n")),
        (format("@\ny'TRUE%s\\in=>\\in<<a, b>>@;<2 0>@ @ @,Cardinality(S)\\in\u{3b1}\u{3b2}\u{3b3}@,x@\ny'@[<v2>zzzzzzzzzzzzzzzzzzzzz@[<hv1>@,@ \u{2200}@,aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa@;<3 4>\\in=>@[<hov3>%a@;<2 1>%s@]", vec!["=>".into(), format("@\nzzzzzzzzzzzzz@ Cardinality(S)@;<1 0>Cardinality(S)@,@,%s@[<b1>@;<2 0>%a@]", vec!["aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".into(), format("@,@\ny'@\n\\in@\n%a@[x@]zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz@,", vec![format("@[<h2>@ @[<b3>y'bbbbbbbbbbbbbbbbbbbbbbbbbbbbbb@]@]", vec![]).into()]).into()]).into(), "\\A".into()]), 0, Some("\ny'TRUE=>\\in=>\\in<<a, b>>    Cardinality(S)\\in\u{3b1}\u{3b2}\u{3b3}\nx\ny'\nzzzzzzzzzzzzzzzzzzzzz\n\n\n\u{2200}\naaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n\\in=>\n\nzzzzzzzzzzzzz Cardinality(S) Cardinality(S)\naaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n  \ny'\n\\in\n y'bbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\nxzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz  \\A")),
        (format("@ @\n%ay'@ =>@[<h3>@\n@]abc@ foo_bar", vec![format("=>aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaafoo_bar%a@ @\nCardinality(S)\u{3b1}\u{3b2}\u{3b3}@[<v4>@;<2 0>@]@ ", vec![format("@ @ @;<1 1> @.aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa@ zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz", vec![]).into()]).into()]), 68, Some("\n\n=>aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaafoo_bar\n \n  \naaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\nzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz \nCardinality(S)\u{3b1}\u{3b2}\u{3b3}\n                         y' =>\n                                 abc\nfoo_bar")),
        (format("%sfoo_bar@[<b3>\u{3b1}\u{3b2}\u{3b3}@ %a%sCardinality(S)Cardinality(S)abc@[@ \u{3b1}\u{3b2}\u{3b3}\\in@ =>@]Cardinality(S)%a\\A@[%s@,TRUE%a@,\\inCardinality(S)@ abc@,@]@ %sTRUE@;<3 1>@ @[<hov3>@]@ foo_bar@;<0 3>@]", vec!["\u{2200}".into(), format("@[<v1>@,%a@[<v1>@]@ %a\u{3b1}\u{3b2}\u{3b3}\u{3b1}\u{3b2}\u{3b3}@[<hv2>@]\\in", vec![format("Cardinality(S)x=>@[Cardinality(S)%a@ @[<h4>@ @]y'@ @]", vec![format("@\n@ Cardinality(S)@[<h1>@]zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz@,", vec![]).into()]).into(), format("\\in@ Cardinality(S)@ x@;<2 2>aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", vec![]).into()]).into(), "zzzzzzzzzzzzzz".into(), format("Cardinality(S)y'@ \\AxCardinality(S)\\ATRUE@ abc", vec![]).into(), "Cardinality(S)".into(), format("abc@ \\inTRUE@[<hov0>%a@[<h0>@\n@[<hov3>@]@]@]", vec![format("@\nx@.@,bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz@ @\nCardinality(S)@\n%a\\in", vec![format(" abc@[<hv3> @[<b3>TRUE\u{2200}", vec![]).into()]).into()]).into(), "\u{2200}".into()]), 35, Some("\u{2200}foo_bar\u{3b1}\u{3b2}\u{3b3}\n             \n              Cardinality(S)x=>Cardinality(S)\n                                Cardinality(S)\n                               zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz\n                                 y' \n              \n              \\in\n              Cardinality(S)\n              x\n                aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\u{3b1}\u{3b2}\u{3b3}\u{3b1}\u{3b2}\u{3b3}\n              \\inzzzzzzzzzzzzzzCardinality(S)Cardinality(S)abc\n               \u{3b1}\u{3b2}\u{3b3}\\in =>Cardinality(S)Cardinality(S)y'\n              \\AxCardinality(S)\\ATRUE\n              abc\\ACardinality(S)TRUEabc \\inTRUE\n                                   x\n\nbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz\n\nCardinality(S)\n abc TRUE\u{2200}\\in\n               \\inCardinality(S) abc \u{2200}TRUE    \n foo_bar\n   ")),
        (format("\\in=>@[<h3>@]@[<h2>@]@ @[<h1>@]@ aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa@ TRUE%s\u{3b1}\u{3b2}\u{3b3}@[=>\\A@[<hov3>@[<hv4>@]@]@]", vec!["aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".into()]), 68, Some("\\in=>  aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\nTRUEaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\u{3b1}\u{3b2}\u{3b3}\n=>\\A")),
        (format("@[<hv4>\u{3b1}\u{3b2}\u{3b3}@]aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa@ @[<b4>@,@]@[<hov4>@,\u{2200}=>@ @] @ %s@[<v1>abc@;<2 2>@]", vec!["y'".into()]), 10, Some("\u{3b1}\u{3b2}\u{3b3}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa \n\u{2200}=>  \ny'abc\n     ")),
        (format("@;<1 4>@;<2 4>@\n<<a, b>> @ @[<h2>abc \u{2200}Cardinality(S)@[<hv1>@ @[<hv2>@]", vec![]), 0, Some("   \n<<a, b>> \nabc \u{2200}Cardinality(S) ")),
        (format("%a@,TRUE\u{2200}\u{3b1}\u{3b2}\u{3b3}@[<v0>@ @ \u{2200}\u{2200}@,%sfoo_bar\\A@[<v1>@ <<a, b>><<a, b>>bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb@,@]@]", vec![format("Cardinality(S)@,@\n@ @\n%sfoo_bar@ @;<3 2>%a@ x", vec!["foo_bar".into(), format("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa<<a, b>>@ TRUE@\n@\n@\n\u{3b1}\u{3b2}\u{3b3}@ @;<2 4>", vec![]).into()]).into(), "foo_bar".into()]), 35, Some("Cardinality(S)\n \nfoo_barfoo_bar    aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa<<a, b>> TRUE\n\n\n\u{3b1}\u{3b2}\u{3b3}    x\nTRUE\u{2200}\u{3b1}\u{3b2}\u{3b3}\n             \n             \u{2200}\u{2200}\n             foo_barfoo_bar\\A\n                              <<a, b>><<a, b>>bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\n                              ")),
        ];
        for (index, (doc, max_indent, expected)) in cases.iter().enumerate() {
            let rendered = render_doc(doc, *max_indent);
            assert_eq!(
                rendered.as_deref().ok(),
                *expected,
                "case {index}: {rendered:?}"
            );
        }
    }

    #[test]
    fn fails_to_render_a_directive_without_its_close() {
        for pattern in ["a@[<hov2", "a@;<1 2", "a@<1%s"] {
            assert!(render_doc(&format(pattern, vec!["x".into()]), 68).is_err());
        }
    }

    #[test]
    fn stops_format_delimited_at_the_first_error() {
        let mut seen = Vec::new();
        let result = format_delimited(
            &[1, 2, 3],
            |item| {
                seen.push(*item);
                if *item == 2 {
                    return Err(ObligationError::assert_failure());
                }
                Ok(text("x"))
            },
            None,
        );
        assert_eq!(result, Err(ObligationError::assert_failure()));
        assert_eq!(seen, [1, 2]);
    }
}
