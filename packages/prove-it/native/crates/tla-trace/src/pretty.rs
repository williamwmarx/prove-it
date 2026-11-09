//! TLC's tlc2.pprint, as `src/pretty-print.ts` ports it: re-parses a printed value and breaks it
//! across lines of at most 80 columns, or keeps the original text when the parse fails. It works
//! on UTF-16 units, as Java and JavaScript count a string's length.

const WIDTH: i64 = 80;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Constant,
    Set,
    Sequence,
    Record,
    Function,
    Subset,
    Pair,
}

struct Node {
    kind: Kind,
    first: usize,
    last: usize,
    children: Vec<Node>,
}

struct Delimiters {
    open: &'static str,
    close: &'static str,
    pad: &'static str,
    separator: &'static str,
    divider: &'static str,
    divider_pad: &'static str,
}

fn delimiters(kind: Kind) -> Delimiters {
    let items = |open, close, pad| Delimiters {
        open,
        close,
        pad,
        separator: ",",
        divider: "",
        divider_pad: "",
    };
    match kind {
        Kind::Set => items("{ ", " }", "  "),
        Kind::Sequence => items("<< ", " >>", "   "),
        Kind::Subset => items("SUBSET ", " ", " "),
        Kind::Function => Delimiters {
            open: "( ",
            close: " )",
            pad: "  ",
            separator: " @@",
            divider: " :>",
            divider_pad: "    ",
        },
        _ => Delimiters {
            open: "[ ",
            close: " ]",
            pad: "  ",
            separator: ",",
            divider: " |->",
            divider_pad: "    ",
        },
    }
}

fn is_whitespace(unit: u16) -> bool {
    matches!(unit, 0x09..=0x0d | 0x1c..=0x20 | 0x1680 | 0x2028 | 0x2029 | 0x205f | 0x3000)
        || ((0x2000..=0x200a).contains(&unit) && unit != 0x2007)
}

fn to_char(unit: u16) -> Option<char> {
    char::from_u32(u32::from(unit))
}

// TLA+ prints only ASCII outside strings, where these agree with Unicode's Nd, L and Nd.
fn is_digit(unit: u16) -> bool {
    to_char(unit).is_some_and(|character| {
        character.is_ascii_digit() || (!character.is_ascii() && character.is_numeric())
    })
}

fn is_letter_or_digit(unit: u16) -> bool {
    to_char(unit).is_some_and(char::is_alphanumeric)
}

struct Parser<'a> {
    text: &'a [u16],
}

impl Parser<'_> {
    fn at(&self, index: usize) -> Option<u16> {
        self.text.get(index).copied()
    }

    fn starts_with(&self, index: usize, prefix: &str) -> bool {
        let units: Vec<u16> = prefix.encode_utf16().collect();
        self.text
            .get(index..index + units.len())
            .is_some_and(|slice| slice == units.as_slice())
    }

    fn skip_while(&self, mut index: usize, predicate: fn(u16) -> bool) -> usize {
        while self.at(index).is_some_and(predicate) {
            index += 1;
        }
        index
    }

    fn skip_whitespace(&self, index: usize) -> Option<usize> {
        let end = self.skip_while(index, is_whitespace);
        (end < self.text.len()).then_some(end)
    }

    fn items(
        &self,
        kind: Kind,
        first: usize,
        start: usize,
        close: u16,
        is_pair: Option<&str>,
        separator: &str,
    ) -> Option<Node> {
        let mut node = Node {
            kind,
            first,
            last: first,
            children: Vec::new(),
        };
        let mut index = self.skip_whitespace(start);
        while let Some(position) = index.filter(|&position| self.at(position) != Some(close)) {
            let item = match is_pair {
                Some(divider) => self.pair(position, divider)?,
                None => self.parse(position)?,
            };
            let after_item = self.skip_whitespace(item.last + 1)?;
            node.children.push(item);
            let after_separator = if self.starts_with(after_item, separator) {
                after_item + separator.encode_utf16().count()
            } else {
                after_item
            };
            index = self.skip_whitespace(after_separator);
        }
        node.last = index?;
        Some(node)
    }

    fn pair(&self, index: usize, divider: &str) -> Option<Node> {
        let left = self.parse(index)?;
        let divider_index = self.skip_whitespace(left.last + 1)?;
        if !self.starts_with(divider_index, divider) {
            return None;
        }
        let right_index = self.skip_whitespace(divider_index + divider.len())?;
        let right = self.parse(right_index)?;
        Some(Node {
            kind: Kind::Pair,
            first: index,
            last: right.last,
            children: vec![left, right],
        })
    }

    fn constant(&self, first: usize, last: usize) -> Option<Node> {
        Some(Node {
            kind: Kind::Constant,
            first,
            last,
            children: Vec::new(),
        })
    }

    fn interval(&self, first: usize) -> Option<Node> {
        let low_end = self.skip_while(first, is_digit);
        if !self.starts_with(low_end, "..") || !self.at(low_end + 2).is_some_and(is_digit) {
            return None;
        }
        self.constant(first, self.skip_while(low_end + 2, is_digit) - 1)
    }

    fn parse_constant(&self, first: usize) -> Option<Node> {
        let unit = self.at(first)?;
        if unit == u16::from(b'"') {
            let closing = (first + 1..self.text.len()).find(|&index| self.text[index] == unit)?;
            return self.constant(first, closing);
        }
        if is_digit(unit)
            && let Some(interval) = self.interval(first)
        {
            return Some(interval);
        }
        if unit == u16::from(b'-') {
            if first + 1 >= self.text.len() {
                return None;
            }
            return self.constant(first, self.skip_while(first + 1, is_digit) - 1);
        }
        if !is_letter_or_digit(unit) {
            return None;
        }
        self.constant(first, self.skip_while(first, is_letter_or_digit) - 1)
    }

    fn parse(&self, index: usize) -> Option<Node> {
        let first = self.skip_whitespace(index)?;
        match self.at(first).and_then(to_char) {
            Some('{') => self.items(Kind::Set, first, first + 1, u16::from(b'}'), None, ","),
            Some('<') => {
                let node =
                    self.items(Kind::Sequence, first, first + 2, u16::from(b'>'), None, ",")?;
                if node.last + 1 >= self.text.len() {
                    return None;
                }
                Some(Node {
                    last: node.last + 1,
                    ..node
                })
            }
            Some('[') => self.items(
                Kind::Record,
                first,
                first + 1,
                u16::from(b']'),
                Some("|->"),
                ",",
            ),
            Some('(') => self.items(
                Kind::Function,
                first,
                first + 1,
                u16::from(b')'),
                Some(":>"),
                "@@",
            ),
            _ if self.starts_with(first, "SUBSET") => {
                let element_index = self.skip_whitespace(first + 6)?;
                let element = self.parse(element_index)?;
                Some(Node {
                    kind: Kind::Subset,
                    first,
                    last: element.last,
                    children: vec![element],
                })
            }
            _ => self.parse_constant(first),
        }
    }
}

struct Formatter<'a> {
    text: &'a [u16],
}

impl Formatter<'_> {
    fn text(&self, node: &Node) -> String {
        String::from_utf16_lossy(&self.text[node.first..=node.last])
    }

    fn length(node: &Node) -> i64 {
        (node.last - node.first + 1) as i64
    }

    fn format(&self, node: &Node, width: i64, trailer: i64, pad: &str) -> Option<String> {
        if Self::length(node) + trailer <= width || node.kind == Kind::Constant {
            return Some(self.text(node));
        }
        if node.kind == Kind::Pair {
            return None;
        }
        let delimiters = delimiters(node.kind);
        let inner_width = width - delimiters.open.len().max(delimiters.pad.len()) as i64;
        let inner_trailer = trailer + delimiters.close.len() as i64;
        let inner_pad = format!("{pad}{}", delimiters.pad);
        let inner = if matches!(node.kind, Kind::Function | Kind::Record) {
            self.pairs(
                &node.children,
                inner_width,
                inner_trailer,
                &inner_pad,
                &delimiters,
            )
        } else {
            self.items(
                &node.children,
                inner_width,
                inner_trailer,
                &inner_pad,
                delimiters.separator,
            )
        }?;
        Some(format!("{}{inner}{}", delimiters.open, delimiters.close))
    }

    fn items(
        &self,
        items: &[Node],
        width: i64,
        trailer: i64,
        pad: &str,
        separator: &str,
    ) -> Option<String> {
        let mut result = String::new();
        for (index, item) in items.iter().enumerate() {
            let is_last = index == items.len() - 1;
            let formatted = self.format(
                item,
                width,
                if is_last {
                    trailer
                } else {
                    separator.len() as i64
                },
                pad,
            )?;
            result.push_str(&formatted);
            if !is_last {
                result.push_str(&format!("{separator}\n{pad}"));
            }
        }
        Some(result)
    }

    fn pairs(
        &self,
        pairs: &[Node],
        width: i64,
        trailer: i64,
        pad: &str,
        delimiters: &Delimiters,
    ) -> Option<String> {
        let mut result = String::new();
        for (index, pair) in pairs.iter().enumerate() {
            let is_last = index == pairs.len() - 1;
            let (left, right) = (&pair.children[0], &pair.children[1]);
            let ending = if is_last {
                String::new()
            } else {
                format!("{}\n{pad}", delimiters.separator)
            };
            let divider = delimiters.divider.len() as i64;
            let separator = delimiters.separator.len() as i64;
            let pair_length = Self::length(left) + divider + 1 + Self::length(right);
            let fits = if is_last {
                pair_length + trailer <= width
            } else {
                pair_length + separator <= width
            };
            if fits {
                result.push_str(&format!(
                    "{}{} {}{ending}",
                    self.text(left),
                    delimiters.divider,
                    self.text(right)
                ));
                continue;
            }
            let formatted_left = if Self::length(left) + divider <= width {
                self.text(left)
            } else {
                self.format(left, width, trailer + divider, pad)?
            };
            let formatted_right = self.format(
                right,
                width - delimiters.divider_pad.len() as i64,
                if is_last { trailer } else { separator },
                &format!("{pad}{}", delimiters.divider_pad),
            )?;
            result.push_str(&format!(
                "{formatted_left}{}\n{pad}{}{formatted_right}{ending}",
                delimiters.divider, delimiters.divider_pad
            ));
        }
        Some(result)
    }
}

/// TLC's pretty printing of a printed value, as `prettyPrint` in `src/pretty-print.ts`.
pub fn pretty_print(text: &[u16]) -> String {
    let parser = Parser { text };
    let tree = if text.is_empty() {
        None
    } else {
        parser.parse(0)
    };
    match tree {
        Some(tree) if tree.last + 1 >= text.len() => Formatter { text }
            .format(&tree, WIDTH, 0, "")
            .unwrap_or_else(|| String::from_utf16_lossy(text)),
        _ => String::from_utf16_lossy(text),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Values and what `prettyPrint` in `src/pretty-print.ts` makes of each, generated from it.
    const CASES: &str = include_str!("../tests/pretty-print.txt");

    #[test]
    fn breaks_values_as_the_typescript_printer_does() {
        let mut count = 0;
        for case in CASES.split("\n===\n") {
            let (input, expected) = case.split_once("\n---\n").expect("a case");
            let units: Vec<u16> = input.encode_utf16().collect();
            assert_eq!(pretty_print(&units), expected, "for {input}");
            count += 1;
        }
        assert_eq!(count, 208);
    }
}
