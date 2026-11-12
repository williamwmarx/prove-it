//! A module's file as tlapm reads it: bytes, whose columns it counts in bytes (`Loc`'s
//! `pos_cnum - pos_bol + 1`). The front end reads text and counts columns in UTF-16 units, so a
//! file is decoded with each byte that doesn't start a well-formed UTF-8 sequence (Unicode's
//! Table 3-7) as a marker of its own, U+10FF00 plus the byte, which keeps two different byte
//! strings different; and a file registered here has its columns printed in bytes, a marker as
//! the one byte it stands for.

use std::cell::RefCell;
use std::collections::HashMap;

const MARKER_BASE: u32 = 0x10_FF00;

/// The marker a byte that isn't UTF-8 reads as.
pub fn get_marker(byte: u8) -> char {
    char::from_u32(MARKER_BASE + u32::from(byte)).expect("a code point")
}

/// The byte a marker stands for. Only the bytes from 0x80 have markers.
pub fn get_marked_byte(character: char) -> Option<u8> {
    let code = u32::from(character).checked_sub(MARKER_BASE)?;
    u8::try_from(code).ok().filter(|byte| *byte >= 0x80)
}

/// The text of a file's bytes, each byte that doesn't start a well-formed sequence as its marker.
pub fn decode(bytes: &[u8]) -> String {
    let mut text = String::with_capacity(bytes.len());
    let mut rest = bytes;
    loop {
        match std::str::from_utf8(rest) {
            Ok(valid) => {
                text.push_str(valid);
                return text;
            }
            Err(error) => {
                let (valid, invalid) = rest.split_at(error.valid_up_to());
                text.push_str(std::str::from_utf8(valid).expect("the valid prefix"));
                let length = error.error_len().unwrap_or(invalid.len());
                text.extend(invalid[..length].iter().map(|byte| get_marker(*byte)));
                rest = &invalid[length..];
            }
        }
    }
}

/// The first character of the file's UTF-8 that is a marker, which the file would read alike with
/// the byte it stands for.
pub fn find_marker_held(bytes: &[u8]) -> Option<char> {
    bytes
        .utf8_chunks()
        .flat_map(|chunk| chunk.valid().chars())
        .find(|character| get_marked_byte(*character).is_some())
}

/// The bytes that aren't UTF-8 in the file, in order.
pub fn get_bytes_not_utf8(bytes: &[u8]) -> Vec<u8> {
    bytes
        .utf8_chunks()
        .flat_map(|chunk| chunk.invalid().iter().copied())
        .collect()
}

/// The first marker `value`'s `Debug` holds, which reaches each text it holds and writes a marker
/// as its escape, `\u{10ffxx}`.
pub fn find_marker_in(value: &dyn std::fmt::Debug) -> Option<char> {
    struct Finder {
        tail: String,
        found: Option<char>,
    }
    impl std::fmt::Write for Finder {
        fn write_str(&mut self, text: &str) -> std::fmt::Result {
            self.tail.push_str(text);
            let mut start = 0;
            while let Some(found) = self.tail[start..].find("\\u{10ff") {
                let at = start + found + "\\u{10ff".len();
                let Some(digits) = self.tail.get(at..at + 3) else {
                    break;
                };
                if let Some(hex) = digits.strip_suffix('}')
                    && let Ok(byte) = u8::from_str_radix(hex, 16)
                    && byte >= 0x80
                {
                    self.found = Some(get_marker(byte));
                    return Err(std::fmt::Error);
                }
                start = at;
            }
            let keep = self.tail.len().saturating_sub(16);
            let keep = (keep..=self.tail.len())
                .find(|index| self.tail.is_char_boundary(*index))
                .unwrap_or(self.tail.len());
            self.tail.drain(..keep);
            Ok(())
        }
    }
    let mut finder = Finder {
        tail: String::new(),
        found: None,
    };
    let _ = std::fmt::write(&mut finder, format_args!("{value:?}"));
    finder.found
}

thread_local! {
    // The lines of each file registered that holds more than ASCII, by its name.
    static LINES: RefCell<HashMap<String, Vec<String>>> = RefCell::default();
}

/// Has the loci of `file` print their columns in the bytes of `text`.
pub fn register_byte_columns(file: &str, text: &str) {
    if text.is_ascii() {
        return;
    }
    let lines = text.split('\n').map(str::to_owned).collect();
    LINES.with(|files| files.borrow_mut().insert(file.to_owned(), lines));
}

pub fn reset_byte_columns() {
    LINES.with(|files| files.borrow_mut().clear());
}

/// The column, which the front end counts in UTF-16 units from 1, as tlapm counts it in a file
/// registered: in bytes.
pub fn get_byte_column(file: &str, line: u32, column: u32) -> u32 {
    if column == 0 {
        return column;
    }
    LINES.with(|files| {
        let files = files.borrow();
        let Some(text) = files
            .get(file)
            .and_then(|lines| lines.get(usize::try_from(line).ok()?.checked_sub(1)?))
        else {
            return column;
        };
        let mut units = column - 1;
        let mut bytes = 0;
        for character in text.chars() {
            let length = character.len_utf16() as u32;
            if units < length {
                break;
            }
            units -= length;
            bytes += if get_marked_byte(character).is_some() {
                1
            } else {
                character.len_utf8() as u32
            };
        }
        1 + bytes + units
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reads_each_byte_that_isnt_utf8_as_its_marker() {
        assert_eq!(decode(b"a\xffb"), "a\u{10ffff}b");
        // E2 82 starts a sequence it doesn't finish; ED A0 80 encodes a surrogate.
        assert_eq!(decode(b"\xe2\x82*"), "\u{10ffe2}\u{10ff82}*");
        assert_eq!(decode(b"\xed\xa0\x80"), "\u{10ffed}\u{10ffa0}\u{10ff80}");
        assert_eq!(decode("é😀".as_bytes()), "é😀");
        assert_eq!(get_marked_byte('\u{10ffe9}'), Some(0xe9));
        assert_eq!(get_marked_byte('\u{10ff41}'), None);
        assert_eq!(get_marked_byte('a'), None);
    }

    #[test]
    fn finds_a_marker_wherever_it_is_held() {
        assert_eq!(
            find_marker_held("a\u{10ff80}".as_bytes()),
            Some('\u{10ff80}')
        );
        assert_eq!(find_marker_held(b"a\xff"), None);
        assert_eq!(
            get_bytes_not_utf8(b"a\xff\xe2\x82*\xc3\xa9"),
            [0xff, 0xe2, 0x82]
        );
        let held = vec![("a".to_owned(), Some(decode(b"\xfe")))];
        assert_eq!(find_marker_in(&held), Some('\u{10fffe}'));
        assert_eq!(find_marker_in(&vec!["a"]), None);
    }

    #[test]
    fn counts_the_columns_of_a_registered_file_in_bytes() {
        let text = decode(b"ab\n(* \xe2\x82 \xc3\xa9 \xf0\x9f\x98\x80 *) X\n");
        register_byte_columns("M.tla", &text);
        // A marker is two UTF-16 units: `X` is the 17th unit and the 18th byte.
        assert_eq!(get_byte_column("M.tla", 2, 16), 17);
        assert_eq!(get_byte_column("M.tla", 2, 17), 18);
        assert_eq!(get_byte_column("M.tla", 2, 30), 31);
        assert_eq!(get_byte_column("M.tla", 1, 2), 2);
        assert_eq!(get_byte_column("Other.tla", 2, 16), 16);
        reset_byte_columns();
        assert_eq!(get_byte_column("M.tla", 2, 16), 16);
    }
}
