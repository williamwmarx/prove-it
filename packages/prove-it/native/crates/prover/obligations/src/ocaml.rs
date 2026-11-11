//! The parts of OCaml's standard library whose exact order steers what tlapm prints, a port of
//! `src/prover/ocaml.ts`, and OCaml's ints, which tlapm reads numerals and step levels into.

/// `OcamlValue`: an int, a string, or a list of values.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OcamlValue {
    Int(i64),
    Text(String),
    List(Vec<OcamlValue>),
}

// String.compare: byte by byte, on the UTF-8 bytes. Code units order the same way for the ASCII
// names tlapm compares.
pub fn compare_strings(left: &str, right: &str) -> i64 {
    match left.encode_utf16().cmp(right.encode_utf16()) {
        std::cmp::Ordering::Less => -1,
        std::cmp::Ordering::Equal => 0,
        std::cmp::Ordering::Greater => 1,
    }
}

// Stdlib.compare on ints, strings, and lists, where a list is smaller than any longer list it
// starts.
pub fn compare_values(left: &OcamlValue, right: &OcamlValue) -> i64 {
    match (left, right) {
        (OcamlValue::Int(left), OcamlValue::Int(right)) => left.saturating_sub(*right),
        (OcamlValue::Text(left), OcamlValue::Text(right)) => compare_strings(left, right),
        (OcamlValue::List(left), OcamlValue::List(right)) => {
            let index = left.iter().enumerate().position(|(position, item)| {
                position >= right.len() || compare_values(item, &right[position]) != 0
            });
            match index {
                None => left.len() as i64 - right.len() as i64,
                Some(index) if index >= right.len() => 1,
                Some(index) => compare_values(&left[index], &right[index]),
            }
        }
        _ => 0,
    }
}

/// OCaml's `max_int` and `min_int`: an int is 63 bits wide.
pub const MAX_INT: i64 = (1 << 62) - 1;
pub const MIN_INT: i64 = -(1 << 62);

/// `int_of_string`: OCaml 5.1's `caml_int_of_string` (runtime/ints.c:139), `parse_intnat` with 63
/// bits (ints.c:77-115), or `None` where it raises `Failure "int_of_string"`. A `0x`, `0o`, `0b` or
/// `0u` prefix reads the digits as unsigned, up to 2^63 - 1, which `Val_long` wraps into the 63-bit
/// range; without one they are signed, from -2^62 to 2^62 - 1. Underscores after the first digit
/// are skipped.
pub fn int_of_string(text: &str) -> Option<i64> {
    let bytes = text.as_bytes();
    // parse_sign_and_base (ints.c:33-58).
    let (sign, mut index) = match bytes.first() {
        Some(b'-') => (-1, 1),
        Some(b'+') => (1, 1),
        _ => (1, 0),
    };
    let (base, is_signed) = match (bytes.get(index), bytes.get(index + 1)) {
        (Some(b'0'), Some(b'x' | b'X')) => (16, false),
        (Some(b'0'), Some(b'o' | b'O')) => (8, false),
        (Some(b'0'), Some(b'b' | b'B')) => (2, false),
        (Some(b'0'), Some(b'u' | b'U')) => (10, false),
        _ => (10, true),
    };
    if !is_signed {
        index += 2;
    }
    let digit = |byte: Option<&u8>| {
        byte.and_then(|byte| char::from(*byte).to_digit(16))
            .filter(|digit| *digit < base)
            .map(u64::from)
    };
    let mut result = digit(bytes.get(index))?;
    index += 1;
    while index < bytes.len() {
        if bytes[index] != b'_' {
            let Some(digit) = digit(bytes.get(index)) else {
                break;
            };
            result = result.checked_mul(u64::from(base))?.checked_add(digit)?;
        }
        index += 1;
    }
    if index != bytes.len() {
        return None;
    }
    let limit = 1u64 << 62;
    let is_in_range = match (is_signed, sign) {
        (true, 1) => result < limit,
        (true, _) => result <= limit,
        (false, _) => result < limit << 1,
    };
    if !is_in_range {
        return None;
    }
    // The intnat parse_intnat returns, and the int Val_long keeps of it: its low 63 bits.
    let value = (result as i64).wrapping_mul(sign);
    Some((value << 1) >> 1)
}

/// `n + 1` on an OCaml int, which wraps from `max_int` to `min_int`.
pub fn succ(value: i64) -> i64 {
    if value == MAX_INT { MIN_INT } else { value + 1 }
}

// Expected values from running the TypeScript.
#[cfg(test)]
mod tests {
    use super::*;

    fn int(value: i64) -> OcamlValue {
        OcamlValue::Int(value)
    }

    fn text(value: &str) -> OcamlValue {
        OcamlValue::Text(value.to_string())
    }

    fn list(values: Vec<OcamlValue>) -> OcamlValue {
        OcamlValue::List(values)
    }

    #[test]
    fn compares_strings() {
        assert_eq!(compare_strings("a", "b"), -1);
        assert_eq!(compare_strings("b", "a"), 1);
        assert_eq!(compare_strings("ab", "ab"), 0);
        assert_eq!(compare_strings("ab", "a"), 1);
        assert_eq!(compare_strings("", "a"), -1);
        assert_eq!(compare_strings("Z", "a"), -1);
        assert_eq!(compare_strings("\u{ff5e}", "\u{1f600}"), 1);
    }

    #[test]
    fn compares_values() {
        assert_eq!(compare_values(&int(3), &int(7)), -4);
        assert_eq!(compare_values(&int(7), &int(3)), 4);
        assert_eq!(compare_values(&text("x"), &text("y")), -1);
        assert_eq!(compare_values(&int(1), &text("y")), 0);
        assert_eq!(compare_values(&list(vec![]), &int(1)), 0);
        assert_eq!(
            compare_values(&list(vec![int(1)]), &list(vec![int(1), int(2)])),
            -1
        );
        assert_eq!(
            compare_values(&list(vec![int(1), int(2)]), &list(vec![int(1)])),
            1
        );
        assert_eq!(
            compare_values(&list(vec![int(1), int(2)]), &list(vec![int(1), int(2)])),
            0
        );
        assert_eq!(
            compare_values(
                &list(vec![int(2), list(vec![text("a"), text("c")])]),
                &list(vec![int(2), list(vec![text("a"), text("b"), text("z")])])
            ),
            1
        );
        assert_eq!(
            compare_values(&list(vec![int(5)]), &list(vec![int(9), int(0)])),
            -4
        );
        assert_eq!(
            compare_values(&list(vec![text("b")]), &list(vec![text("a"), int(3)])),
            1
        );
    }

    // runtime/ints.c:77-115 at OCaml 5.1.0, as caml_int_of_string calls it with 63 bits.
    #[test]
    fn reads_ints_as_int_of_string_does() {
        let cases: [(&str, Option<i64>); 26] = [
            ("0", Some(0)),
            ("007", Some(7)),
            ("4611686018427387903", Some(MAX_INT)),
            ("4611686018427387904", None),
            ("-4611686018427387904", Some(MIN_INT)),
            ("-4611686018427387905", None),
            ("99999999999999999999999", None),
            ("0x1F", Some(31)),
            ("0b101", Some(5)),
            ("0o17", Some(15)),
            ("0x3FFFFFFFFFFFFFFF", Some(MAX_INT)),
            // Unsigned digits past max_int wrap into the negative ints.
            ("0x4000000000000000", Some(MIN_INT)),
            ("0x7FFFFFFFFFFFFFFF", Some(-1)),
            ("0x8000000000000000", None),
            ("0xFFFFFFFFFFFFFFFF", None),
            ("0x10000000000000000", None),
            ("0x0000000000000000000000001", Some(1)),
            ("-0x1", Some(-1)),
            ("1_000", Some(1000)),
            ("_1", None),
            ("", None),
            ("-", None),
            ("0x", None),
            ("12a", None),
            ("0b2", None),
            ("0u18446744073709551615", None),
        ];
        for (text, expected) in cases {
            assert_eq!(int_of_string(text), expected, "{text}");
        }
    }

    #[test]
    fn wraps_the_successor_of_max_int() {
        assert_eq!(succ(1), 2);
        assert_eq!(succ(MAX_INT), MIN_INT);
        assert_eq!(succ(MIN_INT), MIN_INT + 1);
    }
}
