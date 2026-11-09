//! JSON as JavaScript's `JSON.stringify` writes it, so the differential harness compares the
//! Rust front end's output with the TypeScript one's as text.

use std::fmt::Write;

pub fn write_js_string(out: &mut String, text: &str) {
    out.push('"');
    for character in text.chars() {
        match character {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\u{8}' => out.push_str("\\b"),
            '\u{c}' => out.push_str("\\f"),
            '\0'..='\u{1f}' => {
                let _ = write!(out, "\\u{:04x}", u32::from(character));
            }
            _ => out.push(character),
        }
    }
    out.push('"');
}

/// A number as JavaScript prints it: `null` for one JSON can't hold, the digits of an integer
/// below 10^21, and the shortest digits that round-trip otherwise.
pub fn write_js_number(out: &mut String, value: f64) {
    if !value.is_finite() {
        out.push_str("null");
    } else if value == 0.0 {
        out.push('0');
    } else if value.abs() >= 1e21 || value.abs() < 1e-6 {
        let scientific = format!("{value:e}");
        let (mantissa, exponent) = scientific.split_once('e').unwrap_or((&scientific, "0"));
        let sign = if exponent.starts_with('-') { "" } else { "+" };
        let _ = write!(out, "{mantissa}e{sign}{exponent}");
    } else {
        let _ = write!(out, "{value}");
    }
}
