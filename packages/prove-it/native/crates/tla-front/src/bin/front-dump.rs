//! Writes what the front end makes of each file named on standard input, one JSON line per file,
//! for `scripts/front-differential.ts` to compare with the TypeScript front end:
//!
//! - `front-dump tokens` writes each module's tokens as `[kind, text, spelling, line, column,
//!   endColumn]`, or the syntax error the lexer raises.

use std::fmt::Write as _;
use std::io::{BufRead, Write, stdin, stdout};
use std::process::ExitCode;

use tla_front::errors::SyntaxError;
use tla_front::json::write_js_string;
use tla_front::lexer::tokenize;

fn write_error(out: &mut String, error: &SyntaxError) {
    out.push_str("{\"error\":");
    write_js_string(out, &error.message);
    if let Some(failure) = &error.failure {
        out.push_str(",\"failure\":{\"reason\":");
        write_js_string(out, &failure.reason);
        let _ = write!(
            out,
            ",\"line\":{},\"column\":{},\"isEnd\":{}}}",
            failure.line, failure.column, failure.is_end
        );
    }
    out.push('}');
}

fn write_tokens(out: &mut String, source: &str) {
    match tokenize(source) {
        Err(error) => write_error(out, &error),
        Ok(tokens) => {
            out.push('[');
            for (index, token) in tokens.iter().enumerate() {
                if index > 0 {
                    out.push(',');
                }
                out.push('[');
                write_js_string(out, token.kind.name());
                out.push(',');
                write_js_string(out, &token.text);
                out.push(',');
                match &token.spelling {
                    Some(spelling) => write_js_string(out, spelling),
                    None => out.push_str("null"),
                }
                let _ = write!(
                    out,
                    ",{},{},{}]",
                    token.line, token.column, token.end_column
                );
            }
            out.push(']');
        }
    }
}

fn main() -> ExitCode {
    let mode = std::env::args().nth(1).unwrap_or_default();
    if mode != "tokens" {
        eprintln!("usage: front-dump tokens < paths");
        return ExitCode::from(2);
    }
    let mut output = stdout().lock();
    for path in stdin().lock().lines().map_while(Result::ok) {
        let source = match std::fs::read(&path) {
            Ok(bytes) => String::from_utf8_lossy(&bytes).into_owned(),
            Err(error) => {
                eprintln!("{path}: {error}");
                return ExitCode::FAILURE;
            }
        };
        let mut line = String::new();
        write_tokens(&mut line, &source);
        line.push('\n');
        if output.write_all(line.as_bytes()).is_err() {
            return ExitCode::FAILURE;
        }
    }
    ExitCode::SUCCESS
}
