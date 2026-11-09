//! Writes what the front end makes of each file named on standard input, one JSON line per file,
//! for `scripts/front-differential.ts` to compare with the TypeScript front end:
//!
//! - `front-dump tokens` writes each module's tokens as `[kind, text, spelling, line, column,
//!   endColumn]`, or the syntax error the lexer raises;
//! - `front-dump ast` writes the module `parseModule` reads, as canonical JSON, or its error;
//! - `front-dump sany-ast` does the same for `parseSanyModule`;
//! - `front-dump config` writes the model configuration `parseConfig` reads from each file, for
//!   TLC master and 1.7.4, or the error it raises;
//! - `front-dump time` writes the best of five times to tokenize and parse each module, in
//!   milliseconds.

use std::fmt::Write as _;
use std::io::{BufRead, Write, stdin, stdout};
use std::process::ExitCode;

use tla_front::TlcVersion;
use tla_front::config::parse_config;
use tla_front::dump;
use tla_front::json::write_js_string;
use tla_front::lexer::tokenize;
use tla_front::parser::{parse_module, parse_sany_module};

fn write_tokens(out: &mut String, source: &str) {
    match tokenize(source) {
        Err(error) => dump::syntax_error(&error).write(out),
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

fn write_module(out: &mut String, source: &str, is_sany: bool) {
    let parsed = if is_sany {
        parse_sany_module(source, None, TlcVersion::Master)
    } else {
        parse_module(source)
    };
    match parsed {
        Ok(module) => dump::module(&module).write(out),
        Err(error) => dump::syntax_error(&error).write(out),
    }
}

fn write_time(out: &mut String, source: &str) {
    let best = (0..5)
        .map(|_| {
            let start = std::time::Instant::now();
            std::hint::black_box(parse_module(source)).ok();
            start.elapsed().as_secs_f64() * 1000.0
        })
        .fold(f64::INFINITY, f64::min);
    let _ = write!(out, "{best:.4}");
}

fn main() -> ExitCode {
    let mode = std::env::args().nth(1).unwrap_or_default();
    let write: fn(&mut String, &str) = match mode.as_str() {
        "tokens" => write_tokens,
        "ast" => |out, source| write_module(out, source, false),
        "sany-ast" => |out, source| write_module(out, source, true),
        "time" => write_time,
        "config" => |out, source| {
            out.push_str("{\"master\":");
            dump::config(&parse_config(source, TlcVersion::Master)).write(out);
            out.push_str(",\"v174\":");
            dump::config(&parse_config(source, TlcVersion::V1_7_4)).write(out);
            out.push('}');
        },
        _ => {
            eprintln!("usage: front-dump tokens|ast|sany-ast|config|time < paths");
            return ExitCode::from(2);
        }
    };
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
        write(&mut line, &source);
        line.push('\n');
        if output.write_all(line.as_bytes()).is_err() {
            return ExitCode::FAILURE;
        }
    }
    ExitCode::SUCCESS
}
