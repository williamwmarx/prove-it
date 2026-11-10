//! Writes the obligations of each module named on standard input, one JSON line per module, for
//! `scripts/obligation-differential.ts` to compare with the TypeScript ones: each result's name,
//! summary and obligations, the warnings in order, and the error that stopped it, if any.
//!
//! `obligations-dump --library <json>` reads `{"modules": {name: path}, "standard": directory}`
//! and finds a module as `readModule` in `scripts/proof-records.ts` does: beside the module, then
//! in `modules`, then in `standard`.

use std::collections::HashMap;
use std::fmt::Write as _;
use std::io::{Read, Write, stdin, stdout};
use std::path::Path;
use std::process::ExitCode;

use prove_obligations::errors::ObligationError;
use prove_obligations::expression::{Channel, ObligationWarning};
use prove_obligations::index::{ObligationSource, format_summary, get_obligations};
use prove_obligations::proof::{ObligationKind, Omission};
use tla_front::json::{write_js_number, write_js_string};

/// The JSON the library file holds: strings and objects, and nothing else that it reads.
enum Json {
    String(String),
    Object(Vec<(String, Json)>),
}

struct JsonReader<'text> {
    characters: std::iter::Peekable<std::str::Chars<'text>>,
}

impl JsonReader<'_> {
    fn skip_space(&mut self) {
        while self
            .characters
            .next_if(|character| character.is_ascii_whitespace())
            .is_some()
        {}
    }

    fn expect(&mut self, expected: char) -> Result<(), String> {
        self.skip_space();
        match self.characters.next() {
            Some(character) if character == expected => Ok(()),
            other => Err(format!("expected {expected:?}, found {other:?}")),
        }
    }

    fn read_hex(&mut self) -> Result<u32, String> {
        let mut value = 0;
        for _ in 0..4 {
            let digit = self
                .characters
                .next()
                .and_then(|character| character.to_digit(16))
                .ok_or("bad \\u escape")?;
            value = value * 16 + digit;
        }
        Ok(value)
    }

    fn read_string(&mut self) -> Result<String, String> {
        self.expect('"')?;
        let mut text = String::new();
        loop {
            match self.characters.next().ok_or("unterminated string")? {
                '"' => return Ok(text),
                '\\' => match self.characters.next().ok_or("unterminated escape")? {
                    'n' => text.push('\n'),
                    't' => text.push('\t'),
                    'r' => text.push('\r'),
                    'b' => text.push('\u{8}'),
                    'f' => text.push('\u{c}'),
                    'u' => {
                        let high = self.read_hex()?;
                        let code = if (0xd800..0xdc00).contains(&high) {
                            if self.characters.next() != Some('\\')
                                || self.characters.next() != Some('u')
                            {
                                return Err("lone surrogate".to_owned());
                            }
                            let low = self.read_hex()?;
                            0x10000 + ((high - 0xd800) << 10) + (low.wrapping_sub(0xdc00) & 0x3ff)
                        } else {
                            high
                        };
                        text.push(char::from_u32(code).ok_or("bad code point")?);
                    }
                    other => text.push(other),
                },
                other => text.push(other),
            }
        }
    }

    fn read_value(&mut self) -> Result<Json, String> {
        self.skip_space();
        if self.characters.peek() == Some(&'"') {
            return Ok(Json::String(self.read_string()?));
        }
        self.expect('{')?;
        let mut entries = Vec::new();
        self.skip_space();
        if self.characters.next_if_eq(&'}').is_some() {
            return Ok(Json::Object(entries));
        }
        loop {
            let key = self.read_string()?;
            self.expect(':')?;
            entries.push((key, self.read_value()?));
            self.skip_space();
            match self.characters.next() {
                Some(',') => {}
                Some('}') => return Ok(Json::Object(entries)),
                other => return Err(format!("expected , or }}, found {other:?}")),
            }
        }
    }
}

struct Library {
    modules: HashMap<String, String>,
    standard: String,
}

fn read_library(path: &str) -> Result<Library, String> {
    let text = std::fs::read_to_string(path).map_err(|error| format!("{path}: {error}"))?;
    let Json::Object(entries) = (JsonReader {
        characters: text.chars().peekable(),
    })
    .read_value()?
    else {
        return Err("the library is not an object".to_owned());
    };
    let mut modules = HashMap::new();
    let mut standard = None;
    for (key, value) in entries {
        match (key.as_str(), value) {
            ("modules", Json::Object(names)) => {
                for (name, path) in names {
                    if let Json::String(path) = path {
                        modules.insert(name, path);
                    }
                }
            }
            ("standard", Json::String(directory)) => standard = Some(directory),
            _ => {}
        }
    }
    Ok(Library {
        modules,
        standard: standard.ok_or("the library has no standard directory")?,
    })
}

/// `readFileSync(path, "utf8")`, which replaces bytes that aren't UTF-8.
fn read_text(path: &Path) -> Option<String> {
    std::fs::read(path)
        .ok()
        .map(|bytes| String::from_utf8_lossy(&bytes).into_owned())
}

fn read_module(library: &Library, path: &str, name: &str) -> Option<ObligationSource> {
    let file_name = format!("{name}.tla");
    let directory = Path::new(path).parent().unwrap_or(Path::new(""));
    let file = [
        Some(directory.join(&file_name)),
        library.modules.get(name).map(Into::into),
        Some(Path::new(&library.standard).join(&file_name)),
    ]
    .into_iter()
    .flatten()
    .find(|candidate| candidate.exists())?;
    Some(ObligationSource {
        file: file.to_string_lossy().into_owned(),
        source: read_text(&file)?,
    })
}

fn get_channel_name(channel: Channel) -> &'static str {
    match channel {
        Channel::Toolbox => "toolbox",
        Channel::ToolboxOnly => "toolboxOnly",
        Channel::Stderr => "stderr",
        Channel::Stdout => "stdout",
    }
}

fn get_kind_name(kind: &ObligationKind) -> &'static str {
    match kind {
        ObligationKind::Main => "Main",
        ObligationKind::Support => "Support",
        ObligationKind::Error(_) => "Error",
        ObligationKind::Omitted(Omission::Implicit) => "Omitted Implicit",
        ObligationKind::Omitted(Omission::Explicit) => "Omitted Explicit",
        ObligationKind::Omitted(Omission::Elsewhere) => "Omitted Elsewhere",
    }
}

fn write_optional_string(out: &mut String, text: Option<&str>) {
    match text {
        Some(text) => write_js_string(out, text),
        None => out.push_str("null"),
    }
}

fn write_error(out: &mut String, error: &ObligationError) {
    out.push_str("{\"name\":");
    write_js_string(out, error.name());
    out.push_str(",\"message\":");
    write_js_string(out, error.message());
    if let ObligationError::Proof {
        failure, exception, ..
    } = error
    {
        if let Some(failure) = failure {
            out.push_str(",\"failure\":");
            write_js_string(out, failure);
        }
        out.push_str(",\"exception\":");
        write_js_string(out, exception);
    }
    out.push('}');
}

/// `writeModule` of the differential script.
fn write_module(out: &mut String, library: &Library, path: &str) {
    let mut warnings: Vec<ObligationWarning> = Vec::new();
    let outcome = match read_text(Path::new(path)) {
        None => Err(ObligationError::Syntax(format!("cannot read {path}"))),
        Some(source) => get_obligations(
            &[ObligationSource {
                file: path.to_owned(),
                source,
            }],
            &mut |name| read_module(library, path, name),
            None,
            &mut |warning| warnings.push(warning),
        ),
    };
    out.push_str("{\"results\":[");
    for (index, result) in outcome.iter().flatten().enumerate() {
        if index > 0 {
            out.push(',');
        }
        out.push_str("{\"name\":");
        write_js_string(out, &result.name);
        out.push_str(",\"summary\":");
        write_js_string(out, &format_summary(result));
        out.push_str(",\"obligations\":[");
        for (position, obligation) in result.obligations.iter().enumerate() {
            if position > 0 {
                out.push(',');
            }
            let _ = write!(out, "{{\"id\":{},\"location\":", obligation.id);
            write_js_string(out, &obligation.location);
            out.push_str(",\"kind\":");
            write_js_string(out, get_kind_name(&obligation.kind));
            out.push_str(",\"method\":");
            match &obligation.method {
                None => out.push_str("null"),
                Some(method) => {
                    out.push('[');
                    write_js_string(out, &method.name);
                    out.push(',');
                    write_optional_string(out, method.tactic.as_deref());
                    out.push(',');
                    match method.timeout {
                        Some(timeout) => write_js_number(out, timeout),
                        None => out.push_str("null"),
                    }
                    out.push(']');
                }
            }
            out.push_str(",\"text\":");
            write_js_string(out, &obligation.text);
            out.push('}');
        }
        out.push_str("]}");
    }
    out.push_str("],\"warnings\":[");
    for (index, warning) in warnings.iter().enumerate() {
        if index > 0 {
            out.push(',');
        }
        out.push('[');
        write_js_string(out, get_channel_name(warning.channel));
        out.push(',');
        write_js_string(out, &warning.text);
        out.push(']');
    }
    out.push_str("],\"error\":");
    match &outcome {
        Ok(_) => out.push_str("null"),
        Err(error) => write_error(out, error),
    }
    out.push('}');
}

fn run() -> Result<(), String> {
    let arguments: Vec<String> = std::env::args().collect();
    let library_path = arguments
        .iter()
        .position(|argument| argument == "--library")
        .and_then(|index| arguments.get(index + 1))
        .ok_or("usage: obligations-dump --library <json>")?;
    let library = read_library(library_path)?;
    let mut input = String::new();
    stdin()
        .read_to_string(&mut input)
        .map_err(|error| error.to_string())?;
    let mut output = stdout().lock();
    for path in input.lines().filter(|line| !line.is_empty()) {
        let mut line = String::new();
        write_module(&mut line, &library, path);
        line.push('\n');
        output
            .write_all(line.as_bytes())
            .map_err(|error| error.to_string())?;
    }
    output.flush().map_err(|error| error.to_string())
}

fn main() -> ExitCode {
    // The obligations recurse on the depth of expressions and proofs, as the TypeScript does.
    let worker = std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(run)
        .map_err(|error| error.to_string());
    match worker.and_then(|handle| {
        handle
            .join()
            .map_err(|_| "obligations-dump panicked".to_owned())?
    }) {
        Ok(()) => ExitCode::SUCCESS,
        Err(message) => {
            eprintln!("{message}");
            ExitCode::FAILURE
        }
    }
}
