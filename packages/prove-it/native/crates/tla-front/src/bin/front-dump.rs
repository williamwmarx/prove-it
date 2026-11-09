//! Writes what the front end makes of each file named on standard input, one JSON line per file,
//! for `scripts/front-differential.ts` to compare with the TypeScript front end:
//!
//! - `front-dump tokens` writes each module's tokens as `[kind, text, spelling, line, column,
//!   endColumn]`, or the syntax error the lexer raises;
//! - `front-dump ast` writes the module `parseModule` reads, as canonical JSON, or its error;
//! - `front-dump sany-ast` does the same for `parseSanyModule`;
//! - `front-dump config` writes the model configuration `parseConfig` reads from each file, for
//!   TLC master and 1.7.4, or the error it raises;
//! - `front-dump resolve [--library <directory>]` links each file as the root module of a spec,
//!   as `createEnvironment` does without a model, reading the modules it imports from the file's
//!   directory and then the library directory, and writes the environment as canonical JSON;
//! - `front-dump model [--library <directory>]` reads lines of a configuration's path, a tab and
//!   its spec's path, and writes the environment of each model as `resolve` does;
//! - `front-dump ir [--library <directory>]` links each file as `resolve` does and writes, in
//!   hex, the IR of a model whose configuration names every definition as an invariant;
//! - `front-dump order [--library <directory>]` reads lines as `model` does and writes TLC's
//!   string order for each model, the root module's variables and constants in SANY's order, and
//!   its definitions in the order TLC computes them;
//! - `front-dump model-ir [--library <directory>]` reads lines as `model` does and writes the IR
//!   of each model's environment as `ir` does, with the texts ranked in TLC's string order;
//! - `front-dump time` writes the best of five times to tokenize and parse each module, in
//!   milliseconds.

use std::fmt::Write as _;
use std::io::{BufRead, Write, stdin, stdout};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use std::rc::Rc;
use tla_front::TlcVersion;
use tla_front::config::parse_config;
use tla_front::dump;

use tla_front::ast::{Expression, ExpressionKind, Location};
use tla_front::dependencies::create_definition_facts;
use tla_front::environment::{Environment, EnvironmentOptions, create_environment};
use tla_front::errors::FrontError;
use tla_front::json::write_js_string;
use tla_front::lexer::tokenize;
use tla_front::lower::{Lowering, RankedTexts};
use tla_front::model::{ModelOptions, lower_model};
use tla_front::order::TlcOrder;
use tla_front::parser::{parse_module, parse_sany_module};
use tla_front::spec::{get_properties, get_specification};
use tla_ir::Model;

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

/// A module's text from the spec's directory, or else the library's.
fn load(path: &Path, library: Option<&Path>, name: &str) -> Option<String> {
    let directory = path.parent().unwrap_or(Path::new("."));
    let file = format!("{name}.tla");
    std::fs::read_to_string(directory.join(&file))
        .ok()
        .or_else(|| library.and_then(|library| std::fs::read_to_string(library.join(&file)).ok()))
}

/// Links the spec at `path` with the configuration `config`, or as SANY does without one.
fn link(
    source: &str,
    path: &Path,
    library: Option<&Path>,
    config: Option<&str>,
) -> Result<Environment, FrontError> {
    let load_module = |name: &str| load(path, library, name);
    let parsed = match config {
        None => parse_config("", TlcVersion::Master),
        Some(text) => parse_config(text, TlcVersion::Master),
    };
    parsed
        .map_err(|error| FrontError::Config(error.message))
        .and_then(|model| {
            create_environment(&EnvironmentOptions {
                source,
                load_module: &load_module,
                config: &model,
                is_unconfigured: config.is_none(),
                version: TlcVersion::Master,
            })
        })
}

fn write_environment(
    out: &mut String,
    source: &str,
    path: &Path,
    library: Option<&Path>,
    config: Option<&str>,
) {
    dump::environment(&link(source, path, library, config)).write(out);
}

/// The IR of a model whose Init and Next are a placeholder and whose configuration names each
/// definition of the environment, by key, as an invariant, so it holds every definition.
fn lower_definitions(
    environment: &Environment,
    ranked: RankedTexts,
) -> Result<Vec<u8>, FrontError> {
    let mut lowering = Lowering::new(environment, ranked);
    let root = Rc::new(Expression::new(
        ExpressionKind::Number {
            value: 0.0,
            text: Rc::from("0"),
        },
        Location {
            line: 0,
            column: 0,
            range: None,
        },
    ));
    let init = lowering.write_root(&root)?;
    let next = lowering.write_root(&root)?;
    let invariants = environment
        .definitions
        .keys()
        .map(|key| lowering.config_name(key))
        .collect();
    let model = Model {
        init,
        next,
        scope: None,
        actions: Vec::new(),
        is_labelled: false,
        invariants,
        property_invariants: Vec::new(),
        property_invariant_names: Vec::new(),
        constraints: Vec::new(),
        action_constraints: Vec::new(),
        possible: Vec::new(),
        action_properties: Vec::new(),
        initial_predicates: Vec::new(),
        view: None,
        alias: None,
        postconditions: Vec::new(),
        symmetry: None,
        check_deadlock: true,
        is_warning_enabled: true,
        is_recording_graph: false,
        version: None,
        // TLC's default seed, 0, and java.util.Random seeded with it, which no assumption has drawn
        // from: the model `ir.ts` writes for an environment that evaluated nothing at startup.
        random_seed: 0,
        startup_random: 0x5_DEEC_E66D,
        atoms: Vec::new(),
        live_formula: Vec::new(),
        live_properties: Vec::new(),
    };
    Ok(tla_ir::encode(&lowering.finish(model)?))
}

fn write_lowered(out: &mut String, source: &str, path: &Path, library: Option<&Path>) {
    let lowered = link(source, path, library, None).and_then(|environment| {
        lower_definitions(
            &environment,
            RankedTexts {
                texts: &[],
                ranks: Default::default(),
            },
        )
    });
    write_ir(out, lowered);
}

fn write_ir(out: &mut String, lowered: Result<Vec<u8>, FrontError>) {
    match lowered {
        Ok(bytes) => {
            out.push_str("{\"ir\":\"");
            for byte in bytes {
                let _ = write!(out, "{byte:02x}");
            }
            out.push_str("\"}");
        }
        Err(error) => dump::environment(&Err(error)).write(out),
    }
}

/// The IR of a model's environment, with the texts ranked in TLC's string order, as `ir` writes a
/// module's.
fn write_model_ir(out: &mut String, config: &str, spec_path: &Path, library: Option<&Path>) {
    let source = std::fs::read_to_string(spec_path).unwrap_or_default();
    let load_module = |name: &str| load(spec_path, library, name);
    let lowered = parse_config(config, TlcVersion::Master)
        .map_err(|error| FrontError::Config(error.message))
        .and_then(|model| {
            let strings = TlcOrder::new(&source, &load_module, TlcVersion::Master)?
                .get_string_order(&model)?;
            let texts: Vec<Rc<str>> = strings.iter().map(|text| Rc::from(text.as_str())).collect();
            let environment = create_environment(&EnvironmentOptions {
                source: &source,
                load_module: &load_module,
                config: &model,
                is_unconfigured: false,
                version: TlcVersion::Master,
            })?;
            let ranks = texts
                .iter()
                .enumerate()
                .map(|(rank, text)| (text.clone(), rank as u32))
                .collect();
            lower_definitions(
                &environment,
                RankedTexts {
                    texts: &texts,
                    ranks,
                },
            )
        });
    write_ir(out, lowered);
}

/// The IR of a model as `check.ts` lowers it, without TLC's actions, which the engine splits.
fn write_model_full(out: &mut String, config: &str, spec_path: &Path, library: Option<&Path>) {
    let options = ModelOptions {
        library,
        version: None,
        is_warning_enabled: true,
    };
    write_ir(out, lower_model(spec_path, config, &options));
}

/// TLC's orders of a model: its string order, the root module's variables and constants, and the
/// root module's definitions in the order TLC computes them.
fn write_order(out: &mut String, config: &str, spec_path: &Path, library: Option<&Path>) {
    let source = std::fs::read_to_string(spec_path).unwrap_or_default();
    let load_module = |name: &str| load(spec_path, library, name);
    let orders = parse_config(config, TlcVersion::Master)
        .map_err(|error| FrontError::Config(error.message))
        .and_then(|model| {
            let order = TlcOrder::new(&source, &load_module, TlcVersion::Master)?;
            let strings = order.get_string_order(&model)?;
            let variables = order.get_declaration_order(true)?;
            let constants = order.get_declaration_order(false)?;
            let definitions = order.get_definition_order(None)?;
            Ok((strings, variables, constants, definitions))
        });
    let names = |items: &[Rc<str>]| {
        let mut written = String::from("[");
        for (index, item) in items.iter().enumerate() {
            if index > 0 {
                written.push(',');
            }
            write_js_string(&mut written, item);
        }
        written.push(']');
        written
    };
    match orders {
        Ok((strings, variables, constants, definitions)) => {
            let strings: Vec<Rc<str>> =
                strings.iter().map(|text| Rc::from(text.as_str())).collect();
            let _ = write!(
                out,
                "{{\"constants\":{},\"definitions\":{},\"strings\":{},\"variables\":{}}}",
                names(&constants),
                names(&definitions),
                names(&strings),
                names(&variables)
            );
        }
        Err(error) => dump::environment(&Err(error)).write(out),
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
    let arguments: Vec<String> = std::env::args().collect();
    let mode = arguments.get(1).cloned().unwrap_or_default();
    let library: Option<PathBuf> = arguments
        .iter()
        .position(|argument| argument == "--library")
        .and_then(|index| arguments.get(index + 1))
        .map(PathBuf::from);
    let write: fn(&mut String, &str) = match mode.as_str() {
        "resolve" | "model" | "ir" | "order" | "model-ir" | "model-full" | "spec"
        | "properties" => |_, _| {},
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
            eprintln!(
                "usage: front-dump tokens|ast|sany-ast|config|resolve|model|ir|order|model-ir|model-full|spec|properties|time < paths"
            );
            return ExitCode::from(2);
        }
    };
    let mut output = stdout().lock();
    for path in stdin().lock().lines().map_while(Result::ok) {
        let (file, spec_path) = path.split_once('\t').unwrap_or((&path, ""));
        let source = match std::fs::read(file) {
            Ok(bytes) => String::from_utf8_lossy(&bytes).into_owned(),
            Err(error) => {
                eprintln!("{path}: {error}");
                return ExitCode::FAILURE;
            }
        };
        let mut line = String::new();
        if mode == "model-full" {
            write_model_full(&mut line, &source, Path::new(spec_path), library.as_deref());
        } else if mode == "model-ir" {
            write_model_ir(&mut line, &source, Path::new(spec_path), library.as_deref());
        } else if mode == "order" {
            write_order(&mut line, &source, Path::new(spec_path), library.as_deref());
        } else if mode == "ir" {
            write_lowered(&mut line, &source, Path::new(&path), library.as_deref());
        } else if mode == "resolve" {
            write_environment(
                &mut line,
                &source,
                Path::new(&path),
                library.as_deref(),
                None,
            );
        } else if mode == "properties" {
            let spec = std::fs::read_to_string(spec_path).unwrap_or_default();
            let properties = link(
                &spec,
                Path::new(spec_path),
                library.as_deref(),
                Some(&source),
            )
            .and_then(|environment| {
                let config = parse_config(&source, TlcVersion::Master)
                    .map_err(|error| FrontError::Config(error.message))?;
                let facts = create_definition_facts(&environment);
                get_properties(&config, &environment, &facts, TlcVersion::Master)
            });
            dump::properties(&properties).write(&mut line);
        } else if mode == "spec" {
            let spec = std::fs::read_to_string(spec_path).unwrap_or_default();
            let specification = link(
                &spec,
                Path::new(spec_path),
                library.as_deref(),
                Some(&source),
            )
            .and_then(|environment| {
                let config = parse_config(&source, TlcVersion::Master)
                    .map_err(|error| FrontError::Config(error.message))?;
                let facts = create_definition_facts(&environment);
                get_specification(&config, &environment, &facts, TlcVersion::Master)
            });
            dump::specification(&specification).write(&mut line);
        } else if mode == "model" {
            // The line names the configuration and then, after a tab, the spec.
            let spec = std::fs::read_to_string(spec_path).unwrap_or_default();
            write_environment(
                &mut line,
                &spec,
                Path::new(spec_path),
                library.as_deref(),
                Some(&source),
            );
        } else {
            write(&mut line, &source);
        }
        line.push('\n');
        if output.write_all(line.as_bytes()).is_err() {
            return ExitCode::FAILURE;
        }
    }
    ExitCode::SUCCESS
}
