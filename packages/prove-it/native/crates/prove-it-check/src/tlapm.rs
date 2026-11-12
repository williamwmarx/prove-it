//! `prove-it tlapm …`: tlapm's command line (`Tlapm_lib.main`), with Prove It's obligations and
//! back ends, as `src/cli/tlapm.ts` ran it. It prints what tlapm prints, on stdout, on stderr and
//! in the toolbox's protocol, and keeps tlapm's cache: each module's theory and fingerprints file,
//! and the fingerprints file's history.
//!
//! The obligations recurse as deep as the proofs nest and share their terms by `Rc`, so the run
//! goes on a thread of its own with a deep stack, which reaches the host and the output only
//! through `Io`. Each decision runs on a thread of the `--threads` pool; in WebAssembly, everything
//! runs in place.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::sync::mpsc::channel;

use prove_it_prover::driver::{
    Answer, Attempt, Cache, Report, Round, Settings, Status, prove_obligations_with,
};
use prove_it_prover::tlapm_cache::{FingerprintTable, KnownResults, LocalTime, load_fingerprints};
use prove_it_prover::{Cancel, DecideError, Limits, Statistic, Verdict};
use prove_obligations::errors::ObligationError;
use prove_obligations::expression::{Channel, get_at_prefix, get_locus_text};
use prove_obligations::format::{format, render_doc};
use prove_obligations::generate::LineRange;
use prove_obligations::index::{
    ModuleObligations, ObligationSource, PrintedObligation, WHOLE_MODULE, format_summary,
    get_obligations,
};
use prove_obligations::prep::normalize::{expand_defs, normalize_expand, normalize_sequent};
use prove_obligations::printer::{format_obligation, print_sequent};
use prove_obligations::proof::ObligationKind;
use prove_obligations::ship::{ProofAttempt, encode_proof_theory};
use prove_obligations::tlaps_module::TLAPS_MODULE;
use tla_engine::clock::Instant;

use crate::check::not_native;
use crate::host::{Entry, Host, PathKind};
use crate::messages::Output;
use crate::outcome::Outcome;
use crate::overlay::Overlay;
use crate::time::civil_from_days;

const TLAPM_VERSION: &str = "9ed0376";

/// The options `src/cli/options.ts` names in `TLAPM_COMMAND`, with how many values each takes.
const OPTIONS: [(&str, usize); 17] = [
    ("-N", 0),
    ("--summary", 0),
    ("--strict", 0),
    ("--toolbox", 2),
    ("--line", 1),
    ("--printallobs", 0),
    ("--threads", 1),
    ("--version", 0),
    ("-I", 1),
    ("-k", 0),
    ("--noproving", 0),
    ("--nofp", 0),
    ("--nofpl", 2),
    ("--safefp", 0),
    ("--cleanfp", 0),
    ("--usefp", 1),
    ("--cache-dir", 1),
];

const INTEGER_OPTIONS: [&str; 4] = ["--toolbox", "--line", "--threads", "--nofpl"];

const GLOB_CHARACTERS: [char; 4] = ['*', '?', '[', '{'];

// Schedule.run's bounds on --threads.
const MAXIMUM_THREADS: i64 = 99;

// The most severe first.
const STRICT_FAILED: i32 = 10;
const STRICT_INCOMPLETE: i32 = 11;
const STRICT_EMPTY_TARGET: i32 = 12;

const FAILURE_STATUS: i32 = 3;

const UNPROVED_ENDING: &str = concat!(
    " tlapm ending abnormally with Failure(\"backend errors: there are unproved obligations\")\n",
    "Raised at Stdlib.failwith in file \"stdlib.ml\", line 29, characters 17-33\n",
    "Called from Tlapm_lib.process_module in file \"src/tlapm_lib.ml\", lines 492-493, characters 12-37\n",
    "Called from Tlapm_lib.main.f in file \"src/tlapm_lib.ml\", line 640, characters 23-43\n",
    "Called from Stdlib__List.fold_left in file \"list.ml\", line 125, characters 24-34\n",
    "Called from Tlapm_lib.main in file \"src/tlapm_lib.ml\", line 643, characters 13-40\n",
    "Called from Tlapm_lib.init in file \"src/tlapm_lib.ml\", line 659, characters 8-59\n",
);

// Fpfile.fp_init keeps this many runs of history.
const HISTORY_SIZE: usize = 10;

#[cfg(not(target_arch = "wasm32"))]
const PROVE_STACK_BYTES: usize = 256 * 1024 * 1024;

const PACKAGE: &str = include_str!("../../../../package.json");

/// What the fingerprints file stores as the versions of tlapm, Zenon and Isabelle, which --safefp
/// compares: Prove It's own, `tla-ts <package version>`.
fn get_stored_version() -> String {
    let version = PACKAGE
        .split_once("\"version\": \"")
        .and_then(|(_, rest)| rest.split_once('"'))
        .map_or("", |(version, _)| version);
    format!("tla-ts {version}")
}

/// Why the run stops without tlapm's output: what Prove It can't do as tlapm does yet.
struct Decline(String);

type Run<T> = Result<T, Decline>;

fn decline<T>(reason: impl Into<String>) -> Run<T> {
    Err(Decline(reason.into()))
}

type Call<'a> = Box<dyn FnOnce(&mut Session<'_>) + Send + 'a>;

/// What the run reaches on the thread that holds the output: the output, which holds back what the
/// run prints, and the overlay, which holds back what it writes.
struct Session<'o> {
    output: Output<'o>,
    overlay: Overlay,
}

impl Session<'_> {
    fn host(&self) -> &dyn Host {
        self.output.host
    }

    fn get_kind(&self, path: &Path) -> Option<PathKind> {
        self.overlay.get_kind(path, self.output.host)
    }

    fn read(&self, path: &Path) -> Option<Vec<u8>> {
        self.overlay.read(path, self.output.host)
    }
}

/// How the run reaches the session from its own thread: each call runs on the thread that holds it.
struct Io<'a> {
    send: Box<dyn Fn(Call<'a>) + 'a>,
}

impl<'a> Io<'a> {
    fn call<R: Send + 'a>(&self, work: impl FnOnce(&mut Session<'_>) -> R + Send + 'a) -> R {
        let (answer, answered) = channel();
        (self.send)(Box::new(move |session| {
            let _ = answer.send(work(session));
        }));
        answered.recv().expect("the output's thread answers")
    }

    fn out(&self, text: String) {
        self.call(move |session| {
            let _ = session.output.out.write_all(text.as_bytes());
        });
    }

    fn err(&self, text: String) {
        self.call(move |session| {
            let _ = session.output.err.write_all(text.as_bytes());
        });
    }

    fn get_kind(&self, path: &str) -> Option<PathKind> {
        let path = PathBuf::from(path);
        self.call(move |session| session.get_kind(&path))
    }

    fn exists(&self, path: &str) -> bool {
        self.get_kind(path).is_some()
    }
}

/// What the run printed, on stdout and on stderr, in the order it printed it.
#[derive(Default)]
struct Recording {
    chunks: RefCell<Vec<(bool, Vec<u8>)>>,
}

struct Recorder<'r> {
    recording: &'r Recording,
    is_err: bool,
}

impl Write for Recorder<'_> {
    fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
        let mut chunks = self.recording.chunks.borrow_mut();
        match chunks.last_mut() {
            Some((is_err, chunk)) if *is_err == self.is_err => chunk.extend_from_slice(bytes),
            _ => chunks.push((self.is_err, bytes.to_vec())),
        }
        Ok(bytes.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

/// Runs tlapm's command line `args`, without the word `tlapm`, and returns its exit status. A run
/// either prints and writes what tlapm does or declines as a whole: it holds back what it prints
/// and writes until it ends, then has the host apply the file operations in order and prints.
pub fn run(args: &[String], output: &mut Output<'_>) -> i32 {
    let recording = Recording::default();
    let (result, overlay) = {
        let mut out = Recorder {
            recording: &recording,
            is_err: false,
        };
        let mut err = Recorder {
            recording: &recording,
            is_err: true,
        };
        let mut session = Session {
            output: Output {
                out: &mut out,
                err: &mut err,
                host: output.host,
                outcome: Outcome::default(),
            },
            overlay: Overlay::default(),
        };
        let result = run_in_place(args, &mut session);
        (result, session.overlay)
    };
    let status = match result {
        Ok(status) => status,
        Err(Decline(reason)) => return not_native(output, &reason),
    };
    for operation in overlay.into_journal() {
        if !output.host.apply(&operation) {
            return not_native(output, &operation.get_failure());
        }
    }
    for (is_err, chunk) in recording.chunks.into_inner() {
        let _ = if is_err {
            output.err.write_all(&chunk)
        } else {
            output.out.write_all(&chunk)
        };
    }
    status
}

#[cfg(target_arch = "wasm32")]
fn run_in_place(args: &[String], session: &mut Session<'_>) -> Run<i32> {
    let session = RefCell::new(session);
    let io = Io {
        send: Box::new(|call: Call<'_>| call(&mut session.borrow_mut())),
    };
    run_tlapm(&io, args)
}

#[cfg(not(target_arch = "wasm32"))]
fn run_in_place(args: &[String], session: &mut Session<'_>) -> Run<i32> {
    std::thread::scope(|scope| {
        let (calls, received) = channel::<Call<'_>>();
        let running = std::thread::Builder::new()
            .name("prove-it tlapm".into())
            .stack_size(PROVE_STACK_BYTES)
            .spawn_scoped(scope, move || {
                let io = Io {
                    send: Box::new(move |call| calls.send(call).expect("the output's thread")),
                };
                run_tlapm(&io, args)
            });
        let Ok(running) = running else {
            return decline("a thread for tlapm's run, which the system refuses");
        };
        for call in received {
            call(session);
        }
        running
            .join()
            .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
    })
}

/// Where OCaml's `Arg` stops reading tlapm's command line before its end: at `--version`, which
/// prints the version and exits, or at what tlapm reports or ends abnormally on, which Prove It
/// declines.
enum Stop {
    Version,
    Decline(String),
}

struct Parsed {
    options: Vec<(String, Vec<String>)>,
    positionals: Vec<String>,
    stop: Option<Stop>,
}

impl Parsed {
    // Arg.parse_argv: each option in turn, until one stops it.
    fn parse(args: &[String]) -> Parsed {
        let mut parsed = Parsed {
            options: Vec::new(),
            positionals: Vec::new(),
            stop: None,
        };
        let mut index = 0;
        while index < args.len() && parsed.stop.is_none() {
            let arg = &args[index];
            index += 1;
            let Some(&(_, arity)) = OPTIONS.iter().find(|(name, _)| name == arg) else {
                if arg.starts_with('-') {
                    parsed.stop = Some(Stop::Decline(format!("the tlapm option {arg}")));
                } else {
                    parsed.positionals.push(arg.clone());
                }
                continue;
            };
            let values: Vec<String> = args[index..].iter().take(arity).cloned().collect();
            index += values.len();
            parsed.stop = parsed.check(arg, &values);
            parsed.options.push((arg.clone(), values));
        }
        parsed
    }

    // What Arg reports, or what the option's action raises.
    fn check(&self, name: &str, values: &[String]) -> Option<Stop> {
        let arity = OPTIONS
            .iter()
            .find(|(option, _)| *option == name)
            .map_or(0, |(_, arity)| *arity);
        if values.len() < arity {
            return Some(Stop::Decline(format!(
                "tlapm's report of {name} without its arguments"
            )));
        }
        if INTEGER_OPTIONS.contains(&name) && values.iter().any(|value| parse_int(value).is_none())
        {
            return Some(Stop::Decline(format!(
                "tlapm's report of {name} without an integer"
            )));
        }
        match name {
            "--version" => Some(Stop::Version),
            // Tlapm_args.set_max_threads raises Arg.Bad.
            "--threads" if parse_int(&values[0]).is_some_and(|threads| threads < 0) => {
                Some(Stop::Decline(format!(
                    "tlapm's report of --threads {}, which it refuses",
                    values[0]
                )))
            }
            // Params.add_search_dir reads the directory's first character.
            "-I" if values[0].is_empty() => Some(Stop::Decline(
                "the backtrace tlapm prints as it ends with -I \"\"".to_owned(),
            )),
            _ => None,
        }
    }

    fn has(&self, name: &str) -> bool {
        self.options.iter().any(|(option, _)| option == name)
    }

    fn get(&self, name: &str) -> Option<&[String]> {
        self.options
            .iter()
            .rfind(|(option, _)| option == name)
            .map(|(_, values)| values.as_slice())
    }

    fn get_integers(&self, name: &str) -> Option<Vec<i64>> {
        self.get(name).map(|values| {
            values
                .iter()
                .map(|value| parse_int(value).unwrap_or_default())
                .collect()
        })
    }
}

// OCaml's max_int, the largest of its 63-bit integers.
const OCAML_MAX_INT: i64 = (1 << 62) - 1;

/// OCaml's `int_of_string` (`parse_intnat` in runtime/ints.c): a sign, a prefix `0x`, `0o`, `0b` or
/// `0u`, and digits, with `_` after the first; a decimal must fit in 63 bits, and a prefixed one in
/// 63 bits unsigned, which wraps.
fn parse_int(text: &str) -> Option<i64> {
    let bytes = text.as_bytes();
    let (is_negative, mut rest) = match bytes.first() {
        Some(b'-') => (true, &bytes[1..]),
        Some(b'+') => (false, &bytes[1..]),
        _ => (false, bytes),
    };
    let (base, is_signed) = match rest {
        [b'0', b'x' | b'X', ..] => (16, false),
        [b'0', b'o' | b'O', ..] => (8, false),
        [b'0', b'b' | b'B', ..] => (2, false),
        [b'0', b'u' | b'U', ..] => (10, false),
        _ => (10, true),
    };
    if !is_signed {
        rest = &rest[2..];
    }
    let digit = |byte: u8| char::from(byte).to_digit(16).filter(|digit| *digit < base);
    let (first, rest) = rest.split_first()?;
    let mut value = u64::from(digit(*first)?);
    for byte in rest {
        if *byte == b'_' {
            continue;
        }
        let digit = digit(*byte)?;
        value = value
            .checked_mul(u64::from(base))?
            .checked_add(u64::from(digit))?;
    }
    let limit = 1_u64 << 62;
    if is_signed {
        if value > limit || (value == limit && !is_negative) {
            return None;
        }
    } else if value >= limit << 1 {
        return None;
    }
    let value = if is_negative {
        value.wrapping_neg()
    } else {
        value
    };
    // Val_long keeps the low 63 bits.
    Some(((value << 1) as i64) >> 1)
}

/// OCaml's `+` on its 63-bit integers, which wraps.
fn add_ocaml(left: i64, right: i64) -> i64 {
    (left.wrapping_add(right) << 1) >> 1
}

/// Tlapm_args.quote_if_needed.
fn quote_shell_argument(arg: &str) -> String {
    let is_plain = !arg.is_empty()
        && arg
            .chars()
            .all(|character| character.is_ascii_alphanumeric() || "+,-./:=@_".contains(character));
    if is_plain {
        arg.to_owned()
    } else {
        format!("'{}'", arg.replace('\'', "'\\''"))
    }
}

/// OCaml's `%S`: a string in quotes, as String.escaped writes it.
fn quote_ocaml(text: &str) -> String {
    let mut quoted = String::from("\"");
    for byte in text.bytes() {
        match byte {
            b'"' => quoted.push_str("\\\""),
            b'\\' => quoted.push_str("\\\\"),
            b'\n' => quoted.push_str("\\n"),
            b'\t' => quoted.push_str("\\t"),
            b'\r' => quoted.push_str("\\r"),
            8 => quoted.push_str("\\b"),
            b' '..=b'~' => quoted.push(char::from(byte)),
            other => quoted.push_str(&format!("\\{other:03}")),
        }
    }
    quoted.push('"');
    quoted
}

/// C's `%g`: six significant digits, without trailing zeros, in exponent form outside 1e-4 to 1e6.
fn format_general(value: f64) -> String {
    if value.is_nan() {
        return "nan".to_owned();
    }
    if value.is_infinite() {
        return if value > 0.0 { "inf" } else { "-inf" }.to_owned();
    }
    if value == 0.0 {
        return if value.is_sign_negative() { "-0" } else { "0" }.to_owned();
    }
    let scientific = format!("{value:.5e}");
    let (mantissa, exponent) = scientific.split_once('e').expect("an exponent");
    let exponent: i32 = exponent.parse().expect("an exponent");
    let trim = |text: &str| {
        if text.contains('.') {
            text.trim_end_matches('0').trim_end_matches('.').to_owned()
        } else {
            text.to_owned()
        }
    };
    if !(-4..6).contains(&exponent) {
        let sign = if exponent < 0 { '-' } else { '+' };
        return format!("{}e{sign}{:02}", trim(mantissa), exponent.abs());
    }
    let decimals = usize::try_from(5 - exponent).unwrap_or(0);
    trim(&format!("{value:.decimals$}"))
}

/// Node's `path.posix.dirname`.
fn get_dirname(path: &str) -> String {
    let bytes = path.as_bytes();
    if bytes.is_empty() {
        return ".".to_owned();
    }
    let has_root = bytes[0] == b'/';
    let mut end = None;
    let mut is_slash_matched = true;
    for index in (1..bytes.len()).rev() {
        if bytes[index] == b'/' {
            if !is_slash_matched {
                end = Some(index);
                break;
            }
        } else {
            is_slash_matched = false;
        }
    }
    match end {
        None if has_root => "/".to_owned(),
        None => ".".to_owned(),
        Some(1) if has_root => "//".to_owned(),
        Some(end) => path[..end].to_owned(),
    }
}

/// Node's `path.posix.join` of two paths: joined by a slash, then normalized.
fn join_paths(left: &str, right: &str) -> String {
    let joined = match (left.is_empty(), right.is_empty()) {
        (true, true) => return ".".to_owned(),
        (true, false) => right.to_owned(),
        (false, true) => left.to_owned(),
        (false, false) => format!("{left}/{right}"),
    };
    let is_absolute = joined.starts_with('/');
    let is_directory = joined.ends_with('/');
    let mut parts: Vec<&str> = Vec::new();
    for part in joined.split('/') {
        match part {
            "" | "." => {}
            ".." if parts.last().is_some_and(|last| *last != "..") => {
                parts.pop();
            }
            ".." if is_absolute => {}
            other => parts.push(other),
        }
    }
    let mut normalized = parts.join("/");
    if normalized.is_empty() && !is_absolute {
        normalized.push('.');
    }
    if is_directory && !normalized.is_empty() {
        normalized.push('/');
    }
    if is_absolute {
        format!("/{normalized}")
    } else {
        normalized
    }
}

// A message of tlapm's toolbox protocol, which it writes to stderr.
fn format_toolbox_message(fields: &[String]) -> String {
    let mut message = String::from("@!!BEGIN\n");
    for field in fields {
        message.push_str(&format!("@!!{field}\n"));
    }
    message.push_str("@!!END\n\n");
    message
}

fn format_obligation_message(
    obligation: &PrintedObligation,
    status: &str,
    fields: Vec<String>,
) -> String {
    let mut all = vec![
        "type:obligation".to_owned(),
        format!("id:{}", obligation.id),
        format!("loc:{}", obligation.location),
        format!("status:{status}"),
    ];
    all.extend(fields);
    format_toolbox_message(&all)
}

/// The local time now.
fn get_local_time(host: &dyn Host) -> LocalTime {
    let utc = host
        .now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |duration| duration.as_secs() as i64);
    let seconds = utc + host.zone().offset(utc);
    let (days, second) = (seconds.div_euclid(86_400), seconds.rem_euclid(86_400));
    let (year, month, day) = civil_from_days(days);
    LocalTime {
        year,
        month: month - 1,
        day,
        hours: second / 3600,
        minutes: second / 60 % 60,
        seconds: second % 60,
    }
}

fn get_obligation_error(error: &ObligationError) -> Decline {
    Decline(format!("{}: {}", error.name(), error.message()))
}

fn run_tlapm(io: &Io<'_>, args: &[String]) -> Run<i32> {
    let parsed = Parsed::parse(args);
    let is_processing = !parsed.has("-N") && !parsed.has("--summary");
    match parsed.stop {
        Some(Stop::Version) => {
            io.out(format!("{TLAPM_VERSION}\n"));
            return Ok(0);
        }
        Some(Stop::Decline(reason)) => return decline(reason),
        None => {}
    }
    if is_processing && parsed.has("--printallobs") {
        return decline("--printallobs where tlapm proves");
    }
    if parsed
        .positionals
        .iter()
        .any(|path| path.contains(GLOB_CHARACTERS))
    {
        return decline("globs");
    }
    let files = &parsed.positionals;
    if files.is_empty() {
        return decline("tlapm's report of a command line without a module");
    }
    // Schedule.run asserts that it has from 1 to 99 threads; the default is the processor count.
    let threads = match parsed.get_integers("--threads") {
        Some(threads) => threads[0],
        None => io.call(|session| session.host().machine().cores) as i64,
    };
    if is_processing && !(1..=MAXIMUM_THREADS).contains(&threads) {
        return decline(match parsed.get("--threads") {
            Some(_) => format!("--threads {threads}, which tlapm refuses"),
            None => format!("{threads} processors, more threads than tlapm takes"),
        });
    }
    let threads = usize::try_from(threads).unwrap_or(1).max(1);
    let module_paths: Vec<String> = files
        .iter()
        .map(|path| {
            if path.ends_with(".tla") {
                path.clone()
            } else {
                format!("{path}.tla")
            }
        })
        .collect();
    let is_toolbox = parsed.has("--toolbox") || parsed.has("--line");
    if is_toolbox {
        // tlapm prints its own command line, which here is Prove It's.
        let command = std::iter::once("prove-it")
            .chain(std::iter::once("tlapm"))
            .chain(args.iter().map(String::as_str))
            .map(quote_shell_argument)
            .collect::<Vec<_>>()
            .join(" ");
        let date = io
            .call(|session| crate::time::format_date(session.host().now(), session.host().zone()));
        io.out(format!(
            "\n\\* TLAPM version {TLAPM_VERSION}\n\\* launched at {date} with command line:\n\\* {command}\n\n"
        ));
    }
    // Like tlapm, the last of --toolbox and --line wins, and a 0 means the whole module.
    let mut lines = WHOLE_MODULE;
    for (name, values) in &parsed.options {
        let numbers: Vec<i64> = values
            .iter()
            .map(|value| parse_int(value).unwrap_or_default())
            .collect();
        let get_end = |end: i64| {
            if end == 0 || end == OCAML_MAX_INT {
                f64::INFINITY
            } else {
                end as f64
            }
        };
        match name.as_str() {
            "--toolbox" => {
                lines = LineRange {
                    start: numbers[0] as f64,
                    end: get_end(numbers[1]),
                };
            }
            "--line" if numbers[0] == 0 => lines = WHOLE_MODULE,
            "--line" => {
                lines = LineRange {
                    start: numbers[0] as f64,
                    end: get_end(numbers[0]),
                };
            }
            _ => {}
        }
    }
    let search = Search::new(io, &parsed, &module_paths)?;
    prove_it_obligations_reset();
    let generated = generate_obligations(io, files, &module_paths, &search, lines, is_toolbox);
    let (modules, module_names) = match generated {
        Generated::Modules(modules, names) => (modules, names),
        Generated::Declined(reason) => return decline(reason),
    };
    let status = check_modules(
        io,
        &parsed,
        &modules,
        &module_names,
        lines,
        is_toolbox,
        is_processing,
        threads,
    );
    prove_it_obligations_reset();
    status
}

fn prove_it_obligations_reset() {
    prove_obligations::reset_caches();
}

/// tlapm's standard library: lib/tlapm/stdlib beside bin/tlapm, where it holds TLAPS.tla
/// (`Params.stdlib_path`).
fn find_standard_library(io: &Io<'_>) -> Run<Option<String>> {
    let path = io
        .call(|session| session.host().get_variable("PATH"))
        .unwrap_or_default();
    for directory in path.split(':') {
        let tlapm = join_paths(directory, "tlapm");
        if !io.exists(&tlapm) {
            continue;
        }
        let real = {
            let tlapm = PathBuf::from(&tlapm);
            io.call(move |session| session.host().get_real_path(&tlapm))
        };
        let Some(real) = real else {
            return decline(format!("the real path of {tlapm}"));
        };
        let real = real.to_string_lossy().into_owned();
        let library = join_paths(&get_dirname(&get_dirname(&real)), "lib/tlapm/stdlib");
        if io.exists(&concat_paths(&library, "TLAPS.tla")) {
            return Ok(Some(library));
        }
    }
    Ok(None)
}

/// Where tlapm looks for a module's file: `M_save.file_search'` in the current directory, each -I
/// directory in the order given and the standard library, and where none has it, `Loader` in the
/// directories of the command line's modules, the current directory, the standard library and
/// each -I directory, the last given first (`Tlapm_lib.setup_loader`).
struct Search {
    directories: Vec<String>,
    loader: Vec<String>,
}

/// A module's file as tlapm finds it: the path it reads and names it by, or, where `Loader` read
/// it, the path it read and the name it was asked for, which it names it by.
struct Found {
    path: String,
    name: String,
    is_loaded: bool,
}

impl Search {
    // Params.add_search_dir keeps the standard library first and puts each new directory after it,
    // so that it ends last of all, and the -I directories in the order given.
    fn new(io: &Io<'_>, parsed: &Parsed, files: &[String]) -> Run<Search> {
        let library = find_standard_library(io)?;
        let mut includes: Vec<String> = Vec::new();
        for (_, values) in parsed.options.iter().filter(|(name, _)| name == "-I") {
            let directory = &values[0];
            let directory = match (directory.strip_prefix('+'), &library) {
                (Some(_), None) => {
                    return decline(
                        "the backtrace tlapm prints as it ends with -I + without its standard library",
                    );
                }
                (Some(relative), Some(library)) => concat_paths(library, relative),
                (None, _) => directory.clone(),
            };
            if !includes.contains(&directory) && library.as_ref() != Some(&directory) {
                includes.push(directory);
            }
        }
        let mut directories = vec![".".to_owned()];
        directories.extend(includes.iter().cloned());
        directories.extend(library.iter().cloned());
        let mut loader = vec![".".to_owned()];
        loader.extend(library.iter().cloned());
        loader.extend(includes.iter().rev().cloned());
        for file in files.iter().rev() {
            let directory = get_ocaml_dirname(file);
            if !loader.contains(&directory) {
                loader.insert(0, directory);
            }
        }
        Ok(Search {
            directories,
            loader,
        })
    }

    fn find(&self, io: &Io<'_>, name: &str) -> Run<Option<Found>> {
        let found = |path: String| Found {
            path,
            name: String::new(),
            is_loaded: false,
        };
        if !is_implicit(name) {
            if io.exists(name) {
                return Ok(Some(found(name.to_owned())));
            }
        } else if let Some(path) = self
            .directories
            .iter()
            .map(|directory| concat_paths(directory, name))
            .find(|path| io.exists(path))
        {
            return Ok(Some(found(path)));
        }
        // Loader.load_from_dirs reads the first file it can, and names the module by `name`.
        for directory in &self.loader {
            let path = concat_paths(directory, name);
            match io.get_kind(&path) {
                Some(PathKind::File) => {
                    return Ok(Some(Found {
                        path,
                        name: name.to_owned(),
                        is_loaded: true,
                    }));
                }
                Some(PathKind::Other) => {
                    return decline(format!("a module file tlapm finds but can't read: {path}"));
                }
                _ => {}
            }
        }
        Ok(None)
    }
}

/// OCaml's `Filename.is_implicit`.
fn is_implicit(path: &str) -> bool {
    !path.starts_with('/') && !path.starts_with("./") && !path.starts_with("../")
}

/// OCaml's `Filename.concat`.
fn concat_paths(directory: &str, name: &str) -> String {
    if directory.is_empty() || directory.ends_with('/') {
        format!("{directory}{name}")
    } else {
        format!("{directory}/{name}")
    }
}

/// OCaml's `Filename.dirname`.
fn get_ocaml_dirname(path: &str) -> String {
    let bytes = path.as_bytes();
    let Some(mut end) = bytes.len().checked_sub(1) else {
        return ".".to_owned();
    };
    while bytes[end] == b'/' {
        let Some(previous) = end.checked_sub(1) else {
            return "/".to_owned();
        };
        end = previous;
    }
    while bytes[end] != b'/' {
        let Some(previous) = end.checked_sub(1) else {
            return ".".to_owned();
        };
        end = previous;
    }
    while bytes[end] == b'/' {
        let Some(previous) = end.checked_sub(1) else {
            return "/".to_owned();
        };
        end = previous;
    }
    path[..=end].to_owned()
}

enum Generated {
    Modules(Vec<ModuleObligations>, Vec<String>),
    Declined(String),
}

// What the obligations print as they are generated, held until it is known that the run doesn't
// decline.
enum Printed {
    Out(String),
    Err(String),
}

fn generate_obligations(
    io: &Io<'_>,
    files: &[String],
    module_paths: &[String],
    search: &Search,
    lines: LineRange,
    is_toolbox: bool,
) -> Generated {
    let printed = std::cell::RefCell::new(Vec::new());
    let flush = |printed: Vec<Printed>| {
        for text in printed {
            match text {
                Printed::Out(text) => io.out(text),
                Printed::Err(text) => io.err(text),
            }
        }
    };
    // tlapm ends with the exception and the backtrace of where it was raised, which only a run of
    // tlapm knows.
    let fail = |exception: &str| {
        Generated::Declined(format!(
            "the backtrace tlapm prints as it ends with {exception}"
        ))
    };
    // Tlapm_args gathers the command line's modules last first, and Tlapm_lib.read_new_modules
    // reads them in that order into a map by name, so the first of two modules with one name wins.
    let mut mains = Vec::new();
    for (file, path) in files.iter().zip(module_paths).rev() {
        let found = match search.find(io, path) {
            Ok(Some(found)) => found,
            Ok(None) => {
                return fail(&format!(
                    "Failure(\"Module.Parser.parse_file\"), as it can't find {file}"
                ));
            }
            Err(Decline(reason)) => return Generated::Declined(reason),
        };
        match read_module(io, &found, path) {
            Ok(source) => mains.push(source),
            Err(Decline(reason)) => return Generated::Declined(reason),
        }
    }
    let mut module_names: Vec<String> = Vec::new();
    let mut declined: Option<String> = None;
    let generated = get_obligations(
        &mains,
        &mut |name| {
            if !module_names.iter().any(|known| known == name) {
                module_names.push(name.to_owned());
            }
            if declined.is_some() {
                return None;
            }
            let found = match search.find(io, &format!("{name}.tla")) {
                Ok(found) => found,
                Err(Decline(reason)) => {
                    declined = Some(reason);
                    return None;
                }
            };
            match found.map(|found| read_module(io, &found, &found.path)) {
                Some(Ok(source)) => Some(source),
                Some(Err(Decline(reason))) => {
                    declined = Some(reason);
                    None
                }
                None => (name == "TLAPS").then(|| ObligationSource {
                    file: "TLAPS.tla".to_owned(),
                    source: TLAPS_MODULE.to_owned(),
                }),
            }
        },
        Some(lines),
        &mut |warning| {
            let text = format!("{}\n", warning.text);
            let message = match warning.channel {
                Channel::Stdout => Some(Printed::Out(text)),
                Channel::Toolbox | Channel::ToolboxOnly if is_toolbox => {
                    Some(Printed::Err(format_toolbox_message(&[
                        "type:warning".to_owned(),
                        format!("msg:{}", warning.text),
                    ])))
                }
                Channel::ToolboxOnly => None,
                Channel::Toolbox | Channel::Stderr => Some(Printed::Err(text)),
            };
            printed.borrow_mut().extend(message);
        },
    );
    if let Some(reason) = declined {
        return Generated::Declined(reason);
    }
    let printed = printed.into_inner();
    match generated {
        Ok(modules) => {
            flush(printed);
            Generated::Modules(modules, module_names)
        }
        Err(ObligationError::Proof { exception, .. }) => fail(&exception),
        Err(error) => Generated::Declined(get_obligation_error(&error).0),
    }
}

/// A module's file as tlapm reads it. `Loader` hands tlapm's lexer the text, which it reads in
/// token mode from the start (`Alexer.lex_string`), where it reads a file it finds itself from its
/// module header on (`Alexer.modfile`).
fn read_module(io: &Io<'_>, found: &Found, shown: &str) -> Run<ObligationSource> {
    let path = PathBuf::from(&found.path);
    let bytes = match io.get_kind(&found.path) {
        Some(PathKind::File) => io.call(move |session| session.read(&path)),
        _ => None,
    };
    let Some(source) = bytes.and_then(|bytes| String::from_utf8(bytes).ok()) else {
        return decline(format!("a module file tlapm finds but can't read: {shown}"));
    };
    if found.is_loaded && !is_header_first(source.as_bytes()) {
        return decline(format!(
            "what comes before the module header of {}, which tlapm reads as tokens",
            found.path
        ));
    }
    Ok(ObligationSource {
        file: if found.is_loaded {
            found.name.clone()
        } else {
            found.path.clone()
        },
        source,
    })
}

/// Whether tlapm's lexer, in token mode from the start, reads only blanks and comments before the
/// module header that `Alexer.modfile` finds.
fn is_header_first(bytes: &[u8]) -> bool {
    let is_header_at = |start: usize| {
        let rest = &bytes[start..];
        let dashes = rest.iter().take_while(|byte| **byte == b'-').count();
        let spaces = rest[dashes..]
            .iter()
            .take_while(|byte| **byte == b' ')
            .count();
        dashes >= 4 && rest[dashes + spaces..].starts_with(b"MODULE")
    };
    let mut index = 0;
    while index < bytes.len() {
        match &bytes[index..] {
            [b' ' | b'\n' | b'\r', ..] => index += 1,
            [b'\\', b'*', ..] => {
                index += bytes[index..]
                    .iter()
                    .position(|byte| matches!(byte, b'\n' | b'\r'))
                    .unwrap_or(bytes.len() - index);
            }
            [b'(', b'*', b'{', ..] => break,
            [b'(', b'*', ..] => {
                let mut depth = 0;
                while index < bytes.len() {
                    match &bytes[index..] {
                        [b'(', b'*', ..] => {
                            depth += 1;
                            index += 2;
                        }
                        [b'*', b')', ..] => {
                            depth -= 1;
                            index += 2;
                            if depth == 0 {
                                break;
                            }
                        }
                        _ => index += 1,
                    }
                }
            }
            _ => break,
        }
    }
    index < bytes.len() && is_header_at(index) && !(0..index).any(is_header_at)
}

#[allow(clippy::too_many_arguments)]
fn check_modules(
    io: &Io<'_>,
    parsed: &Parsed,
    modules: &[ModuleObligations],
    module_names: &[String],
    lines: LineRange,
    is_toolbox: bool,
    is_processing: bool,
    threads: usize,
) -> Run<i32> {
    let cache_directory = match parsed.get("--cache-dir") {
        Some(values) => values[0].clone(),
        None => io
            .call(|session| session.host().get_variable("TLAPM_CACHE_DIR"))
            .unwrap_or_else(|| ".tlacache".to_owned()),
    };
    let forgotten = parsed.get_integers("--nofpl").unwrap_or(vec![0, 0]);
    let is_nofp = parsed.has("--nofp");
    let version = get_stored_version();
    let mut table = FingerprintTable::new();
    let mut statuses = Vec::new();
    // Tlapm_lib.mkdir_tlaps would make each module's directory at the root.
    if cache_directory.is_empty() {
        return decline("an empty cache directory, which has tlapm write its cache at /");
    }
    if is_processing && !read_cache(io, parsed, modules, module_names, &cache_directory) {
        return Ok(0);
    }
    for (index, module) in modules.iter().enumerate() {
        // Tlapm_lib.mkdir_tlaps.
        let directory = format!("{cache_directory}/{}.tlaps", module.name);
        let fingerprints_path = format!("{directory}/fingerprints");
        let loaded_path = parsed
            .get("--usefp")
            .map_or(fingerprints_path.clone(), |values| values[0].clone());
        make_cache_directory(io, &cache_directory, &directory)?;
        // Sys.remove removes anything but a directory, and tlapm can't write a directory's
        // fingerprints once it has proved.
        if parsed.has("--cleanfp") {
            match io.get_kind(&fingerprints_path) {
                None => {}
                Some(PathKind::Directory) => return Err(get_abnormal_ending(&fingerprints_path)),
                Some(_) => {
                    remove(io, &fingerprints_path);
                    io.out(format!(
                        "(* fingerprints file {} removed *)\n",
                        quote_ocaml(&fingerprints_path)
                    ));
                }
            }
        }
        if !parsed.has("--cleanfp") && io.exists(&loaded_path) && module.summary.total != 0 {
            io.out(if is_nofp {
                format!(
                    "(* will not use fingerprints (because of option `--nofp`), but will now load fingerprints from the file `{loaded_path}`, in order to overwrite with the new fingerprints, and then save the results at the end. *)\n"
                )
            } else {
                format!("(* loading fingerprints in {} *)\n", quote_ocaml(&loaded_path))
            });
            let bytes = {
                let path = PathBuf::from(&loaded_path);
                io.call(move |session| session.read(&path))
            };
            let Some(bytes) = bytes else {
                return decline(format!(
                    "a fingerprints file tlapm can't read: {loaded_path}"
                ));
            };
            if load_fingerprints(&mut table, &bytes, parsed.has("--safefp"), &version).is_err() {
                return decline(format!(
                    "a fingerprints file tlapm moves aside: {loaded_path}"
                ));
            }
        }
        if parsed.has("--summary") {
            io.out(format!("{}\n", format_summary(module)));
        }
        if is_toolbox {
            let mut messages = String::new();
            for obligation in &module.obligations {
                let fields = if parsed.has("--printallobs") {
                    vec![format!("obl:{}", obligation.text)]
                } else {
                    Vec::new()
                };
                messages.push_str(&format_obligation_message(
                    obligation,
                    "to be proved",
                    fields,
                ));
            }
            messages.push_str(&format_toolbox_message(&[
                "type:obligationsnumber".to_owned(),
                format!("count:{}", module.obligations.len()),
            ]));
            io.err(messages);
        }
        if parsed.has("--strict") {
            let is_targeted = lines.start > 0.0 || lines.end < f64::INFINITY;
            statuses.extend(check_strictly(
                io,
                module,
                is_targeted,
                parsed.has("--summary"),
            ));
        }
        if !is_processing {
            continue;
        }
        // tlapm's history holds the source of each module read so far.
        let sources = get_history_sources(module_names, &modules[..=index]);
        let now = io.call(|session| get_local_time(session.host()));
        save_history(io, &fingerprints_path, &sources, now)?;
        let forgotten = (forgotten[0], forgotten[1]);
        let settings = Settings {
            known: KnownResults::new(&table),
            // Prep.already_processed: `nofp_sl - 1 < start && stop < nofp_el + 1`, which wraps.
            is_fingerprinted: Box::new(move |obligation: &PrintedObligation| {
                !is_nofp
                    && !obligation.locus.as_ref().is_some_and(|locus| {
                        add_ocaml(forgotten.0, -1) < i64::from(locus.start_line)
                            && i64::from(locus.end_line) < add_ocaml(forgotten.1, 1)
                    })
            }),
            is_proving: !parsed.has("--noproving"),
        };
        let paths = ModulePaths {
            theory: format!("{directory}/{}.thy", module.name),
            fingerprints: fingerprints_path,
        };
        let is_failed = prove_module(
            io, module, &paths, settings, &mut table, &version, is_toolbox, threads,
        )?;
        if is_failed && parsed.has("--strict") {
            statuses.push(STRICT_FAILED);
        }
        if is_failed && !parsed.has("--strict") && !is_toolbox {
            io.err(format!("{UNPROVED_ENDING}\n"));
            return Ok(FAILURE_STATUS);
        }
    }
    Ok([STRICT_FAILED, STRICT_INCOMPLETE, STRICT_EMPTY_TARGET]
        .into_iter()
        .find(|status| statuses.contains(status))
        .unwrap_or(0))
}

// tlapm's history holds the source of each module read so far.
fn get_history_sources(module_names: &[String], modules: &[ModuleObligations]) -> Vec<String> {
    module_names
        .iter()
        .chain(modules.iter().map(|module| &module.name))
        .map(|name| format!("{name}.tla"))
        .collect()
}

/// Reads what the run reads of each module's cache before it proves any, and whether the host held
/// all of it: a host that answers what it lacks once the run returns has it stop before it proves.
fn read_cache(
    io: &Io<'_>,
    parsed: &Parsed,
    modules: &[ModuleObligations],
    module_names: &[String],
    cache_directory: &str,
) -> bool {
    for (index, module) in modules.iter().enumerate() {
        let fingerprints = format!("{cache_directory}/{}.tlaps/fingerprints", module.name);
        let loaded = parsed
            .get("--usefp")
            .map_or(fingerprints.clone(), |values| values[0].clone());
        let history = PathBuf::from(format!("{fingerprints}.history"));
        let mut paths = vec![fingerprints, loaded.clone()];
        paths.extend(get_history_sources(module_names, &modules[..=index]));
        io.call(move |session| {
            let host = session.host();
            for path in &paths {
                host.get_path_kind(Path::new(path));
            }
            if host.get_path_kind(Path::new(&loaded)).is_some() {
                host.read_bytes(Path::new(&loaded));
            }
            if host.get_path_kind(&history).is_some() {
                host.list_directory(&history);
            }
        });
    }
    io.call(|session| session.host().is_complete())
}

fn check_strictly(
    io: &Io<'_>,
    module: &ModuleObligations,
    is_targeted: bool,
    is_summary: bool,
) -> Vec<i32> {
    let summary = &module.summary;
    let mut text = String::new();
    if !is_summary {
        for locus in &summary.absent {
            text.push_str(&format!("Missing proof at {}\n", get_locus_text(locus)));
        }
        for locus in &summary.omitted {
            text.push_str(&format!("Omitted proof at {}\n", get_locus_text(locus)));
        }
    }
    let is_incomplete = summary.absent.len() + summary.omitted.len() > 0;
    if is_incomplete {
        text.push_str(&format!(
            "{}[ERROR]: Proof incomplete in module {}: {} missing, {} omitted proof step(s).\n",
            get_at_prefix(module.location.as_ref()),
            quote_ocaml(&module.name),
            summary.absent.len(),
            summary.omitted.len()
        ));
    }
    let is_empty = is_targeted && module.obligations.is_empty();
    if is_empty {
        text.push_str(&format!(
            "{}[ERROR]: No proof obligation found for the selected target.\n",
            get_at_prefix(module.location.as_ref())
        ));
    }
    io.err(text);
    let mut statuses = Vec::new();
    if is_incomplete {
        statuses.push(STRICT_INCOMPLETE);
    }
    if is_empty {
        statuses.push(STRICT_EMPTY_TARGET);
    }
    statuses
}

/// Where tlapm can't make or write its cache, an exception ends it, and it prints the backtrace of
/// where it raised it, which only a run of tlapm knows.
fn get_abnormal_ending(path: &str) -> Decline {
    Decline(format!(
        "the backtrace tlapm prints as it ends where it can't write {path}"
    ))
}

/// Tlapm_lib.mkdir_tlaps: `Unix.mkdir` of the cache directory, where it isn't there, and of the
/// module's in it. Where it can't make the first, it prints why and goes on to fail on the second.
fn make_cache_directory(io: &Io<'_>, cache: &str, directory: &str) -> Run<()> {
    for path in [cache, directory] {
        if io.exists(path) {
            continue;
        }
        let target = PathBuf::from(path);
        if !io.call(move |session| {
            session
                .overlay
                .create_directory(&target, false, session.output.host)
        }) {
            return Err(get_abnormal_ending(directory));
        }
    }
    Ok(())
}

fn remove(io: &Io<'_>, path: &str) {
    let target = PathBuf::from(path);
    io.call(move |session| session.overlay.remove(&target, session.output.host));
}

fn write_file(io: &Io<'_>, path: &str, bytes: Vec<u8>) -> Run<()> {
    let target = PathBuf::from(path);
    if io.call(move |session| session.overlay.write(&target, bytes, session.output.host)) {
        Ok(())
    } else {
        Err(get_abnormal_ending(path))
    }
}

fn pad(value: i64) -> String {
    format!("{value:02}")
}

/// Fpfile.fp_init: copies the fingerprints file and the sources into a new directory of the
/// history, named by the local time, and keeps the latest ten, by shell commands whose failures
/// tlapm ignores. It then writes the fingerprints file, which it can't where a directory is there.
fn save_history(io: &Io<'_>, path: &str, sources: &[String], now: LocalTime) -> Run<()> {
    if io.get_kind(path) == Some(PathKind::Directory) {
        return Err(get_abnormal_ending(path));
    }
    let history = format!("{path}.history");
    let directory = format!(
        "{history}/{}-{}-{}_{}_{}_{}",
        now.year,
        pad(now.month + 1),
        pad(now.day),
        pad(now.hours),
        pad(now.minutes),
        pad(now.seconds),
    );
    let sources = sources.to_vec();
    let (path, history) = (path.to_owned(), PathBuf::from(history));
    io.call(move |session| {
        let host = session.output.host;
        let overlay = &session.overlay;
        let directory = PathBuf::from(directory);
        // mkdir -p, then cp -p of each file there is.
        if !overlay.create_directory(&directory, true, host) {
            return;
        }
        for file in std::iter::once(path.as_str()).chain(sources.iter().map(String::as_str)) {
            let file = Path::new(file);
            if let Some(name) = file.file_name() {
                overlay.copy(file, &directory.join(name), host);
            }
        }
        // rm -rf `ls -1td <history>/* | tail -n +11`: the glob leaves out dotfiles, and ls lists the
        // latest first.
        let now = get_milliseconds(host);
        let Some(mut entries) = overlay.list(&history, now, host) else {
            return;
        };
        entries.retain(|entry| !entry.name.starts_with('.'));
        entries.sort_by(|left: &Entry, right: &Entry| {
            right
                .modified
                .total_cmp(&left.modified)
                .then_with(|| left.name.cmp(&right.name))
        });
        for old in entries.into_iter().skip(HISTORY_SIZE) {
            overlay.remove(&history.join(old.name), host);
        }
    });
    Ok(())
}

fn get_milliseconds(host: &dyn Host) -> f64 {
    host.now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0.0, |since| since.as_secs_f64() * 1000.0)
}

struct ModulePaths {
    theory: String,
    fingerprints: String,
}

/// A decision the driver asked for, as a thread of the pool makes it.
struct Job {
    key: String,
    prover: String,
    text: String,
    time_limit_ms: f64,
}

/// A decision made: the answer, and what tlapm copies to stdout of what the backend wrote to
/// stderr; or why Prove It can't say what tlapm prints for it.
type Decided = (String, Result<(Answer, Option<&'static str>), String>);

fn decide(job: Job, cancel: &Cancel) -> Decided {
    let started = Instant::now();
    let limits = Limits::new(job.time_limit_ms, None, Some(cancel.clone()));
    let decision = prove_it_prover::decide(&job.prover, &job.text, &limits);
    let time_used_ms = started.elapsed().as_secs_f64() * 1000.0;
    let decided = match decision {
        Ok(decision) => {
            let stop = decision
                .statistics
                .iter()
                .find(|(name, _)| *name == "stop")
                .and_then(|(_, statistic)| match statistic {
                    Statistic::Text(text) => Some(text.as_str()),
                    Statistic::Count(_) => None,
                });
            let is_timeout = time_used_ms >= job.time_limit_ms;
            // tlapm runs Zenon with its stderr on tlapm's stdout, and kills it at the time limit.
            let note = match (job.prover.as_str(), decision.verdict, stop) {
                (_, Verdict::Unsat, _) => Ok(None),
                ("zenon", _, Some("exhausted")) => Ok(Some(
                    "Zenon error: exhausted search space without finding a proof\n",
                )),
                ("zenon", _, Some("memory limit")) => Ok(Some(
                    "Zenon error: could not find a proof within the memory size limit\n",
                )),
                ("zenon", _, Some("time limit")) => Ok(None),
                ("zenon", _, stop) => Err(format!(
                    "what Zenon writes where it stops at {}",
                    stop.unwrap_or("no reason")
                )),
                ("isabelle", _, _) if !is_timeout => {
                    Err("what Isabelle writes for an obligation it doesn't prove".to_owned())
                }
                _ => Ok(None),
            };
            note.map(|note| {
                (
                    Answer::Decided {
                        verdict: decision.verdict,
                        time_used_ms,
                    },
                    note,
                )
            })
        }
        Err(DecideError::Prover(message)) => Err(format!(
            "what tlapm prints where {} fails: {message}",
            job.prover
        )),
        Err(DecideError::Declined(reason)) => Err(format!("{} declined: {reason}", job.prover)),
    };
    (job.key, decided)
}

/// Where the driver's decisions are made: `submit` hands one over, `receive` waits for one made,
/// and `poll` takes one made without waiting.
struct Pool<'p> {
    capacity: usize,
    submit: Box<dyn FnMut(Job) + 'p>,
    receive: Box<dyn FnMut() -> Decided + 'p>,
    poll: Box<dyn FnMut() -> Option<Decided> + 'p>,
}

#[cfg(not(target_arch = "wasm32"))]
fn with_pool<T>(threads: usize, work: impl FnOnce(&mut Pool<'_>) -> Run<T>) -> Run<T> {
    use std::sync::Mutex;
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::mpsc::Sender;
    const DECIDE_STACK_BYTES: usize = 256 * 1024 * 1024;
    let is_canceled = Arc::new(AtomicBool::new(false));
    let cancel: Cancel = {
        let is_canceled = is_canceled.clone();
        Arc::new(move || is_canceled.load(Ordering::Relaxed))
    };
    std::thread::scope(|scope| {
        let (jobs, received) = channel::<Job>();
        let received = Arc::new(Mutex::new(received));
        let (decided, answers) = channel::<Decided>();
        for _ in 0..threads {
            let received = received.clone();
            let decided: Sender<Decided> = decided.clone();
            let cancel = cancel.clone();
            let spawned = std::thread::Builder::new()
                .name("prove-it decide".into())
                .stack_size(DECIDE_STACK_BYTES)
                .spawn_scoped(scope, move || {
                    loop {
                        let job = received.lock().expect("the jobs").recv();
                        let Ok(job) = job else { break };
                        if decided.send(decide(job, &cancel)).is_err() {
                            break;
                        }
                    }
                });
            if spawned.is_err() {
                return decline(format!(
                    "{threads} threads for the decisions, which the system refuses"
                ));
            }
        }
        drop(decided);
        let answers = std::cell::RefCell::new(answers);
        let mut pool = Pool {
            capacity: threads,
            submit: Box::new(|job| jobs.send(job).expect("the decide threads")),
            receive: Box::new(|| answers.borrow().recv().expect("a decide thread")),
            poll: Box::new(|| answers.borrow().try_recv().ok()),
        };
        let result = work(&mut pool);
        drop(pool);
        is_canceled.store(true, Ordering::Relaxed);
        drop(jobs);
        result
    })
}

#[cfg(target_arch = "wasm32")]
fn with_pool<T>(_threads: usize, work: impl FnOnce(&mut Pool<'_>) -> Run<T>) -> Run<T> {
    let cancel: Cancel = Arc::new(|| false);
    let waiting = std::cell::RefCell::new(std::collections::VecDeque::new());
    let mut pool = Pool {
        capacity: 1,
        submit: Box::new(|job| waiting.borrow_mut().push_back(job)),
        receive: Box::new(|| {
            let job = waiting
                .borrow_mut()
                .pop_front()
                .expect("a decision submitted");
            decide(job, &cancel)
        }),
        poll: Box::new(|| None),
    };
    work(&mut pool)
}

// Tlapm_lib.process_obs. Returns whether some obligation failed.
#[allow(clippy::too_many_arguments)]
fn prove_module(
    io: &Io<'_>,
    module: &ModuleObligations,
    paths: &ModulePaths,
    settings: Settings,
    table: &mut FingerprintTable,
    version: &str,
    is_toolbox: bool,
    threads: usize,
) -> Run<bool> {
    let is_proving = settings.is_proving;
    let round = with_pool(threads, |pool| {
        prove_in_rounds(io, module, &settings, pool, is_toolbox, is_proving)
    })?;
    let attempts: Vec<Vec<ProofAttempt>> = round
        .reports
        .iter()
        .map(|report| {
            report
                .attempts
                .iter()
                .map(|attempt| attempt.attempt.clone())
                .collect()
        })
        .collect();
    let theory = encode_proof_theory(&module.name, &attempts, &module.obligations)
        .map_err(|error| get_obligation_error(&error))?;
    write_file(io, &paths.theory, theory.into_bytes())?;
    io.out(format!(
        "(* created new {} *)\n",
        quote_ocaml(&paths.theory)
    ));
    let now = io.call(|session| get_local_time(session.host()));
    let bytes = round
        .results
        .save(table, version, now)
        .map_err(|error| get_obligation_error(&error))?;
    let temporary = format!("{}.tmp", paths.fingerprints);
    write_file(io, &temporary, bytes)?;
    let (from, to) = (
        PathBuf::from(&temporary),
        PathBuf::from(&paths.fingerprints),
    );
    if !io.call(move |session| session.overlay.rename(&from, &to, session.output.host)) {
        return Err(get_abnormal_ending(&paths.fingerprints));
    }
    io.out(format!(
        "(* fingerprints written in {} *)\n",
        quote_ocaml(&paths.fingerprints)
    ));
    if !is_proving {
        return Ok(false);
    }
    let unproved: Vec<(&Report, &PrintedObligation)> = round
        .reports
        .iter()
        .zip(&module.obligations)
        .filter(|(report, _)| {
            matches!(
                report.status,
                Status::Failed { .. } | Status::Unsupported { .. }
            )
        })
        .collect();
    let mut text = String::new();
    if is_toolbox {
        for (report, obligation) in &unproved {
            if report.attempts.is_empty() && !matches!(obligation.kind, ObligationKind::Error(_)) {
                text.push_str(&format_failed_obligation(obligation, "unexpected error"));
            }
        }
    }
    for (_, obligation) in unproved.iter().rev() {
        let sequent =
            print_sequent(&obligation.sequent).map_err(|error| get_obligation_error(&error))?;
        let error = render_doc(
            &format(
                "[ERROR]: @[<v2>Could not prove or check:@,%a@]",
                vec![sequent.into()],
            ),
            35,
        )
        .map_err(|error| get_obligation_error(&error))?;
        text.push_str(&format!(
            "{}{error}\n",
            get_at_prefix(obligation.locus.as_ref())
        ));
    }
    let count = module.obligations.len();
    let total = format!("{count} obligation{}", if count > 1 { "s" } else { "" });
    let prefix = get_at_prefix(module.location.as_ref());
    text.push_str(&if unproved.is_empty() {
        format!("{prefix}[INFO]: All {total} proved.\n")
    } else {
        format!(
            "{prefix}[ERROR]: {}/{total} failed.\nThere were backend errors processing module `{}`.\n",
            unproved.len(),
            quote_ocaml(&module.name)
        )
    });
    io.err(text);
    Ok(!unproved.is_empty())
}

// The driver's rounds, each with every decision made so far: each round's new reports are
// printed, and its requests go to the pool, the earliest obligation's first, as many as it has
// threads; the next round starts once a decision is made, with every other made by then.
fn prove_in_rounds(
    io: &Io<'_>,
    module: &ModuleObligations,
    settings: &Settings,
    pool: &mut Pool<'_>,
    is_toolbox: bool,
    is_proving: bool,
) -> Run<Round> {
    let mut answers: HashMap<String, Answer> = HashMap::new();
    let mut in_flight: HashSet<String> = HashSet::new();
    let mut cache = Cache::default();
    let mut reported = 0;
    loop {
        let round = prove_obligations_with(
            &module.obligations,
            &|key| answers.get(key).cloned(),
            &mut cache,
            settings,
        )
        .map_err(|error| get_obligation_error(&error))?;
        for report in &round.reports[reported..] {
            let obligation = &module.obligations[reported];
            check_report(report, is_proving)?;
            if is_toolbox {
                io.err(format_report(report, obligation)?);
            }
            reported += 1;
        }
        if let Some(error) = &round.error {
            return Err(get_obligation_error(error));
        }
        if round.requests.is_empty() {
            return Ok(round);
        }
        let mut waiting: Vec<_> = round
            .requests
            .into_iter()
            .filter(|request| !in_flight.contains(&request.key))
            .collect();
        waiting.sort_by_key(|request| request.priority);
        for request in waiting
            .into_iter()
            .take(pool.capacity.saturating_sub(in_flight.len()))
        {
            in_flight.insert(request.key.clone());
            (pool.submit)(Job {
                key: request.key,
                prover: request.prover,
                text: request.text,
                time_limit_ms: request.time_limit_ms,
            });
        }
        let mut decided = vec![(pool.receive)()];
        while let Some(more) = (pool.poll)() {
            decided.push(more);
        }
        for (key, answer) in decided {
            in_flight.remove(&key);
            let (answer, note) = answer.map_err(Decline)?;
            if let Some(note) = note {
                io.out(note.to_owned());
            }
            answers.insert(key, answer);
        }
    }
}

// A report Prove It can't print as tlapm would: a method it couldn't try, which tlapm tries.
fn check_report(report: &Report, is_proving: bool) -> Run<()> {
    if let Status::Unsupported { reason } = &report.status
        && (is_proving || !reason.is_empty())
    {
        return decline(format!(
            "an obligation Prove It can't prove as tlapm does: {reason}"
        ));
    }
    if let Some(reason) = report
        .attempts
        .iter()
        .filter(|attempt| attempt.is_skipped())
        .find_map(|attempt| attempt.reason.as_deref())
    {
        return decline(format!(
            "a method Prove It can't try as tlapm does: {reason}"
        ));
    }
    Ok(())
}

// What the toolbox reports of an obligation once it is settled.
fn format_report(report: &Report, obligation: &PrintedObligation) -> Run<String> {
    if report.status == Status::Trivial {
        return Ok(format_obligation_message(
            obligation,
            "trivial",
            vec!["prover:tlapm".to_owned(), "already:false".to_owned()],
        ));
    }
    if matches!(obligation.kind, ObligationKind::Error(_)) {
        return Ok(format_failed_obligation(obligation, "user error"));
    }
    let mut text = String::new();
    for attempt in &report.attempts {
        text.push_str(&format_attempt(obligation, attempt)?);
    }
    Ok(text)
}

// A failed obligation as tlapm prints it: Prep.normalize_expand for a new failure, and
// Toolbox.normalize, which keeps pragmas, for a reused one.
fn format_normalized(obligation: &PrintedObligation, is_reused: bool) -> Run<String> {
    let normalize = || {
        if is_reused {
            normalize_sequent(&expand_defs(&obligation.sequent, false)?)
        } else {
            normalize_expand(&obligation.sequent, obligation.method.as_ref(), None)
        }
    };
    let sequent = normalize().map_err(|error| get_obligation_error(&error))?;
    let text = format_obligation(&sequent).map_err(|error| get_obligation_error(&error))?;
    Ok(format!("{text}\n"))
}

// Toolbox.print_res_aux.
fn format_attempt(obligation: &PrintedObligation, attempt: &Attempt) -> Run<String> {
    let method = &attempt.attempt.method;
    let timeout = method.time_limit_ms / 1000.0;
    let times = if timeout == 0.0 {
        String::new()
    } else {
        match attempt.time_used_ms {
            None => format!("time-limit: {}", format_general(timeout)),
            Some(used) => {
                let used = used / 1000.0;
                format!(
                    "time-limit: {}; time-used: {used:.1} ({:.0}%)",
                    format_general(timeout),
                    100.0 * used / timeout
                )
            }
        }
    };
    let meth = [method.tactic.clone().unwrap_or_default(), times]
        .into_iter()
        .filter(|part| !part.is_empty())
        .collect::<Vec<_>>()
        .join("; ");
    let is_smt = matches!(method.prover.as_str(), "smt" | "z3");
    let note = match (is_smt, attempt.reason.as_deref(), attempt.verdict) {
        (true, Some("false"), Some(verdict)) => {
            format!("(* SMT failed with status = {}\n *)\n", verdict.name())
        }
        _ => String::new(),
    };
    let is_proved = attempt.attempt.is_proved;
    let is_reused = attempt.attempt.is_reused;
    let mut fields = vec![format!("prover:{}", method.prover)];
    if !meth.is_empty() {
        fields.push(format!("meth:{meth}"));
    }
    if let Some(reason) = &attempt.reason {
        fields.push(format!("reason:{reason}"));
    }
    fields.push(format!("already:{is_reused}"));
    if !is_proved {
        let lead = if is_reused {
            String::new()
        } else {
            format!("\n{note}")
        };
        fields.push(format!(
            "obl:{lead}{}",
            format_normalized(obligation, is_reused)?
        ));
    }
    Ok(format_obligation_message(
        obligation,
        if is_proved { "proved" } else { "failed" },
        fields,
    ))
}

// Method.Fail, for an error obligation or one no method was tried on.
fn format_failed_obligation(obligation: &PrintedObligation, reason: &str) -> String {
    format_obligation_message(
        obligation,
        "failed",
        vec![
            "prover:fail".to_owned(),
            "meth:time-limit: inf".to_owned(),
            format!("reason:{reason}"),
            "already:false".to_owned(),
            format!("obl:{}", obligation.text),
        ],
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn formats_a_number_as_c_does_with_g() {
        let cases = [
            (5.0, "5"),
            (10.0, "10"),
            (0.5, "0.5"),
            (1.234_567_8, "1.23457"),
            (123_456.0, "123456"),
            (1_234_567.0, "1.23457e+06"),
            (0.0001, "0.0001"),
            (0.000_012_3, "1.23e-05"),
            (f64::INFINITY, "inf"),
            (100.0, "100"),
            (999_999.5, "1e+06"),
        ];
        for (value, expected) in cases {
            assert_eq!(format_general(value), expected, "{value}");
        }
    }

    #[test]
    fn finds_a_directory_as_node_does() {
        let cases = [
            ("Proofs.tla", "."),
            ("sub/Proofs.tla", "sub"),
            ("/Proofs.tla", "/"),
            ("a//b", "a/"),
            ("/a/b/", "/a"),
            ("", "."),
        ];
        for (path, expected) in cases {
            assert_eq!(get_dirname(path), expected, "{path}");
        }
        assert_eq!(join_paths("/usr/bin/", "tlapm"), "/usr/bin/tlapm");
        assert_eq!(join_paths("", "tlapm"), "tlapm");
        assert_eq!(join_paths(".", "tlapm"), "tlapm");
        assert_eq!(join_paths("a/../..", "tlapm"), "../tlapm");
        assert_eq!(join_paths("/", "lib/tlapm/stdlib"), "/lib/tlapm/stdlib");
    }

    #[test]
    fn reads_an_integer_as_ocamls_int_of_string_does() {
        let cases = [
            ("42", Some(42)),
            ("-7", Some(-7)),
            ("+7", Some(7)),
            ("1_000", Some(1000)),
            ("0x1F", Some(31)),
            ("0o17", Some(15)),
            ("0b101", Some(5)),
            ("0u12", Some(12)),
            ("-0x1", Some(-1)),
            ("4611686018427387903", Some(OCAML_MAX_INT)),
            ("-4611686018427387904", Some(-OCAML_MAX_INT - 1)),
            ("4611686018427387904", None),
            ("0x4000000000000000", Some(-OCAML_MAX_INT - 1)),
            ("0x7FFFFFFFFFFFFFFF", Some(-1)),
            ("0x8000000000000000", None),
            ("_1", None),
            ("1x", None),
            ("", None),
            ("-", None),
            ("0x", None),
            (" 1", None),
            ("1.0", None),
        ];
        for (text, expected) in cases {
            assert_eq!(parse_int(text), expected, "{text}");
        }
        assert_eq!(add_ocaml(OCAML_MAX_INT, 1), -OCAML_MAX_INT - 1);
        assert_eq!(add_ocaml(-OCAML_MAX_INT - 1, -1), OCAML_MAX_INT);
    }

    #[test]
    fn quotes_as_ocaml_and_the_shell_do() {
        assert_eq!(
            quote_ocaml("a\"b\\c\n\u{e9}"),
            "\"a\\\"b\\\\c\\n\\195\\169\""
        );
        assert_eq!(quote_shell_argument("Spec.tla"), "Spec.tla");
        assert_eq!(quote_shell_argument(""), "''");
        assert_eq!(quote_shell_argument("it's"), "'it'\\''s'");
    }
}
