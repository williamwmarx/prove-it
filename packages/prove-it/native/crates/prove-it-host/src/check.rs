//! The native binary's check, in-process, for the library and the CLI of `dist/`:
//! `checkSources(args, known, machine)` checks the spec the TLC command line `args` names as the
//! binary does, reading its files from what JavaScript knows (`sources`), and returns one of:
//!
//! - `{ kind: "checked", exitCode, out, err, thrown, outcome, writes, files }`, what the binary
//!   prints to stdout and stderr, its exit code, what the check found where it searched, as the
//!   library reports it (`get_outcome`), or else, where it stopped before it searched, the error the
//!   library throws (`get_thrown`), each file the library's check wrote, in order, as
//!   `{ path, bytes, isAppended }`, and the operations on the files tlapm's command line held back
//!   until its run ended, in the order JavaScript applies them (`files.rs`);
//! - `{ kind: "needed", keys }`, what the check reads that isn't known yet (`sources`). It asks for
//!   everything before it searches or proves, so a round never does either; tlapm's command line
//!   learns whether the history's new directory, named by the time, is there from the history's
//!   entries, and asks for it alone where a run of the same second left one;
//! - `{ kind: "declined", reason }`, where the binary prints `not native yet`, without what it
//!   printed before, or where the library's check can't throw the error TLC reports as TLC does.
//!
//! The CLI answers for the machine's files, which the check finds as the binary does: `stat:<path>`,
//! `"file"`, `"directory"` or `"other"` where the system finds something at the path,
//! `bytes:<path>`, the bytes of a file there as a Uint8Array, `realpath:<path>`, its path with its
//! links followed, `cwd`, the working directory, and `tmpdir`, the system's temporary directory.
//! tlapm's command line also reads `entries:<path>`, a directory's entries, each as its `mtimeMs`
//! and its name, each ended by a NUL. The library has no files: it answers `text:<path>` for the
//! spec and its configuration, `module:<name>`, `class:<name>`, and `read:<path>` for a file the
//! spec reads, as the Json module's operators do, through `readFile`.
//!
//! `resolveFiles(args, given, request, known)` answers, through the same keys, what the CLI's
//! TypeScript check asks of where TLC finds the files of the spec `given` on the command line
//! `args` (`resolve_files`). `machine` gives what TLC's banner and dates describe, and what the
//! check may use of it:
//! `[system, release, arch, cores, memoryMegabytes, pid, now, zone, variables, isLibrary]`, with
//! `now` in milliseconds since the epoch, `zone` a POSIX TZ rule, `variables` the environment's
//! `[name, value]` pairs the check reads, and `isLibrary` whether the library's check runs it: the
//! library answers for files itself, so the Json module's operators don't touch the machine's, and
//! it reads each printed state's plain data, which the CLI doesn't, so only it has the check write
//! them.

use std::cell::RefCell;
use std::path::{Path, PathBuf};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use prove_it_check::host_path::Platform;
use prove_it_check::resolve::{self, Config, Resolved};
use prove_it_check::zone::{Zone, parse_rule};
use prove_it_check::{
    Entry, FileDescriber, FileDescription, FileKind, FileOperation, Files, Host, Machine, Outcome,
    Output, Thrown, is_directory_there,
};
use tla_engine::clock::Instant;
use tla_front::errors::SanyError;

use crate::files::{get_journal, parse_entries};
use crate::hooks::HookResult;
use crate::sources::{Sources, get_strings, get_text};
use crate::value::HostValue;

/// How the binary starts the line on stderr that declines a model.
const NOT_NATIVE: &str = "prove-it: not native yet: ";

/// What the host JavaScript runs on gives the check.
struct SourcesHost {
    sources: Sources,
    machine: Machine,
    /// The wall clock when the check started, which goes on from then by the monotonic clock.
    now: SystemTime,
    started: Instant,
    zone: Zone,
    variables: Vec<(String, String)>,
    is_library: bool,
    /// What the library's check wrote, in order, as `(path, bytes, is_appended)`, which
    /// JavaScript writes (`writes` in the result).
    writes: RefCell<Vec<(String, Vec<u8>, bool)>>,
    /// The operations on the files the check asks for, which only tlapm's command line does.
    files: RefCell<Vec<FileOperation>>,
}

impl SourcesHost {
    /// Whether the CLI can write the file (`writable:<path>`): a file there it can write, or none
    /// in a directory it can write into.
    fn is_writable(&self, path: &Path) -> bool {
        self.get(format!("writable:{}", path.display())).is_some()
    }

    fn get(&self, key: String) -> Option<String> {
        self.sources.get(key)
    }
}

impl Host for SourcesHost {
    // The library names its files by the spec's name alone. The CLI answers for paths: what is
    // there, its bytes and its real path, which the check reads next of a file it finds, so they
    // come in the same round.
    // The engine as WebAssembly runs on whatever host JavaScript does, which names its platform.
    fn platform(&self) -> Platform {
        if self.is_library || !cfg!(target_arch = "wasm32") {
            return Platform::NATIVE;
        }
        self.get("platform".to_string())
            .map_or(Platform::NATIVE, |name| Platform::from_node(&name))
    }

    fn kind(&self, path: &Path) -> FileKind {
        let path = path.display();
        if self.is_library {
            return match self.get(format!("text:{path}")) {
                Some(_) => FileKind::File,
                None => FileKind::Absent,
            };
        }
        let _ = self.platform();
        let _ = self.sources.get_bytes(format!("bytes:{path}"));
        let _ = self.get(format!("realpath:{path}"));
        match self.get(format!("stat:{path}")).as_deref() {
            Some("directory") => FileKind::Directory,
            Some("other") => FileKind::Other,
            Some(_) => FileKind::File,
            None => FileKind::Absent,
        }
    }

    fn real_path(&self, path: &Path) -> Option<PathBuf> {
        if self.is_library {
            return Some(path.to_path_buf());
        }
        self.get(format!("realpath:{}", path.display()))
            .map(PathBuf::from)
    }

    fn current_dir(&self) -> PathBuf {
        if self.is_library {
            return PathBuf::new();
        }
        self.get("cwd".into())
            .map(PathBuf::from)
            .unwrap_or_default()
    }

    fn temp_dir(&self) -> PathBuf {
        self.get("tmpdir".into())
            .map(PathBuf::from)
            .unwrap_or_default()
    }

    fn read_text(&self, path: &Path) -> Option<String> {
        if self.is_library {
            return self.get(format!("text:{}", path.display()));
        }
        // As the CLI read a file before, with readFileSync's UTF-8, and TLC reads text not in it.
        Some(String::from_utf8_lossy(&self.read_bytes(path)?).into_owned())
    }

    fn read_bytes(&self, path: &Path) -> Option<Vec<u8>> {
        self.sources.get_bytes(format!("bytes:{}", path.display()))
    }

    fn list_directory(&self, path: &Path) -> Option<Vec<Entry>> {
        parse_entries(&self.get(format!("entries:{}", path.display()))?)
    }

    // JavaScript applies the operations once the check returns.
    fn apply(&self, operation: &FileOperation) -> bool {
        self.files.borrow_mut().push(operation.clone());
        true
    }

    fn load_module(&self, directories: &[&Path], name: &str) -> Result<Option<String>, PathBuf> {
        if self.is_library {
            return Ok(self.get(format!("module:{name}")));
        }
        resolve::load_module(self, directories, name)
    }

    fn load_class(&self, directories: &[&Path], name: &str) -> Option<(PathBuf, Vec<u8>)> {
        if self.is_library {
            let bytes = self.sources.get_bytes(format!("class:{name}"))?;
            return Some((PathBuf::from(format!("{name}.class")), bytes));
        }
        resolve::load_class(self, directories, name)
    }

    fn get_file_describer<'h>(&'h self, files: &Files) -> FileDescription<'h> {
        if self.is_library {
            return Box::new(|_, _| Ok(String::new()));
        }
        let describer = FileDescriber::new(files, self);
        Box::new(move |name, origin| describer.describe(name, origin))
    }

    fn get_variable(&self, name: &str) -> Option<String> {
        self.variables
            .iter()
            .find(|(variable, _)| variable == name)
            .map(|(_, value)| value.clone())
    }

    fn now(&self) -> SystemTime {
        self.now + self.started.elapsed()
    }

    fn zone(&self) -> &Zone {
        &self.zone
    }

    fn machine(&self) -> &Machine {
        &self.machine
    }

    fn is_file_system(&self) -> bool {
        !self.is_library
    }

    fn read_spec_file(&self, path: &str) -> Option<Vec<u8>> {
        self.get(format!("read:{path}")).map(String::into_bytes)
    }

    fn spec_files_read(&self) -> Vec<(String, Option<Vec<u8>>)> {
        self.sources
            .get_answered_with("read:")
            .into_iter()
            .map(|(key, text)| {
                (
                    key["read:".len()..].to_owned(),
                    text.map(String::into_bytes),
                )
            })
            .collect()
    }

    // The check's writes go back to JavaScript, which writes them: the library's, which answers
    // for files itself, and the CLI's into a directory it said it can write.
    fn write_file(&self, path: &Path, bytes: &[u8], is_appended: bool) -> bool {
        let is_written = self.is_library || self.is_writable(path);
        if is_written {
            self.writes.borrow_mut().push((
                path.display().to_string(),
                bytes.to_vec(),
                is_appended,
            ));
        }
        is_written
    }

    fn prepare_write(&self, path: &Path) {
        if !self.is_library {
            self.is_writable(path);
        }
    }

    // The CLI's answer is what `prepare_write` asked, so that nothing new is asked once the check
    // has searched.
    fn can_write(&self, path: &Path) -> bool {
        if self.is_library {
            return is_directory_there(self, path);
        }
        self.is_writable(path)
    }

    fn is_plain(&self) -> bool {
        self.is_library
    }

    fn is_complete(&self) -> bool {
        !self.sources.has_needed()
    }

    // The library names a module by its name alone, which several specs in different directories
    // could each resolve to another file. For the CLI, a spec that declines after another one fails
    // would end in the other's exit code, which `check` doesn't take for a decline, so the
    // TypeScript check checks each spec.
    fn is_checking_several(&self) -> bool {
        false
    }
}

fn get_number(value: &HostValue, what: &str) -> Result<f64, String> {
    match value {
        HostValue::Number(number) => Ok(*number),
        _ => Err(format!("{what} must be a number")),
    }
}

/// The stack of the thread the check runs on, as the binary's run thread has.
#[cfg(not(target_arch = "wasm32"))]
const CHECK_STACK_BYTES: usize = 64 * 1024 * 1024;

/// `checkSources(args, known, machine)`, on this thread: wasm's stack is the one it links.
#[cfg(target_arch = "wasm32")]
pub fn check_sources(arguments: &[HostValue]) -> HookResult {
    check(arguments)
}

/// `checkSources(args, known, machine)`, on a thread with a deep stack.
#[cfg(not(target_arch = "wasm32"))]
pub fn check_sources(arguments: &[HostValue]) -> HookResult {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(CHECK_STACK_BYTES)
            .spawn_scoped(scope, || check(arguments))
            .expect("a thread for the check")
            .join()
            .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
    })
}

fn check(arguments: &[HostValue]) -> HookResult {
    let [args, known, machine] = arguments else {
        return Err("checkSources takes the arguments, what is known and the machine".into());
    };
    let args = get_strings(args, "the arguments")?;
    let HostValue::Array(machine) = machine else {
        return Err("the machine must be an array".into());
    };
    let [
        system,
        release,
        arch,
        cores,
        memory,
        pid,
        now,
        zone,
        variables,
        is_library,
    ] = machine.as_slice()
    else {
        return Err("the machine must be [system, release, arch, cores, memoryMegabytes, pid, now, zone, variables, isLibrary]".into());
    };
    let HostValue::Bool(is_library) = *is_library else {
        return Err("isLibrary must be a boolean".into());
    };
    let HostValue::Array(variables) = variables else {
        return Err("the variables must be an array of [name, value] pairs".into());
    };
    let variables = variables
        .iter()
        .map(|pair| match get_strings(pair, "a variable")?.as_slice() {
            [name, value] => Ok((name.clone(), value.clone())),
            _ => Err("a variable must be a [name, value] pair".to_owned()),
        })
        .collect::<Result<_, String>>()?;
    let host = SourcesHost {
        sources: Sources::new(known)?,
        machine: Machine {
            system: get_text(system, "the system")?,
            release: get_text(release, "the release")?,
            arch: get_text(arch, "the architecture")?,
            cores: get_number(cores, "the cores")?.max(1.0) as usize,
            memory_megabytes: get_number(memory, "the memory")? as u64,
            pid: get_number(pid, "the pid")? as u32,
        },
        now: UNIX_EPOCH + Duration::from_millis(get_number(now, "now")? as u64),
        started: Instant::now(),
        zone: parse_rule(&get_text(zone, "the zone")?).map_or(Zone::UTC, Zone::from_rule),
        variables,
        is_library,
        writes: RefCell::default(),
        files: RefCell::default(),
    };
    let (mut out, mut err) = (Vec::new(), Vec::new());
    let mut output = Output {
        out: &mut out,
        err: &mut err,
        host: &host,
        outcome: Outcome::default(),
    };
    let exit_code = prove_it_check::run(&args, &mut output);
    let outcome = output.outcome;
    if let Some(needed) = host.sources.get_needed() {
        return Ok(needed);
    }
    let err = String::from_utf8_lossy(&err);
    // What the binary prints as it declines, which the host checks otherwise: what was printed
    // before it is dropped.
    let declined = match &outcome.thrown {
        Some(Thrown::NotNative(reason)) if outcome.status.is_none() => Some(*reason),
        _ => err
            .lines()
            .find_map(|line| line.strip_prefix(NOT_NATIVE))
            .filter(|_| exit_code == 1),
    };
    if let Some(reason) = declined {
        return Ok(HostValue::Object(vec![
            ("kind", HostValue::text("declined")),
            ("reason", HostValue::text(reason)),
        ]));
    }
    Ok(HostValue::Object(vec![
        ("kind", HostValue::text("checked")),
        ("exitCode", HostValue::Number(f64::from(exit_code))),
        ("out", HostValue::text(&String::from_utf8_lossy(&out))),
        ("err", HostValue::text(&err)),
        ("thrown", get_thrown(&outcome)),
        ("outcome", get_outcome(outcome)),
        (
            "writes",
            HostValue::Array(
                host.writes
                    .take()
                    .into_iter()
                    .map(|(path, bytes, is_appended)| {
                        HostValue::Object(vec![
                            ("path", HostValue::text(&path)),
                            ("bytes", HostValue::Uint8s(bytes)),
                            ("isAppended", HostValue::Bool(is_appended)),
                        ])
                    })
                    .collect(),
            ),
        ),
        ("files", get_journal(&host.files.borrow())),
    ]))
}

/// Where the check stopped before it searched, the error the library throws, with what the spec
/// printed before it, which the library prints first: `{ kind: "syntax", sany, prints }` with the
/// report of `TlaSyntaxError`, `{ kind: "config" | "evaluation", message, prints }`, or
/// `{ kind: "stack-overflow", prints }`; undefined otherwise.
fn get_thrown(outcome: &Outcome) -> HostValue {
    let (Some(thrown), None) = (&outcome.thrown, outcome.status) else {
        return HostValue::Undefined;
    };
    let prints = (
        "prints",
        HostValue::Array(
            outcome
                .prints
                .iter()
                .map(|text| HostValue::text(text))
                .collect(),
        ),
    );
    let get_errors = |errors: &[SanyError]| {
        HostValue::Array(
            errors
                .iter()
                .map(|error| {
                    HostValue::Object(vec![
                        ("location", HostValue::text(&error.location)),
                        ("message", HostValue::text(&error.message)),
                    ])
                })
                .collect(),
        )
    };
    match thrown {
        Thrown::Syntax(report) => HostValue::Object(vec![
            ("kind", HostValue::text("syntax")),
            (
                "sany",
                HostValue::Object(vec![
                    ("errors", get_errors(&report.errors)),
                    ("warnings", get_errors(&report.warnings)),
                    ("isFatal", HostValue::Bool(report.is_fatal)),
                    (
                        "parseError",
                        report
                            .parse_error
                            .as_ref()
                            .map_or(HostValue::Undefined, |text| HostValue::text(text)),
                    ),
                ]),
            ),
            prints,
        ]),
        Thrown::Config(message) => HostValue::Object(vec![
            ("kind", HostValue::text("config")),
            ("message", HostValue::text(message)),
            prints,
        ]),
        Thrown::Evaluation(message) => HostValue::Object(vec![
            ("kind", HostValue::text("evaluation")),
            ("message", HostValue::text(message)),
            prints,
        ]),
        Thrown::StackOverflow => {
            HostValue::Object(vec![("kind", HostValue::text("stack-overflow")), prints])
        }
        Thrown::NotNative(_) => HostValue::Undefined,
    }
}

/// The outcome the library reads, or undefined where the check stopped before it searched.
fn get_outcome(outcome: Outcome) -> HostValue {
    let Some(status) = outcome.status else {
        return HostValue::Undefined;
    };
    let counts = outcome.counts;
    let violations = outcome.violations.into_iter().map(|reported| {
        let states = reported.states.into_iter().map(|state| {
            let variables = state.variables.into_iter().map(|variable| {
                HostValue::Array(vec![
                    HostValue::text(&variable.name),
                    HostValue::text(&variable.text),
                    HostValue::text(&variable.data),
                ])
            });
            HostValue::Object(vec![
                ("label", HostValue::text(&state.label)),
                ("variables", HostValue::Array(variables.collect())),
            ])
        });
        HostValue::Object(vec![
            ("code", HostValue::Number(f64::from(reported.code))),
            ("headline", HostValue::text(&reported.headline)),
            ("states", HostValue::Array(states.collect())),
            (
                "loopStart",
                reported.loop_start.map_or(HostValue::Undefined, |start| {
                    HostValue::Number(start as f64)
                }),
            ),
        ])
    });
    HostValue::Object(vec![
        ("status", HostValue::text(status)),
        (
            "generatedStates",
            HostValue::Number(counts.generated as f64),
        ),
        ("distinctStates", HostValue::Number(counts.distinct as f64)),
        ("queuedStates", HostValue::Number(counts.queued as f64)),
        ("depth", HostValue::Number(counts.depth as f64)),
        (
            "prints",
            HostValue::Array(
                outcome
                    .prints
                    .iter()
                    .map(|text| HostValue::text(text))
                    .collect(),
            ),
        ),
        (
            "sanyWarnings",
            HostValue::Array(
                outcome
                    .sany_warnings
                    .iter()
                    .map(|text| HostValue::text(text))
                    .collect(),
            ),
        ),
        ("violations", HostValue::Array(violations.collect())),
        (
            "messages",
            HostValue::Array(
                outcome
                    .messages
                    .iter()
                    .map(|message| {
                        HostValue::Array(vec![
                            HostValue::Number(f64::from(message.code)),
                            HostValue::Number(f64::from(message.level)),
                            HostValue::text(&message.text),
                            HostValue::Number(message.prints_before as f64),
                            message.counts.map_or(HostValue::Undefined, |counts| {
                                HostValue::Array(
                                    [
                                        counts.generated,
                                        counts.distinct,
                                        counts.queued,
                                        counts.depth,
                                    ]
                                    .map(|count| HostValue::Number(count as f64))
                                    .into(),
                                )
                            }),
                        ])
                    })
                    .collect(),
            ),
        ),
    ])
}

/// `resolveFiles(args, given, request, known)`: one of `{ kind: "needed", keys }`,
/// `{ kind: "declined", reason }`, or for the request (`resolve_files`):
///
/// - `spec`: `{ kind: "spec", path, name, directories, config, missingConfig, unreadable, missing }`,
///   with the configuration's path or the name TLC says it doesn't find, a file TLC finds but can't
///   read, and what TLC prints where it doesn't find the spec;
/// - `module:<name>`: `{ kind: "module", text }`, or `{ kind: "unreadable", path }`;
/// - `class:<name>`: `{ kind: "class", path, bytes }`;
/// - `file:<origin>:<name>` and `missing:<file name>`: `{ kind: "text", text }`.
pub fn resolve_files(arguments: &[HostValue]) -> HookResult {
    let [args, given, request, known] = arguments else {
        return Err(
            "resolveFiles takes the arguments, the spec, the request and what is known".into(),
        );
    };
    let args = get_strings(args, "the arguments")?;
    let host = SourcesHost {
        sources: Sources::new(known)?,
        machine: Machine {
            system: String::new(),
            release: String::new(),
            arch: String::new(),
            cores: 1,
            memory_megabytes: 0,
            pid: 0,
        },
        now: UNIX_EPOCH,
        started: Instant::now(),
        zone: Zone::UTC,
        variables: Vec::new(),
        is_library: false,
        writes: RefCell::default(),
        files: RefCell::default(),
    };
    let resolved = resolve::resolve_files(
        &args,
        &get_text(given, "the spec")?,
        &get_text(request, "the request")?,
        &host,
    );
    if let Some(needed) = host.sources.get_needed() {
        return Ok(needed);
    }
    let path = |path: &Path| HostValue::text(&path.to_string_lossy());
    let optional =
        |text: Option<String>| text.map_or(HostValue::Undefined, |text| HostValue::text(&text));
    Ok(HostValue::Object(match resolved {
        Resolved::Spec {
            path: spec,
            name,
            directories,
            config,
            unreadable,
            missing,
        } => {
            let (config, missing_config) = match config {
                Config::Found(found) => (path(&found), HostValue::Undefined),
                Config::Missing(name) => (HostValue::Undefined, HostValue::text(&name)),
                Config::NotNative(reason) => {
                    return Ok(HostValue::Object(vec![
                        ("kind", HostValue::text("declined")),
                        ("reason", HostValue::text(reason)),
                    ]));
                }
            };
            vec![
                ("kind", HostValue::text("spec")),
                ("path", HostValue::text(&spec)),
                ("name", HostValue::text(&name)),
                (
                    "directories",
                    HostValue::Array(
                        directories
                            .iter()
                            .map(|directory| HostValue::text(directory))
                            .collect(),
                    ),
                ),
                ("config", config),
                ("missingConfig", missing_config),
                (
                    "unreadable",
                    unreadable.map_or(HostValue::Undefined, |found| path(&found)),
                ),
                ("missing", optional(missing)),
            ]
        }
        Resolved::Module(Ok(text)) => vec![
            ("kind", HostValue::text("module")),
            ("text", optional(text)),
        ],
        Resolved::Module(Err(found)) => vec![
            ("kind", HostValue::text("unreadable")),
            ("path", path(&found)),
        ],
        Resolved::Class(class) => {
            let (found, bytes) = class.map_or(
                (HostValue::Undefined, HostValue::Undefined),
                |(found, bytes)| (path(&found), HostValue::Uint8s(bytes)),
            );
            vec![
                ("kind", HostValue::text("class")),
                ("path", found),
                ("bytes", bytes),
            ]
        }
        Resolved::Text(text) => vec![
            ("kind", HostValue::text("text")),
            ("text", HostValue::text(&text)),
        ],
        Resolved::NotNative(reason) => vec![
            ("kind", HostValue::text("declined")),
            ("reason", HostValue::text(&reason)),
        ],
    }))
}

#[cfg(test)]
mod tests {
    use super::*;

    // A check's dates go on from the time it was given, so the date it finishes at is not the date
    // it started at.
    #[test]
    fn the_clock_goes_on_from_the_time_given() {
        let host = SourcesHost {
            sources: Sources::new(&HostValue::Array(Vec::new())).expect("no sources"),
            machine: Machine {
                system: String::new(),
                release: String::new(),
                arch: String::new(),
                cores: 1,
                memory_megabytes: 1,
                pid: 1,
            },
            now: UNIX_EPOCH,
            started: Instant::now(),
            zone: Zone::UTC,
            variables: Vec::new(),
            is_library: false,
            writes: RefCell::default(),
            files: RefCell::default(),
        };
        let first = host.now();
        std::thread::sleep(Duration::from_millis(5));
        assert!(host.now() > first && first >= UNIX_EPOCH);
    }
}
