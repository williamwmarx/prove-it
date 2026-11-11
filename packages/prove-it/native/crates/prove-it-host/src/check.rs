//! The native binary's check, in-process, for the library and the CLI of `dist/`:
//! `checkSources(args, known, machine)` checks the spec the TLC command line `args` names as the
//! binary does, reading its files from what JavaScript knows (`sources`), and returns one of:
//!
//! - `{ kind: "checked", exitCode, out, err, outcome }`, what the binary prints to stdout and
//!   stderr, its exit code, and what the check found where it searched, as the library reports it
//!   (`get_outcome`);
//! - `{ kind: "needed", keys }`, what the check reads that isn't known yet (`sources`). It asks for
//!   everything before it searches, so a round never searches;
//! - `{ kind: "declined", reason }`, where the binary prints `not native yet`, without what it
//!   printed before.
//!
//! The keys it reads, besides SANY's `module:` and `file:`, are `text:<path>`, the text of the file
//! at a path the command line names (the spec and its configuration), `bytes:<path>`, the bytes of
//! the tla2tools.jar on a Java launch's class path, and `class:<name>`, the Java override for a
//! module, both as a Uint8Array. `machine` gives what TLC's banner and dates describe, and what the
//! check may use of it:
//! `[system, release, arch, cores, memoryMegabytes, pid, now, zone, variables, isLibrary]`, with
//! `now` in milliseconds since the epoch, `zone` a POSIX TZ rule, `variables` the environment's
//! `[name, value]` pairs the check reads, and `isLibrary` whether the library's check runs it: the
//! library answers for files itself, so the Json module's operators don't touch the machine's, and
//! it reads each printed state's plain data, which the CLI doesn't, so only it has the check write
//! them.

use std::path::Path;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use prove_it_check::zone::{Zone, parse_rule};
use prove_it_check::{FileDescription, Files, Host, Machine, Outcome, Output};
use tla_engine::clock::Instant;
use tla_front::report::ModuleOrigin;

use crate::hooks::HookResult;
use crate::sources::{Sources, get_text};
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
}

impl SourcesHost {
    fn get(&self, key: String) -> Option<String> {
        self.sources.get(key)
    }
}

fn get_origin(origin: ModuleOrigin) -> &'static str {
    match origin {
        ModuleOrigin::File => "file",
        ModuleOrigin::RootFile => "root file",
        ModuleOrigin::Standard => "standard",
    }
}

impl Host for SourcesHost {
    fn is_file(&self, path: &Path) -> bool {
        self.read_text(path).is_some()
    }

    fn read_text(&self, path: &Path) -> Option<String> {
        self.get(format!("text:{}", path.display()))
    }

    fn read_bytes(&self, path: &Path) -> Option<Vec<u8>> {
        self.sources.get_bytes(format!("bytes:{}", path.display()))
    }

    fn load_module(&self, _directories: &[&Path], name: &str) -> Option<String> {
        self.get(format!("module:{name}"))
    }

    fn load_class(&self, _directory: &Path, name: &str) -> Option<Vec<u8>> {
        self.sources.get_bytes(format!("class:{name}"))
    }

    fn get_file_describer<'h>(&'h self, _files: &Files) -> FileDescription<'h> {
        Box::new(move |name, origin| {
            self.get(format!("file:{}:{name}", get_origin(origin)))
                .unwrap_or_default()
        })
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

    fn is_plain(&self) -> bool {
        self.is_library
    }

    fn is_complete(&self) -> bool {
        !self.sources.has_needed()
    }

    // `module:`, `class:` and `file:` name a module by its name alone, which several specs in
    // different directories could each resolve to another file.
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

fn get_strings(value: &HostValue, what: &str) -> Result<Vec<String>, String> {
    match value {
        HostValue::Array(items) => items.iter().map(|item| get_text(item, what)).collect(),
        _ => Err(format!("{what} must be an array of strings")),
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
    if let Some(reason) = err.lines().find_map(|line| line.strip_prefix(NOT_NATIVE))
        && exit_code == 1
    {
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
        ("outcome", get_outcome(outcome)),
    ]))
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
        ("violations", HostValue::Array(violations.collect())),
    ])
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
        };
        let first = host.now();
        std::thread::sleep(Duration::from_millis(5));
        assert!(host.now() > first && first >= UNIX_EPOCH);
    }
}
