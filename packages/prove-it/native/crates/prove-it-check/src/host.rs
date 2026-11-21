//! What a check reads from the host it runs on: the spec's files and facts about the machine. The
//! binary reads them from the file system and its process (`SystemHost`); a host that runs the
//! check in-process answers them itself.

use std::path::{Path, PathBuf};
use std::time::SystemTime;

use tla_engine::search::Advice;
use tla_front::report::ModuleOrigin;

use crate::files::FileDescriber;
use crate::host_path::Platform;
use crate::overlay::FileOperation;
use crate::resolve;
use crate::zone::Zone;

/// The machine TLC's banner describes.
pub struct Machine {
    /// The kernel's name and release, as Node's os.type() and os.release() give them, and the
    /// architecture, as Node's process.arch names it.
    pub system: String,
    pub release: String,
    pub arch: String,
    pub cores: usize,
    pub memory_megabytes: u64,
    pub pid: u32,
}

/// What names the files of a spec's modules as TLC prints them: the spec, the directories TLC
/// finds its modules in, the JVM's temporary directory and -metadir where the launch sets them, and
/// the tla2tools.jar on the class path, which TLC copies the standard modules from.
pub struct Files<'a> {
    /// The execution boundary's explicit reference choice, independent of class absence.
    pub parent_runtime: tla_front::model::ParentRuntime,
    pub java_profile: tla_front::model::JavaProfile,
    pub spec: &'a Path,
    /// The spec as TLC was given it, without `.tla`, which SANY names it by.
    pub main_file: &'a str,
    /// The directories in TLC's order (`get_module_directories`), the working directory as "".
    pub directories: &'a [String],
    pub temporary: Option<&'a str>,
    pub metadir: Option<&'a str>,
    pub jar: Option<&'a str>,
    pub is_174: bool,
    /// The modules of TLC's post conditions, which SANY parses with the spec
    /// (`ModelOptions::root_extendees`).
    pub root_extendees: &'a [&'a str],
    /// Lines the model's lowering reads at the end of the root module, before its `====`: the
    /// definitions of the command line's `-inv` invariants (`insert_before_module_end`).
    pub appended: &'a str,
    /// What -suppressMessages and -messagesAsErrors make of SANY's linter's warnings.
    pub lint_codes: tla_front::report::LintCodes,
}

/// The path TLC prints for the file it parses a module from, by the module's name and origin.
pub type FileDescription<'h> = Box<dyn Fn(&str, ModuleOrigin) -> Result<String, String> + 'h>;

/// What is at a path: nothing the system can follow to, a file, a directory, or anything else, such
/// as a FIFO, which TLC reads as a file and tlapm's loader can't.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FileKind {
    Absent,
    File,
    Directory,
    Other,
}

impl FileKind {
    /// Whether TLC reads what is there as a file.
    pub fn is_read_by_tlc(self) -> bool {
        matches!(self, FileKind::File | FileKind::Other)
    }
}

/// An entry of a directory, with when it was last modified, in milliseconds since the epoch as
/// Node's `mtimeMs` gives it.
#[derive(Clone, Debug, PartialEq)]
pub struct Entry {
    pub name: String,
    pub modified: f64,
}

/// Whether the directory that holds the file is there, or the path names none.
pub fn is_directory_there<H: Host + ?Sized>(host: &H, path: &Path) -> bool {
    let text = path.to_string_lossy();
    host.platform()
        .last_separator(&text)
        .is_none_or(|end| host.is_file(Path::new(&text[..end.max(1)])))
}

pub trait Host {
    /// The rules the host names its files by, which the engine as WebAssembly learns from
    /// JavaScript.
    fn platform(&self) -> Platform {
        Platform::NATIVE
    }
    /// What is at the path, which TLC's resolver takes for found unless it is absent.
    fn kind(&self, path: &Path) -> FileKind;
    fn is_file(&self, path: &Path) -> bool {
        self.kind(path) != FileKind::Absent
    }
    /// The path with its links followed and `.` and `..` resolved, as the system resolves them.
    fn real_path(&self, path: &Path) -> Option<PathBuf>;
    /// The working directory, which TLC's resolver searches as "".
    fn current_dir(&self) -> PathBuf;
    /// The JVM's default `java.io.tmpdir`.
    fn temp_dir(&self) -> PathBuf;
    fn read_text(&self, path: &Path) -> Option<String>;
    /// The bytes of a file, such as a tla2tools.jar.
    fn read_bytes(&self, path: &Path) -> Option<Vec<u8>>;
    /// A module's text: `<name>.tla` in the first of the directories that has it, or that path
    /// where TLC finds it there but can't read it, as a directory (`FileUtil.toIStream`).
    fn load_module(&self, directories: &[&Path], name: &str) -> Result<Option<String>, PathBuf>;
    /// The Java override TLC loads for a module: `<name>.class` in the first of the directories
    /// that has it, by the path TLC's resolver makes for it, and its bytes; none where TLC can't
    /// read that file.
    fn load_class(&self, directories: &[&Path], name: &str) -> Option<(PathBuf, Vec<u8>)>;
    /// Explicit supported reference-runtime choice, never an ambient JVM probe.
    /// A generic host supplies no parent-runtime witness.
    fn modeled_parent_runtime(&self, _is_java_launch: bool) -> tla_front::model::ParentRuntime {
        tla_front::model::ParentRuntime::Unknown
    }

    fn class_origin(&self, _directories: &[&Path], _name: &str) -> tla_front::model::ClassOrigin {
        tla_front::model::ClassOrigin::Unknown
    }
    fn get_file_describer<'h>(&'h self, files: &Files) -> FileDescription<'h>;
    /// An environment variable.
    fn get_variable(&self, name: &str) -> Option<String>;
    fn now(&self) -> SystemTime;
    fn zone(&self) -> &Zone;
    fn machine(&self) -> &Machine;
    /// Whether the host holds everything the check has read so far. A host that answers what it
    /// lacks once the check returns has the check stop before it searches.
    fn is_complete(&self) -> bool {
        true
    }
    /// Whether the host answers for several specs in one run, each from its own directories. A
    /// host that names a module only by its name can't.
    fn is_checking_several(&self) -> bool {
        true
    }
    /// What the host tells the system of the search's large regions of memory
    /// (`Settings::large_region_advice`).
    fn large_region_advice(&self) -> Option<Advice> {
        None
    }
    /// Writes the bytes to the file at the path, after what it holds where `is_appended`, and in
    /// place of it otherwise, such as `-dump`'s; whether it could. A host that writes no files
    /// leaves the check to decline what writes one.
    fn write_file(&self, _path: &Path, _bytes: &[u8], _is_appended: bool) -> bool {
        false
    }
    /// Says, before the check searches, a file it may write after it, so that a host that answers
    /// what it lacks once the check returns knows it before then.
    fn prepare_write(&self, _path: &Path) {}
    /// Why Java's `FileInputStream`, or its `FileOutputStream` where `is_written`, can't open the
    /// file, as its FileNotFoundException words it after the path, such as `No such file or
    /// directory`; none where it can, or where the host doesn't know. A file opened to be written
    /// is created, as Java creates it.
    fn open_failure(&self, _path: &Path, _is_written: bool) -> Option<String> {
        None
    }
    /// Whether the host can write the file: TLC writes a JSON dump into the directories it makes
    /// and a `tlc` one into the directory that holds it, and fails where it can't.
    fn can_write(&self, path: &Path) -> bool {
        is_directory_there(self, path)
    }
    /// The entries of a directory, in no particular order, as tlapm's command line reads its
    /// cache's history. A host that answers none of these, nor the operations below, writes no
    /// cache, and the command declines.
    fn list_directory(&self, _path: &Path) -> Option<Vec<Entry>> {
        None
    }
    /// Applies an operation on the files tlapm's command line held back until its run ended;
    /// whether it could.
    fn apply(&self, _operation: &FileOperation) -> bool {
        false
    }
    /// Whether the check may read and write the machine's files, as the Json module's operators
    /// do (`Settings::json_files`).
    fn is_file_system(&self) -> bool {
        true
    }
    /// For a host that answers for the files itself, the bytes of a file the spec reads, as the
    /// Json module's operators do, or none where there is none; it learns of one it hasn't read
    /// yet, which it reads before the check runs again.
    fn read_spec_file(&self, _path: &str) -> Option<Vec<u8>> {
        None
    }
    /// The files the spec reads that the host has read (`read_spec_file`), each with its bytes, or
    /// none where there is none.
    fn spec_files_read(&self) -> Vec<(String, Option<Vec<u8>>)> {
        Vec::new()
    }
    /// Whether the caller reads the outcome (`Outcome`), as only the library's check does: then the
    /// check keeps the spec's prints and each printed state, with its variables as plain data too.
    /// Otherwise it keeps neither, so that a search that prints much holds none of it.
    fn is_plain(&self) -> bool {
        false
    }
}

/// The file system and the process the binary runs in, and the advice the binary gives the system
/// of the search's large regions, such as Linux's huge pages.
pub struct SystemHost {
    zone: Zone,
    machine: Machine,
    large_region_advice: Option<Advice>,
}

impl SystemHost {
    pub fn new(large_region_advice: Option<Advice>) -> Self {
        // Node's os.type(): the kernel's name.
        let system = read_trimmed("/proc/sys/kernel/ostype").unwrap_or_else(|| {
            match std::env::consts::OS {
                "macos" => "Darwin",
                "windows" => "Windows_NT",
                "linux" => "Linux",
                other => other,
            }
            .into()
        });
        let arch = match std::env::consts::ARCH {
            "x86_64" => "x64",
            "aarch64" => "arm64",
            other => other,
        };
        SystemHost {
            zone: Zone::local(),
            machine: Machine {
                system,
                release: read_trimmed("/proc/sys/kernel/osrelease").unwrap_or_default(),
                arch: arch.into(),
                cores: std::thread::available_parallelism().map_or(1, usize::from),
                memory_megabytes: get_memory_megabytes(),
                pid: std::process::id(),
            },
            large_region_advice,
        }
    }
}

impl Host for SystemHost {
    fn modeled_parent_runtime(&self, is_java_launch: bool) -> tla_front::model::ParentRuntime {
        // Bare native invocation defines the supported modeled runtime. An explicit
        // Java launch needs artifact/JDK/manifest attribution that this host lacks.
        if is_java_launch {
            tla_front::model::ParentRuntime::Unknown
        } else {
            tla_front::model::ParentRuntime::ModeledTlcMasterJdk21
        }
    }

    fn kind(&self, path: &Path) -> FileKind {
        match std::fs::metadata(path) {
            Ok(metadata) if metadata.is_dir() => FileKind::Directory,
            Ok(metadata) if metadata.is_file() => FileKind::File,
            Ok(_) => FileKind::Other,
            Err(_) => FileKind::Absent,
        }
    }

    fn real_path(&self, path: &Path) -> Option<PathBuf> {
        std::fs::canonicalize(path).ok()
    }

    fn current_dir(&self) -> PathBuf {
        std::env::current_dir().unwrap_or_default()
    }

    fn temp_dir(&self) -> PathBuf {
        std::env::temp_dir()
    }

    fn read_text(&self, path: &Path) -> Option<String> {
        std::fs::read_to_string(path).ok()
    }

    fn write_file(&self, path: &Path, bytes: &[u8], is_appended: bool) -> bool {
        std::fs::OpenOptions::new()
            .create(true)
            .write(true)
            .append(is_appended)
            .truncate(!is_appended)
            .open(path)
            .and_then(|mut file| std::io::Write::write_all(&mut file, bytes))
            .is_ok()
    }

    fn read_bytes(&self, path: &Path) -> Option<Vec<u8>> {
        std::fs::read(path).ok()
    }

    // The JVM opens a directory and then refuses it (`fileOpen` in io_util_md.c); otherwise it
    // words the system's error as the C library does, which Rust's error repeats before its code.
    fn open_failure(&self, path: &Path, is_written: bool) -> Option<String> {
        if std::fs::metadata(path).is_ok_and(|metadata| metadata.is_dir()) {
            return Some("Is a directory".into());
        }
        let opened = std::fs::OpenOptions::new()
            .read(!is_written)
            .write(is_written)
            .create(is_written)
            .truncate(is_written)
            .open(path);
        let code = opened.err()?.raw_os_error()?;
        let text = std::io::Error::from_raw_os_error(code).to_string();
        text.strip_suffix(&format!(" (os error {code})"))
            .map(String::from)
    }

    fn list_directory(&self, path: &Path) -> Option<Vec<Entry>> {
        std::fs::read_dir(path)
            .ok()?
            .map(|entry| {
                let entry = entry.ok()?;
                Some(Entry {
                    name: entry.file_name().to_string_lossy().into_owned(),
                    modified: get_modified(&entry.path())?,
                })
            })
            .collect()
    }

    fn apply(&self, operation: &FileOperation) -> bool {
        match operation {
            FileOperation::MakeDirectory(path) => std::fs::create_dir_all(path).is_ok(),
            FileOperation::Write(path, bytes) => self.write_file(path, bytes, false),
            FileOperation::Remove(path) => match std::fs::symlink_metadata(path) {
                Err(_) => true,
                Ok(metadata) if metadata.is_dir() => std::fs::remove_dir_all(path).is_ok(),
                Ok(_) => std::fs::remove_file(path).is_ok(),
            },
            FileOperation::Rename(from, to) => std::fs::rename(from, to).is_ok(),
            FileOperation::Copy(from, to) => {
                let copy = || -> std::io::Result<()> {
                    std::fs::copy(from, to)?;
                    let modified = std::fs::metadata(from)?.modified()?;
                    std::fs::File::options()
                        .write(true)
                        .open(to)?
                        .set_modified(modified)
                };
                copy().is_ok()
            }
        }
    }

    fn load_module(&self, directories: &[&Path], name: &str) -> Result<Option<String>, PathBuf> {
        resolve::load_module(self, directories, name)
    }

    fn load_class(&self, directories: &[&Path], name: &str) -> Option<(PathBuf, Vec<u8>)> {
        resolve::load_class(self, directories, name)
    }

    fn class_origin(&self, directories: &[&Path], name: &str) -> tla_front::model::ClassOrigin {
        use tla_front::model::ClassOrigin;
        for directory in directories {
            match std::fs::symlink_metadata(directory.join(format!("{name}.class"))) {
                Ok(_) => return ClassOrigin::Present,
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
                Err(_) => return ClassOrigin::Unknown,
            }
        }
        ClassOrigin::Absent
    }

    fn get_file_describer<'h>(&'h self, files: &Files) -> FileDescription<'h> {
        let describer = FileDescriber::new(files, self);
        Box::new(move |name, origin| describer.describe(name, origin))
    }

    fn get_variable(&self, name: &str) -> Option<String> {
        std::env::var(name).ok()
    }

    // The tests fix the clock with PROVE_IT_TEST_NOW, milliseconds since the epoch, to check
    // what TLC writes of the time it ran.
    fn now(&self) -> SystemTime {
        std::env::var("PROVE_IT_TEST_NOW")
            .ok()
            .and_then(|milliseconds| milliseconds.parse().ok())
            .map_or_else(SystemTime::now, |milliseconds| {
                std::time::UNIX_EPOCH + std::time::Duration::from_millis(milliseconds)
            })
    }

    fn zone(&self) -> &Zone {
        &self.zone
    }

    fn machine(&self) -> &Machine {
        &self.machine
    }

    fn large_region_advice(&self) -> Option<Advice> {
        self.large_region_advice
    }
}

/// `statSync(path).mtimeMs`: seconds and nanoseconds since the epoch as a double of milliseconds.
fn get_modified(path: &Path) -> Option<f64> {
    let since = std::fs::metadata(path)
        .ok()?
        .modified()
        .ok()?
        .duration_since(std::time::UNIX_EPOCH)
        .ok()?;
    Some(since.as_secs() as f64 * 1e3 + f64::from(since.subsec_nanos()) / 1e6)
}

fn read_trimmed(path: &str) -> Option<String> {
    std::fs::read_to_string(path)
        .ok()
        .map(|text| text.trim().to_string())
}

/// The memory the banner reports as the heap: the machine's, since the native search has no limit
/// of its own.
fn get_memory_megabytes() -> u64 {
    std::fs::read_to_string("/proc/meminfo")
        .ok()
        .and_then(|info| {
            let line = info.lines().find(|line| line.starts_with("MemTotal:"))?;
            line.split_whitespace().nth(1)?.parse::<u64>().ok()
        })
        .map_or(0, |kilobytes| kilobytes / 1024)
}

#[cfg(test)]
mod parent_runtime_tests {
    use super::{Host, SystemHost};
    use tla_front::model::ParentRuntime;

    #[test]
    fn native_reference_choice_does_not_attribute_explicit_java_launches() {
        let host = SystemHost::new(None);
        assert_eq!(
            host.modeled_parent_runtime(false),
            ParentRuntime::ModeledTlcMasterJdk21
        );
        assert_eq!(host.modeled_parent_runtime(true), ParentRuntime::Unknown);
    }
}
