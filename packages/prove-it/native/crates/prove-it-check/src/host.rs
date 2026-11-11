//! What a check reads from the host it runs on: the spec's files and facts about the machine. The
//! binary reads them from the file system and its process (`SystemHost`); a host that runs the
//! check in-process answers them itself.

use std::path::{Path, PathBuf};
use std::time::SystemTime;

use tla_engine::search::Advice;
use tla_front::report::ModuleOrigin;

use crate::files::FileDescriber;
use crate::host_path::Platform;
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
}

/// The path TLC prints for the file it parses a module from, by the module's name and origin.
pub type FileDescription<'h> = Box<dyn Fn(&str, ModuleOrigin) -> String + 'h>;

/// What is at a path: nothing the system can follow to, a directory, or anything else, which TLC
/// reads as a file.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FileKind {
    Absent,
    File,
    Directory,
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
    /// Whether the check may read and write the machine's files, as the Json module's operators
    /// do (`Settings::is_file_system`).
    fn is_file_system(&self) -> bool {
        true
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
    fn kind(&self, path: &Path) -> FileKind {
        match std::fs::metadata(path) {
            Ok(metadata) if metadata.is_dir() => FileKind::Directory,
            Ok(_) => FileKind::File,
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

    fn load_module(&self, directories: &[&Path], name: &str) -> Result<Option<String>, PathBuf> {
        resolve::load_module(self, directories, name)
    }

    fn load_class(&self, directories: &[&Path], name: &str) -> Option<(PathBuf, Vec<u8>)> {
        resolve::load_class(self, directories, name)
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
