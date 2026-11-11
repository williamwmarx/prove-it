//! What a check reads from the host it runs on: the spec's files and facts about the machine. The
//! binary reads them from the file system and its process (`SystemHost`); a host that runs the
//! check in-process answers them itself.

use std::path::Path;
use std::time::SystemTime;

use tla_engine::search::Advice;
use tla_front::report::ModuleOrigin;

use crate::files::FileDescriber;
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

/// What names the files of a spec's modules as TLC prints them: the spec, the libraries, the
/// JVM's temporary directory and -metadir where the launch sets them, and the tla2tools.jar on the
/// class path, which TLC copies the standard modules from.
pub struct Files<'a> {
    pub spec: &'a Path,
    pub libraries: &'a [String],
    pub temporary: Option<&'a str>,
    pub metadir: Option<&'a str>,
    pub jar: Option<&'a str>,
    pub is_174: bool,
    /// TLC records the trace for its trace exploration spec, so SANY parses `_TLCTrace` too.
    pub is_trace_recorded: bool,
}

/// The path TLC prints for the file it parses a module from, by the module's name and origin.
pub type FileDescription<'h> = Box<dyn Fn(&str, ModuleOrigin) -> String + 'h>;

pub trait Host {
    fn is_file(&self, path: &Path) -> bool;
    fn read_text(&self, path: &Path) -> Option<String>;
    /// The bytes of a file, such as a tla2tools.jar.
    fn read_bytes(&self, path: &Path) -> Option<Vec<u8>>;
    /// A module's text: `<name>.tla` in the first of the directories that has it.
    fn load_module(&self, directories: &[&Path], name: &str) -> Option<String>;
    /// The Java override TLC loads for a module: `<name>.class` in the directory.
    fn load_class(&self, directory: &Path, name: &str) -> Option<Vec<u8>>;
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
    /// Writes the text to the file at the path, after what it holds where `is_appended`, and in
    /// place of it otherwise, such as `-dump`'s; whether it could. A host that writes no files
    /// leaves the check to decline what writes one.
    fn write_file(&self, _path: &Path, _text: &str, _is_appended: bool) -> bool {
        false
    }
    /// Whether the check may read and write the machine's files, as the Json module's operators
    /// do (`Settings::is_file_system`).
    fn is_file_system(&self) -> bool {
        true
    }
    /// Whether the check writes each printed state's variables as plain data too, which only the
    /// library's check reads (`Outcome`).
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
    fn is_file(&self, path: &Path) -> bool {
        path.exists()
    }

    fn read_text(&self, path: &Path) -> Option<String> {
        std::fs::read_to_string(path).ok()
    }

    fn write_file(&self, path: &Path, text: &str, is_appended: bool) -> bool {
        std::fs::OpenOptions::new()
            .create(true)
            .write(true)
            .append(is_appended)
            .truncate(!is_appended)
            .open(path)
            .and_then(|mut file| std::io::Write::write_all(&mut file, text.as_bytes()))
            .is_ok()
    }

    fn read_bytes(&self, path: &Path) -> Option<Vec<u8>> {
        std::fs::read(path).ok()
    }

    fn load_module(&self, directories: &[&Path], name: &str) -> Option<String> {
        directories
            .iter()
            .find_map(|directory| self.read_text(&directory.join(format!("{name}.tla"))))
    }

    fn load_class(&self, directory: &Path, name: &str) -> Option<Vec<u8>> {
        std::fs::read(directory.join(format!("{name}.class"))).ok()
    }

    fn get_file_describer<'h>(&'h self, files: &Files) -> FileDescription<'h> {
        let describer = FileDescriber::new(files);
        Box::new(move |name, origin| describer.describe(name, origin))
    }

    fn get_variable(&self, name: &str) -> Option<String> {
        std::env::var(name).ok()
    }

    fn now(&self) -> SystemTime {
        SystemTime::now()
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
