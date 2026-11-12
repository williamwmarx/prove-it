//! What a check reads from the host it runs on: the spec's files and facts about the machine. The
//! binary reads them from the file system and its process (`SystemHost`); a host that runs the
//! check in-process answers them itself.

use std::path::{Path, PathBuf};
use std::time::SystemTime;

use tla_engine::search::Advice;
use tla_front::report::ModuleOrigin;

use crate::files::FileDescriber;
use crate::overlay::FileOperation;
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

/// What a path names, where it names something.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PathKind {
    File,
    Directory,
    Other,
}

/// An entry of a directory, with when it was last modified, in milliseconds since the epoch as
/// Node's `mtimeMs` gives it.
#[derive(Clone, Debug, PartialEq)]
pub struct Entry {
    pub name: String,
    pub modified: f64,
}

pub trait Host {
    fn is_file(&self, path: &Path) -> bool;
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
    /// What the path names, as tlapm's command line asks, which writes its cache beside the
    /// modules. A host that answers none of these, nor the operations below, writes no cache, and
    /// the command declines.
    fn get_path_kind(&self, _path: &Path) -> Option<PathKind> {
        None
    }
    /// The path with every link resolved, as Node's `realpathSync` gives it.
    fn get_real_path(&self, _path: &Path) -> Option<PathBuf> {
        None
    }
    /// The entries of a directory, in no particular order.
    fn list_directory(&self, _path: &Path) -> Option<Vec<Entry>> {
        None
    }
    /// Applies an operation on the files tlapm's command line held back until its run ended;
    /// whether it could.
    fn apply(&self, _operation: &FileOperation) -> bool {
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
    fn is_file(&self, path: &Path) -> bool {
        path.exists()
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

    fn get_path_kind(&self, path: &Path) -> Option<PathKind> {
        let metadata = std::fs::metadata(path).ok()?;
        Some(if metadata.is_file() {
            PathKind::File
        } else if metadata.is_dir() {
            PathKind::Directory
        } else {
            PathKind::Other
        })
    }

    fn get_real_path(&self, path: &Path) -> Option<PathBuf> {
        std::fs::canonicalize(path).ok()
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
        let Some(path) = directories
            .iter()
            .map(|directory| directory.join(format!("{name}.tla")))
            .find(|path| path.exists())
        else {
            return Ok(None);
        };
        std::fs::read_to_string(&path).map(Some).map_err(|_| path)
    }

    // TLCClass loads no override from a class file it finds but can't read.
    fn load_class(&self, directories: &[&Path], name: &str) -> Option<(PathBuf, Vec<u8>)> {
        let path = directories
            .iter()
            .map(|directory| directory.join(format!("{name}.class")))
            .find(|path| path.exists())?;
        std::fs::read(&path).ok().map(|bytes| (path, bytes))
    }

    fn get_file_describer<'h>(&'h self, files: &Files) -> FileDescription<'h> {
        let describer = FileDescriber::new(files);
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
