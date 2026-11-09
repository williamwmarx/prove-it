//! The paths TLC names the files SANY parses by, as `createFileDescriber` in `src/cli/tlc.ts` writes
//! them: a module's own file, the root module's file copied into a directory named for it, or a
//! standard module copied into a directory named for the spec.

use std::path::{Component, Path, PathBuf};

use tla_front::report::ModuleOrigin;
use tla_values::fingerprint::{INITIAL, extend_byte, extend_int};

const STRING_VALUE: u8 = 3;

pub struct FileDescriber {
    spec: PathBuf,
    directories: Vec<PathBuf>,
    temporary: PathBuf,
    metadir: Option<PathBuf>,
    is_174: bool,
}

impl FileDescriber {
    /// `temporary` is the JVM's `java.io.tmpdir` when the launch sets it.
    pub fn new(
        spec: &Path,
        libraries: &[String],
        temporary: Option<&str>,
        metadir: Option<&str>,
        is_174: bool,
    ) -> FileDescriber {
        let spec = resolve(spec);
        let mut directories = vec![spec.parent().map(Path::to_path_buf).unwrap_or_default()];
        directories.extend(libraries.iter().map(PathBuf::from));
        let temporary = temporary.map_or_else(std::env::temp_dir, PathBuf::from);
        FileDescriber {
            spec,
            directories,
            temporary: std::fs::canonicalize(&temporary).unwrap_or_else(|_| resolve(&temporary)),
            metadir: metadir.map(|metadir| resolve(Path::new(metadir))),
            is_174,
        }
    }

    pub fn describe(&self, name: &str, origin: ModuleOrigin) -> String {
        let file_name = format!("{name}.tla");
        let real = |path: &Path| {
            std::fs::canonicalize(path)
                .unwrap_or_else(|_| path.to_path_buf())
                .display()
                .to_string()
        };
        match origin {
            ModuleOrigin::File => {
                let found = self
                    .directories
                    .iter()
                    .map(|directory| directory.join(&file_name))
                    .find(|path| path.exists());
                real(found.as_deref().unwrap_or(&self.spec))
            }
            // TLC 1.7.4 copies a standard module into the temporary directory itself.
            _ if self.is_174 => self.temporary.join(&file_name).display().to_string(),
            // FileUtil.createTempFile copies a module from the root module's file into the
            // -metadir.
            ModuleOrigin::RootFile => {
                let root = real(&self.spec);
                let directory = self.metadir.as_ref().unwrap_or(&self.temporary);
                let copy = directory
                    .join(temporary_name(&format!("{root} {name}")))
                    .join(&file_name);
                format!("{} ({root})", copy.display())
            }
            ModuleOrigin::Standard => self
                .temporary
                .join(format!(
                    "tlc-{}",
                    temporary_name(&self.spec.display().to_string())
                ))
                .join(&file_name)
                .display()
                .to_string(),
        }
    }
}

/// Java's Files.createTempDirectory names a directory by a random unsigned long; tla-ts derives it
/// from TLC's fingerprint of what the directory holds, so that each run of a spec prints the same
/// files (`getTemporaryName`).
fn temporary_name(contents: &str) -> String {
    let units: Vec<u16> = contents.encode_utf16().collect();
    let mut fingerprint = extend_int(extend_byte(INITIAL, STRING_VALUE), units.len() as i32);
    let whole = units.len() & !3;
    for chunk in units[..whole].chunks(4) {
        let word = chunk.iter().enumerate().fold(0u32, |word, (index, unit)| {
            word | (u32::from(*unit & 0xff) << (8 * index))
        });
        fingerprint = extend_int(fingerprint, word as i32);
    }
    for unit in &units[whole..] {
        fingerprint = extend_byte(fingerprint, (*unit & 0xff) as u8);
    }
    fingerprint.to_string()
}

/// Node's `path.resolve`: absolute, with `.` and `..` resolved by name, not through links.
fn resolve(path: &Path) -> PathBuf {
    let absolute = std::env::current_dir().unwrap_or_default().join(path);
    let mut resolved = PathBuf::new();
    for component in absolute.components() {
        match component {
            Component::ParentDir => {
                resolved.pop();
            }
            Component::CurDir => {}
            other => resolved.push(other),
        }
    }
    resolved
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn names_a_directory_as_the_typescript_cli_does() {
        // getTemporaryName in src/cli/tlc.ts for the same text.
        assert_eq!(temporary_name("/a/Spec.tla"), "2110373863359387791");
        assert_eq!(
            temporary_name("/a/Spec.tla Naturals"),
            "5093068189582079104"
        );
    }
}
