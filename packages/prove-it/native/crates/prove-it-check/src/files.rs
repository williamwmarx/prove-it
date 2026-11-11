//! The paths TLC names the files SANY parses by, as `createFileDescriber` in `src/cli/tlc.ts` writes
//! them: a module's own file, the root module's file copied into a directory named for it, or a
//! standard module copied into a directory named for the spec, from the jar on the class path.

use std::path::{Component, Path, PathBuf};

use tla_front::report::ModuleOrigin;
use tla_values::fingerprint::Polynomial;

use crate::host::Files;
use crate::jar::get_standard_modules_url;

const STRING_VALUE: u8 = 3;

pub struct FileDescriber {
    spec: PathBuf,
    directories: Vec<PathBuf>,
    temporary: PathBuf,
    metadir: Option<PathBuf>,
    /// The URL TLC names the standard modules in the jar by.
    standard_modules: Option<String>,
    is_174: bool,
}

impl FileDescriber {
    /// The temporary directory is the JVM's `java.io.tmpdir` where the launch sets it.
    pub fn new(files: &Files) -> FileDescriber {
        let spec = resolve(files.spec);
        let directories = files.directories.iter().map(PathBuf::from).collect();
        let temporary = files
            .temporary
            .map_or_else(std::env::temp_dir, PathBuf::from);
        FileDescriber {
            spec,
            directories,
            temporary: std::fs::canonicalize(&temporary).unwrap_or_else(|_| resolve(&temporary)),
            metadir: files.metadir.map(|metadir| resolve(Path::new(metadir))),
            standard_modules: files
                .jar
                .map(|jar| get_standard_modules_url(&resolve(Path::new(jar)))),
            is_174: files.is_174,
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
            // ParseUnit names the file by its real path, and by the URI of the path its resolver
            // made, through the directory as given, where the two differ.
            ModuleOrigin::File => {
                let Some(found) = self
                    .directories
                    .iter()
                    .map(|directory| directory.join(&file_name))
                    .find(|path| path.exists())
                else {
                    return real(&self.spec);
                };
                let resolved = real(&found);
                let made = get_java_absolute(&found);
                if made == resolved {
                    resolved
                } else {
                    format!("{resolved} (file:{})", quote_uri_path(&made))
                }
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
            ModuleOrigin::Standard => {
                let copy = self
                    .temporary
                    .join(format!(
                        "tlc-{}",
                        temporary_name(&self.spec.display().to_string())
                    ))
                    .join(&file_name);
                match &self.standard_modules {
                    Some(url) => format!("{} ({url}{file_name})", copy.display()),
                    None => copy.display().to_string(),
                }
            }
        }
    }
}

/// Java's Files.createTempDirectory names a directory by a random unsigned long; tla-ts derives it
/// from TLC's fingerprint of what the directory holds, so that each run of a spec prints the same
/// files (`getTemporaryName`).
fn temporary_name(contents: &str) -> String {
    let units: Vec<u16> = contents.encode_utf16().collect();
    let polynomial = Polynomial::get(0);
    let mut fingerprint = polynomial.extend_int(
        polynomial.extend_byte(polynomial.value(), STRING_VALUE),
        units.len() as i32,
    );
    let whole = units.len() & !3;
    for chunk in units[..whole].chunks(4) {
        let word = chunk.iter().enumerate().fold(0u32, |word, (index, unit)| {
            word | (u32::from(*unit & 0xff) << (8 * index))
        });
        fingerprint = polynomial.extend_int(fingerprint, word as i32);
    }
    for unit in &units[whole..] {
        fingerprint = polynomial.extend_byte(fingerprint, (*unit & 0xff) as u8);
    }
    fingerprint.to_string()
}

/// Java's `File.getAbsolutePath`: against the working directory, with repeated separators and a
/// trailing one dropped, and `.` and `..` kept.
fn get_java_absolute(path: &Path) -> String {
    let text = path.to_string_lossy();
    let absolute = if path.is_absolute() {
        text.into_owned()
    } else {
        format!(
            "{}/{text}",
            std::env::current_dir().unwrap_or_default().display()
        )
    };
    let mut normalized = String::new();
    for character in absolute.chars() {
        if !(character == '/' && normalized.ends_with('/')) {
            normalized.push(character);
        }
    }
    if normalized.len() > 1 && normalized.ends_with('/') {
        normalized.pop();
    }
    normalized
}

/// A path as `java.net.URI` quotes it in `File.toURI`: each byte of a character a URI's path
/// doesn't allow as `%XX`, and characters beyond ASCII as they are.
fn quote_uri_path(path: &str) -> String {
    let mut quoted = String::new();
    for character in path.chars() {
        let is_allowed = character.is_ascii_alphanumeric()
            || "-_.!~*'()/,;:$&+=@".contains(character)
            || (!character.is_ascii() && !character.is_control() && !character.is_whitespace());
        if is_allowed {
            quoted.push(character);
        } else {
            let mut bytes = [0; 4];
            for byte in character.encode_utf8(&mut bytes).bytes() {
                quoted.push_str(&format!("%{byte:02X}"));
            }
        }
    }
    quoted
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
