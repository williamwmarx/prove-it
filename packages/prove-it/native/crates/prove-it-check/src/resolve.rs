//! Where TLC's resolver (`SimpleFilenameToStream`) finds a spec, its configuration, its modules and
//! the Java classes that override them, and what TLC prints of a spec it doesn't find, on the
//! host's file system. The binary, the CLI's check and the CLI's TypeScript check resolve through
//! these (`resolve_files`).

use std::path::{Path, PathBuf};

use tla_front::report::ModuleOrigin;
use tla_front::{TlcVersion, get_standard_module};

use crate::args::{Java, get_java_launch};
use crate::files::FileDescriber;
use crate::host::{FileKind, Files, Host};
use crate::host_path::Platform;
use crate::jar::{get_standard_modules_url, get_tools_jar, is_174};

/// The directories TLC's resolver finds a spec's modules in, in its order, for the spec at
/// `main_file`, the path TLC was given without `.tla` (`SimpleFilenameToStream`): an absolute
/// spec's own directory, which TLC makes its user directory, then the library path; or the working
/// directory, written "", then the directory the spec was named in, or, for a spec named without
/// one, the library path.
pub fn get_module_directories(
    platform: Platform,
    main_file: &str,
    libraries: &[String],
) -> Vec<String> {
    match platform.last_separator(main_file) {
        Some(end) if platform.is_absolute(main_file) => {
            std::iter::once(main_file[..=end].to_string())
                .chain(libraries.iter().cloned())
                .collect()
        }
        Some(end) => vec![String::new(), main_file[..=end].to_string()],
        None => std::iter::once(String::new())
            .chain(libraries.iter().cloned())
            .collect(),
    }
}

/// The spec TLC checks for the path it was given: TLC also looks for a spec named without a
/// directory on the library path, by the path it makes there.
pub fn find_spec(host: &dyn Host, given: &str, libraries: &[String]) -> String {
    let platform = host.platform();
    if host.is_file(Path::new(given)) || platform.has_separator(given) {
        return given.to_string();
    }
    libraries
        .iter()
        .map(|directory| platform.join(directory, given))
        .find(|candidate| host.is_file(Path::new(candidate)))
        .unwrap_or_else(|| given.to_string())
}

/// Where TLC finds the configuration: the file, or the name TLC says it didn't find, or why the
/// binary doesn't read what TLC does.
pub enum Config {
    Found(PathBuf),
    Missing(String),
    NotNative(&'static str),
}

/// TLC names the configuration by -config without one `.cfg` (`TLC.handleParameters`), or by the
/// spec's name, reads one named `.tla` from that module's CONFIG section and adds `.cfg` to any
/// other (`MonolithSpecExtractor.getConfig`), then finds it as it finds a module (`ModelConfig`),
/// among the standard modules in its jar too.
pub fn find_config(
    host: &dyn Host,
    config: Option<&str>,
    main_file: &str,
    directories: &[String],
    version: TlcVersion,
) -> Config {
    let platform = host.platform();
    let name = match config {
        Some(path) => {
            let base = path.strip_suffix(".cfg").unwrap_or(path);
            if base.ends_with(".tla") {
                base.to_string()
            } else {
                format!("{base}.cfg")
            }
        }
        // TLC takes an absolute spec's directory for its user directory and the spec by its name.
        None if platform.is_absolute(main_file) => {
            format!("{}.cfg", platform.file_name(main_file))
        }
        None => format!("{main_file}.cfg"),
    };
    let found = directories
        .iter()
        .map(|directory| PathBuf::from(platform.join(directory, &name)))
        .find(|path| host.is_file(path));
    if let Some(module) = name.strip_suffix(".tla")
        && (found.is_some()
            || !platform.has_separator(module) && get_standard_module(module, version).is_some())
    {
        return Config::NotNative(
            "a configuration in a module's CONFIG section, which TLC reads from a -config ending in .tla",
        );
    }
    found.map_or(Config::Missing(name), Config::Found)
}

/// A module's text from the first of the directories that has its file, or that file where TLC
/// can't read it, as a directory (`FileUtil.toIStream`).
pub fn load_module(
    host: &dyn Host,
    directories: &[&Path],
    name: &str,
) -> Result<Option<String>, PathBuf> {
    let Some(path) = find_file(host, directories, &format!("{name}.tla")) else {
        return Ok(None);
    };
    match host.kind(&path) {
        FileKind::File => host.read_text(&path).map(Some).ok_or(path),
        _ => Err(path),
    }
}

/// The Java class that overrides a module, from the first of the directories that has its file, by
/// that file's absolute path; none where TLC can't read it, as `TLCClass.loadClass` loads none.
pub fn load_class(
    host: &dyn Host,
    directories: &[&Path],
    name: &str,
) -> Option<(PathBuf, Vec<u8>)> {
    let path = find_file(host, directories, &format!("{name}.class"))?;
    if host.kind(&path) != FileKind::File {
        return None;
    }
    let bytes = host.read_bytes(&path)?;
    let current = host.current_dir();
    Some((
        PathBuf::from(
            host.platform()
                .join(&current.to_string_lossy(), &path.to_string_lossy()),
        ),
        bytes,
    ))
}

fn find_file(host: &dyn Host, directories: &[&Path], file_name: &str) -> Option<PathBuf> {
    let platform = host.platform();
    directories
        .iter()
        .map(|directory| PathBuf::from(platform.join(&directory.to_string_lossy(), file_name)))
        .find(|path| host.is_file(path))
}

/// What TLC prints of a spec it doesn't find, as SANY's resolver says where it looked
/// (`FileUtil.createNamedInputStream`), for the path it was given.
pub fn get_missing_spec_message(host: &dyn Host, given: &str, libraries: &[String]) -> String {
    let platform = host.platform();
    let current = host.current_dir();
    let main_file = given.strip_suffix(".tla").unwrap_or(given);
    let (directory, file_name) = if platform.is_absolute(given) {
        let normalized = get_java_path(given);
        let end = platform.last_separator(&normalized).unwrap_or_default();
        (
            if end == 0 {
                &normalized[..1]
            } else {
                &normalized[..end]
            }
            .to_string(),
            format!("{}.tla", platform.file_name(main_file)),
        )
    } else {
        (
            current.display().to_string(),
            format!("./{}.tla", collapse_separators(main_file)),
        )
    };
    // SimpleFilenameToStream looks for a relative spec named with a directory there alone, which it
    // names as Java's Path does.
    let directories: Vec<String> = match platform.last_separator(given) {
        Some(end) if !platform.is_absolute(given) => vec![get_java_path(&given[..end])],
        _ => libraries
            .iter()
            .map(|library| get_java_path(library))
            .collect(),
    };
    format!(
        "File does not exist: {directory}/{file_name} while looking in these directories: {directory}, {}, classpath:/tla2sany/StandardModules, classpath:/",
        directories.join(", ")
    )
}

/// What TLC 1.7.4 prints of a module file it doesn't find, `file_name`, as its resolver says the
/// last file it looked for and the directories it looked in, the jar's standard modules last.
pub fn get_missing_file_message_174(
    host: &dyn Host,
    spec: &str,
    file_name: &str,
    libraries: &[String],
    jar: Option<&str>,
) -> String {
    let platform = host.platform();
    let current = host.current_dir();
    let spec_directory = &spec[..platform.last_separator(spec).map_or(0, |end| end + 1)];
    let is_spec_absolute = platform.is_absolute(spec);
    let directories: Vec<String> = if !is_spec_absolute && !spec_directory.is_empty() {
        vec![spec_directory.to_string()]
    } else {
        libraries
            .iter()
            .map(|directory| {
                if directory.ends_with(|character| platform.is_separator(character)) {
                    directory.clone()
                } else {
                    format!("{directory}/")
                }
            })
            .collect()
    };
    let last = directories.last().map_or_else(
        || {
            if is_spec_absolute {
                spec_directory.to_string()
            } else {
                String::new()
            }
        },
        Clone::clone,
    );
    let path = format!("{last}{file_name}");
    let path = if platform.is_absolute(&path) {
        path
    } else {
        format!("{}/{path}", current.display())
    };
    let looked: Vec<String> = directories
        .into_iter()
        .chain(jar.map(|jar| {
            get_standard_modules_url(Path::new(
                &platform.resolve(&current.to_string_lossy(), jar),
            ))
        }))
        .collect();
    format!(
        "File does not exist: {path} while looking in these directories: {}",
        looked.join(", ")
    )
}

/// What the CLI's TypeScript check asks of where TLC finds the files of the spec it was `given` on
/// the command line `args` (`resolveFiles` in `prove-it-host`).
pub enum Resolved {
    /// The spec TLC checks, the name SANY gives it, the directories TLC finds its modules in, its
    /// configuration, a file TLC finds there but can't read, and what TLC prints where it doesn't
    /// find the spec.
    Spec {
        path: String,
        name: String,
        directories: Vec<String>,
        config: Config,
        unreadable: Option<PathBuf>,
        missing: Option<String>,
    },
    Module(Result<Option<String>, PathBuf>),
    Class(Option<(PathBuf, Vec<u8>)>),
    /// The path TLC prints for the file SANY parses a module from, or what TLC 1.7.4 prints of a
    /// module it doesn't find.
    Text(String),
    NotNative(String),
}

/// Resolves `request` for the spec `given`, with `.tla`: `spec`, `module:<name>`, `class:<name>`,
/// `file:<origin>:<name>` (`file`, `root file` or `standard`), or `missing:<file name>`, what TLC
/// 1.7.4 prints of a module file it doesn't find. `args` is the Java launch, if any, then only the
/// options that name files, `-config` and `-metadir` each with its value, as the TypeScript check
/// parsed them: it takes options the binary's parser declines.
pub fn resolve_files(args: &[String], given: &str, request: &str, host: &dyn Host) -> Resolved {
    let platform = host.platform();
    let (args, java) = match get_java_launch(args, platform) {
        Some(launch) => (launch.args, launch.java),
        None => (args.to_vec(), Java::default()),
    };
    let jar = java
        .class_path
        .as_deref()
        .and_then(|class_path| get_tools_jar(class_path, platform));
    let version = match (java.tlc_version, jar) {
        (Some(version), _) => version,
        (None, Some(jar)) => match is_174(host, jar) {
            Ok(true) => TlcVersion::V1_7_4,
            Ok(false) => TlcVersion::Master,
            Err(reason) => return Resolved::NotNative(format!("the version of {jar}: {reason}")),
        },
        (None, None) => TlcVersion::Master,
    };
    let get_option = |name: &str| {
        args.chunks(2)
            .find(|option| option[0] == name)
            .and_then(|option| option.get(1))
            .map(String::as_str)
    };
    let main_file = given.strip_suffix(".tla").unwrap_or(given);
    let directories = get_module_directories(platform, main_file, &java.libraries);
    let spec = find_spec(host, given, &java.libraries);
    let paths: Vec<&Path> = directories.iter().map(Path::new).collect();
    if request == "spec" {
        let config = find_config(
            host,
            get_option("-config"),
            main_file,
            &directories,
            version,
        );
        let stem = platform.file_name(main_file).to_string();
        let unreadable = match &config {
            Config::Found(path) => Some(path.clone()),
            _ => None,
        }
        .into_iter()
        .chain([PathBuf::from(&spec)])
        .find(|path| host.kind(path) == FileKind::Directory);
        let missing = (!host.is_file(Path::new(&spec))
            && get_standard_module(&stem, version).is_none())
        .then(|| match version {
            TlcVersion::Master => get_missing_spec_message(host, given, &java.libraries),
            TlcVersion::V1_7_4 => get_missing_file_message_174(
                host,
                &spec,
                &format!("{stem}.tla"),
                &java.libraries,
                jar,
            ),
        });
        return Resolved::Spec {
            name: if platform.is_absolute(main_file) {
                stem
            } else {
                main_file.to_string()
            },
            path: spec,
            directories,
            config,
            unreadable,
            missing,
        };
    }
    if let Some(name) = request.strip_prefix("module:") {
        return Resolved::Module(load_module(host, &paths, name));
    }
    if let Some(name) = request.strip_prefix("class:") {
        return Resolved::Class(load_class(host, &paths, name));
    }
    if let Some(file_name) = request.strip_prefix("missing:") {
        return Resolved::Text(get_missing_file_message_174(
            host,
            &spec,
            file_name,
            &java.libraries,
            jar,
        ));
    }
    let Some((origin, name)) = request
        .strip_prefix("file:")
        .and_then(|rest| rest.split_once(':'))
    else {
        return Resolved::NotNative(format!("the request {request}"));
    };
    let origin = match origin {
        "file" => ModuleOrigin::File,
        "root file" => ModuleOrigin::RootFile,
        _ => ModuleOrigin::Standard,
    };
    let files = Files {
        spec: Path::new(&spec),
        main_file,
        directories: &directories,
        temporary: java.temporary_directory.as_deref(),
        metadir: get_option("-metadir"),
        jar,
        is_174: version == TlcVersion::V1_7_4,
        root_extendees: &[],
    };
    Resolved::Text(FileDescriber::new(&files, host).describe(name, origin))
}

/// A path as Java's `Path` names it: without repeated separators, or one that ends it.
fn get_java_path(path: &str) -> String {
    let collapsed = collapse_separators(path);
    if collapsed.len() > 1 {
        collapsed.trim_end_matches('/').to_string()
    } else {
        collapsed
    }
}

fn collapse_separators(path: &str) -> String {
    let mut collapsed = String::new();
    for character in path.chars() {
        if !(character == '/' && collapsed.ends_with('/')) {
            collapsed.push(character);
        }
    }
    collapsed
}

/// Java's `File.getAbsolutePath`, as the CLI wrote it: against the working directory, with
/// repeated `/` and a trailing one dropped, and `.` and `..` kept.
pub fn get_java_absolute(platform: Platform, current: &str, path: &str) -> String {
    let absolute = if platform.is_absolute(path) {
        path.to_string()
    } else {
        format!("{current}/{path}")
    };
    let mut normalized = collapse_separators(&absolute);
    if normalized.len() > 1 && normalized.ends_with('/') {
        normalized.pop();
    }
    normalized
}

#[cfg(test)]
mod tests {
    use std::time::SystemTime;

    use super::*;
    use crate::host::{FileDescription, Machine, SystemHost};
    use crate::zone::Zone;

    /// A Windows host, whose files are at the paths given, the working directory `C:\work`.
    struct WindowsHost {
        system: SystemHost,
        files: Vec<(&'static str, &'static str)>,
    }

    impl WindowsHost {
        fn new(files: &[(&'static str, &'static str)]) -> Self {
            WindowsHost {
                system: SystemHost::new(None),
                files: files.to_vec(),
            }
        }

        fn key(path: &Path) -> String {
            Platform::Windows
                .resolve("C:\\work", &path.to_string_lossy())
                .to_lowercase()
        }

        fn find(&self, path: &Path) -> Option<&'static str> {
            let key = Self::key(path);
            self.files
                .iter()
                .find(|(file, _)| Self::key(Path::new(file)) == key)
                .map(|(_, text)| *text)
        }
    }

    impl Host for WindowsHost {
        fn platform(&self) -> Platform {
            Platform::Windows
        }

        fn kind(&self, path: &Path) -> FileKind {
            let key = Self::key(path);
            if self.find(path).is_some() {
                FileKind::File
            } else if self
                .files
                .iter()
                .any(|(file, _)| Self::key(Path::new(file)).starts_with(&format!("{key}\\")))
            {
                FileKind::Directory
            } else {
                FileKind::Absent
            }
        }

        fn real_path(&self, path: &Path) -> Option<PathBuf> {
            (self.kind(path) != FileKind::Absent).then(|| {
                PathBuf::from(Platform::Windows.resolve("C:\\work", &path.to_string_lossy()))
            })
        }

        fn current_dir(&self) -> PathBuf {
            PathBuf::from("C:\\work")
        }

        fn temp_dir(&self) -> PathBuf {
            PathBuf::from("C:\\Temp")
        }

        fn read_text(&self, path: &Path) -> Option<String> {
            self.find(path).map(String::from)
        }

        fn read_bytes(&self, path: &Path) -> Option<Vec<u8>> {
            self.find(path).map(|text| text.as_bytes().to_vec())
        }

        fn load_module(
            &self,
            directories: &[&Path],
            name: &str,
        ) -> Result<Option<String>, PathBuf> {
            load_module(self, directories, name)
        }

        fn load_class(&self, directories: &[&Path], name: &str) -> Option<(PathBuf, Vec<u8>)> {
            load_class(self, directories, name)
        }

        fn get_file_describer<'h>(&'h self, files: &Files) -> FileDescription<'h> {
            let describer = FileDescriber::new(files, self);
            Box::new(move |name, origin| describer.describe(name, origin))
        }

        fn get_variable(&self, _name: &str) -> Option<String> {
            None
        }

        fn now(&self) -> SystemTime {
            self.system.now()
        }

        fn zone(&self) -> &Zone {
            self.system.zone()
        }

        fn machine(&self) -> &Machine {
            self.system.machine()
        }
    }

    fn strings(args: &[&str]) -> Vec<String> {
        args.iter().map(|&arg| arg.to_string()).collect()
    }

    fn get_spec(host: &WindowsHost, args: &[&str], given: &str) -> (String, Vec<String>, Config) {
        match resolve_files(&strings(args), given, "spec", host) {
            Resolved::Spec {
                path,
                directories,
                config,
                ..
            } => (path, directories, config),
            _ => panic!("no spec"),
        }
    }

    fn get_module(host: &WindowsHost, args: &[&str], given: &str, name: &str) -> Option<String> {
        match resolve_files(&strings(args), given, &format!("module:{name}"), host) {
            Resolved::Module(Ok(text)) => text,
            _ => panic!("no module"),
        }
    }

    // SimpleFilenameToStream's directories, by Node's rules for a Windows path, as the CLI's
    // TypeScript resolver found them.
    #[test]
    fn finds_the_directories_of_a_windows_spec() {
        let libraries = strings(&["D:\\lib"]);
        for (main_file, directories) in [
            ("C:\\specs\\Spec", vec!["C:\\specs\\", "D:\\lib"]),
            ("c:/specs/Spec", vec!["c:/specs/", "D:\\lib"]),
            (
                "\\\\server\\share\\Spec",
                vec!["\\\\server\\share\\", "D:\\lib"],
            ),
            ("\\specs\\Spec", vec!["\\specs\\", "D:\\lib"]),
            ("sub/inner\\Spec", vec!["", "sub/inner\\"]),
            ("sub\\Spec", vec!["", "sub\\"]),
            // Relative to drive C's directory, and named without a separator.
            ("C:Spec", vec!["", "D:\\lib"]),
            ("Spec", vec!["", "D:\\lib"]),
        ] {
            assert_eq!(
                get_module_directories(Platform::Windows, main_file, &libraries),
                directories,
                "{main_file}"
            );
        }
        // On Unix a backslash is part of a name.
        assert_eq!(
            get_module_directories(Platform::Unix, "sub\\Spec", &libraries),
            ["", "D:\\lib"]
        );
    }

    #[test]
    fn finds_modules_on_a_windows_library_path() {
        let host = WindowsHost::new(&[
            ("C:\\specs\\Spec.tla", "spec"),
            ("C:\\specs\\Spec.cfg", ""),
            ("D:\\more\\M.tla", "more"),
            ("\\\\server\\share\\N.tla", "shared"),
            ("C:\\work\\sub\\L.tla", "local"),
        ]);
        let launch = [
            "-DTLA-Library=C:\\lib;D:\\more;\\\\server\\share",
            "tlc2.TLC",
        ];
        let (path, directories, config) = get_spec(&host, &launch, "C:\\specs\\Spec.tla");
        assert_eq!(path, "C:\\specs\\Spec.tla");
        assert_eq!(
            directories,
            ["C:\\specs\\", "C:\\lib", "D:\\more", "\\\\server\\share"]
        );
        assert!(
            matches!(config, Config::Found(found) if found == Path::new("C:\\specs\\Spec.cfg"))
        );
        let module = |name| get_module(&host, &launch, "C:\\specs\\Spec.tla", name);
        assert_eq!(module("M").as_deref(), Some("more"));
        assert_eq!(module("N").as_deref(), Some("shared"));
        assert_eq!(module("L"), None);
        // A spec named relative to the working directory finds its modules beside it.
        assert_eq!(
            get_module(&host, &["tlc2.TLC"], "sub\\Spec", "L").as_deref(),
            Some("local")
        );
    }

    #[test]
    fn finds_a_spec_and_its_config_on_a_windows_library_path() {
        let host = WindowsHost::new(&[("D:\\lib\\Spec.tla", "spec"), ("C:\\work\\Other.cfg", "")]);
        let launch = ["-DTLA-Library=D:\\lib", "tlc2.TLC", "-config", "Other"];
        let (path, _, config) = get_spec(&host, &launch, "Spec.tla");
        assert_eq!(path, "D:\\lib/Spec.tla");
        assert!(matches!(config, Config::Found(found) if found == Path::new("Other.cfg")));
        // A spec named with a directory is looked for there alone.
        let (path, _, config) = get_spec(&host, &["tlc2.TLC"], "sub\\Spec.tla");
        assert_eq!(path, "sub\\Spec.tla");
        assert!(matches!(config, Config::Missing(name) if name == "sub\\Spec.cfg"));
    }

    #[test]
    fn says_where_it_looked_for_a_missing_windows_spec() {
        let host = WindowsHost::new(&[]);
        assert_eq!(
            get_missing_spec_message(&host, "C:\\specs\\Nope.tla", &strings(&["D:\\lib"])),
            "File does not exist: C:\\specs/Nope.tla while looking in these directories: C:\\specs, D:\\lib, classpath:/tla2sany/StandardModules, classpath:/"
        );
        assert_eq!(
            get_missing_spec_message(&host, "sub\\Nope", &[]),
            "File does not exist: C:\\work/./sub\\Nope.tla while looking in these directories: C:\\work, sub, classpath:/tla2sany/StandardModules, classpath:/"
        );
    }

    #[test]
    fn loads_a_windows_override_by_its_absolute_path() {
        let host = WindowsHost::new(&[("C:\\work\\lib\\M.class", "class"), ("D:\\M.class", "d")]);
        let (path, bytes) =
            load_class(&host, &[Path::new("lib\\")], "M").expect("the class beside the spec");
        assert_eq!(path, Path::new("C:\\work/lib\\M.class"));
        assert_eq!(bytes, b"class");
        let (path, _) = load_class(&host, &[Path::new("D:\\")], "M").expect("the class on D:");
        assert_eq!(path, Path::new("D:\\M.class"));
    }
}
