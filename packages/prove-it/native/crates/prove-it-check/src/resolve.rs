//! Where TLC's resolver (`SimpleFilenameToStream`) finds a spec, its configuration, its modules and
//! the Java classes that override them, and what TLC prints of a spec it doesn't find, on the
//! host's file system. The binary, the CLI's check and the CLI's TypeScript check resolve through
//! these (`resolve_files`).

use std::path::{Component, Path, PathBuf};

use tla_front::report::ModuleOrigin;
use tla_front::{TlcVersion, get_standard_module};

use crate::args::{Java, get_java_launch};
use crate::files::FileDescriber;
use crate::host::{FileKind, Files, Host};
use crate::jar::{get_standard_modules_url, get_tools_jar, is_174};

/// The directories TLC's resolver finds a spec's modules in, in its order, for the spec at
/// `main_file`, the path TLC was given without `.tla` (`SimpleFilenameToStream`): an absolute
/// spec's own directory, which TLC makes its user directory, then the library path; or the working
/// directory, written "", then the directory the spec was named in, or, for a spec named without
/// one, the library path.
pub fn get_module_directories(main_file: &str, libraries: &[String]) -> Vec<String> {
    match main_file.rfind('/') {
        Some(end) if is_absolute(Path::new(main_file)) => {
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
    if host.is_file(Path::new(given)) || given.contains('/') {
        return given.to_string();
    }
    libraries
        .iter()
        .map(|directory| Path::new(directory).join(given))
        .find(|candidate| host.is_file(candidate))
        .map_or_else(
            || given.to_string(),
            |candidate| candidate.to_string_lossy().into_owned(),
        )
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
        None if is_absolute(Path::new(main_file)) => format!("{}.cfg", get_file_name(main_file)),
        None => format!("{main_file}.cfg"),
    };
    let found = directories
        .iter()
        .map(|directory| Path::new(directory).join(&name))
        .find(|path| host.is_file(path));
    if let Some(module) = name.strip_suffix(".tla")
        && (found.is_some()
            || !module.contains('/') && get_standard_module(module, version).is_some())
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
    Some((host.current_dir().join(path), bytes))
}

fn find_file(host: &dyn Host, directories: &[&Path], file_name: &str) -> Option<PathBuf> {
    directories
        .iter()
        .map(|directory| directory.join(file_name))
        .find(|path| host.is_file(path))
}

/// What TLC prints of a spec it doesn't find, as SANY's resolver says where it looked
/// (`FileUtil.createNamedInputStream`), for the path it was given.
pub fn get_missing_spec_message(host: &dyn Host, given: &str, libraries: &[String]) -> String {
    let current = host.current_dir();
    let main_file = given.strip_suffix(".tla").unwrap_or(given);
    let (directory, file_name) = if is_absolute(Path::new(given)) {
        let end = given.rfind('/').unwrap_or_default();
        (
            if end == 0 { "/" } else { &given[..end] }.to_string(),
            format!("{}.tla", get_file_name(main_file)),
        )
    } else {
        (
            current.display().to_string(),
            format!("./{}.tla", collapse_separators(main_file)),
        )
    };
    // SimpleFilenameToStream looks for a relative spec named with a directory there alone, which it
    // names as Java's Path does.
    let directories = match given.rfind('/') {
        Some(end) if !is_absolute(Path::new(given)) => {
            let named = collapse_separators(&given[..end]);
            vec![if named.len() > 1 {
                named.trim_end_matches('/').to_string()
            } else {
                named
            }]
        }
        _ => libraries.to_vec(),
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
    let current = host.current_dir();
    let spec_directory = &spec[..spec.rfind('/').map_or(0, |end| end + 1)];
    let is_spec_absolute = is_absolute(Path::new(spec));
    let directories: Vec<String> = if !is_spec_absolute && !spec_directory.is_empty() {
        vec![spec_directory.to_string()]
    } else {
        libraries
            .iter()
            .map(|directory| {
                if directory.ends_with('/') {
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
    let path = if is_absolute(Path::new(&path)) {
        path
    } else {
        format!("{}/{path}", current.display())
    };
    let looked: Vec<String> = directories
        .into_iter()
        .chain(jar.map(|jar| get_standard_modules_url(&resolve(&current, Path::new(jar)))))
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
    let (args, java) = match get_java_launch(args) {
        Some(launch) => (launch.args, launch.java),
        None => (args.to_vec(), Java::default()),
    };
    let jar = java.class_path.as_deref().and_then(get_tools_jar);
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
    let directories = get_module_directories(main_file, &java.libraries);
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
        let stem = get_file_name(main_file);
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
            name: if is_absolute(Path::new(main_file)) {
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

fn get_file_name(path: &str) -> String {
    Path::new(path).file_name().map_or_else(
        || path.to_string(),
        |name| name.to_string_lossy().into_owned(),
    )
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

/// Whether a path is absolute, which std's `Path::is_absolute` says of no path on
/// wasm32-unknown-unknown, where the paths JavaScript names are Unix's.
pub fn is_absolute(path: &Path) -> bool {
    path.is_absolute() || cfg!(target_arch = "wasm32") && path.has_root()
}

/// Java's `File.getAbsolutePath`: against the working directory, with repeated separators and a
/// trailing one dropped, and `.` and `..` kept.
pub fn get_java_absolute(current: &Path, path: &Path) -> String {
    let text = path.to_string_lossy();
    let absolute = if is_absolute(path) {
        text.into_owned()
    } else {
        format!("{}/{text}", current.display())
    };
    let mut normalized = collapse_separators(&absolute);
    if normalized.len() > 1 && normalized.ends_with('/') {
        normalized.pop();
    }
    normalized
}

/// Node's `path.resolve`: absolute, with `.` and `..` resolved by name, not through links.
pub fn resolve(current: &Path, path: &Path) -> PathBuf {
    let mut resolved = PathBuf::new();
    for component in current.join(path).components() {
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
