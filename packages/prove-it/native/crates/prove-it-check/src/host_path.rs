//! Paths on the host's file system, by the host's rules rather than the compile target's: the
//! binary and the addon run on the host itself, but the engine as WebAssembly runs on whatever host
//! JavaScript does, where std's paths are Unix's. The rules are Node's `path` module's for the
//! platform, which the CLI's TypeScript resolver used; the paths TLC prints are built from these
//! with `/`, as that resolver built them.

/// The rules a host names its files by.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Platform {
    Unix,
    Windows,
}

impl Platform {
    /// The rules of the platform this was compiled for, where it runs on the host itself.
    pub const NATIVE: Platform = if cfg!(windows) {
        Platform::Windows
    } else {
        Platform::Unix
    };

    /// The platform Node's `process.platform` names.
    pub fn from_node(name: &str) -> Platform {
        if name == "win32" {
            Platform::Windows
        } else {
            Platform::Unix
        }
    }

    /// What separates the paths of a list, such as `-DTLA-Library` or the class path
    /// (`path.delimiter`, Java's `File.pathSeparator`).
    pub fn delimiter(self) -> char {
        match self {
            Platform::Unix => ':',
            Platform::Windows => ';',
        }
    }

    pub fn is_separator(self, character: char) -> bool {
        character == '/' || self == Platform::Windows && character == '\\'
    }

    pub fn has_separator(self, path: &str) -> bool {
        path.chars().any(|character| self.is_separator(character))
    }

    /// The byte index of the last separator in `path`.
    pub fn last_separator(self, path: &str) -> Option<usize> {
        path.rfind(|character| self.is_separator(character))
    }

    /// The last part of `path`, as Java's `File.getName` names it: after its last separator once
    /// the separators it ends with are dropped, so `a/Spec/` is `Spec`, and `a/.` is `.`.
    pub fn file_name(self, path: &str) -> &str {
        let trimmed = path.trim_end_matches(|character| self.is_separator(character));
        self.last_separator(trimmed)
            .map_or(trimmed, |end| &trimmed[end + 1..])
    }

    /// `path.isAbsolute`: on Windows, a path that starts with a separator or a drive and one, such
    /// as `\a`, `C:\a` or `\\server\share`, but not `C:a`, which is relative to the drive's
    /// directory.
    pub fn is_absolute(self, path: &str) -> bool {
        let mut characters = path.chars();
        match self {
            Platform::Unix => path.starts_with('/'),
            Platform::Windows => match (characters.next(), characters.next(), characters.next()) {
                (Some(first), _, _) if self.is_separator(first) => true,
                (Some(drive), Some(':'), Some(third)) => {
                    drive.is_ascii_alphabetic() && self.is_separator(third)
                }
                _ => false,
            },
        }
    }

    /// `directory` and then `name`, as the CLI joined them, with `/`; `name` alone where it is
    /// absolute or `directory` is empty, the working directory.
    pub fn join(self, directory: &str, name: &str) -> String {
        if directory.is_empty() || self.is_absolute(name) {
            name.to_string()
        } else if directory.ends_with(|character| self.is_separator(character)) {
            format!("{directory}{name}")
        } else {
            format!("{directory}/{name}")
        }
    }

    /// `path.resolve(current, path)`: absolute, with `.` and `..` resolved by name, not through
    /// links, and repeated separators dropped. On Windows, as Node's, with the drive of `current`
    /// for a path rooted without one and `\` between the parts.
    pub fn resolve(self, current: &str, path: &str) -> String {
        let (root, rest) = match self {
            Platform::Unix => {
                let joined = if self.is_absolute(path) {
                    path.to_string()
                } else {
                    format!("{current}/{path}")
                };
                ("/".to_string(), joined)
            }
            Platform::Windows => self.get_windows_start(current, path),
        };
        let separator = match self {
            Platform::Unix => '/',
            Platform::Windows => '\\',
        };
        let mut parts: Vec<&str> = Vec::new();
        for part in rest.split(|character| self.is_separator(character)) {
            match part {
                "" | "." => {}
                ".." => {
                    parts.pop();
                }
                _ => parts.push(part),
            }
        }
        let body = parts.join(&separator.to_string());
        format!("{root}{body}")
    }

    /// The root `path` resolves under on Windows, as `\\server\share\` or `C:\`, and the parts
    /// after it, with `current` first where `path` is relative to it.
    fn get_windows_start(self, current: &str, path: &str) -> (String, String) {
        let (current_root, current_rest) = self.split_windows_root(current);
        let (root, rest) = self.split_windows_root(path);
        let is_rooted = rest.starts_with(|character| self.is_separator(character));
        match root {
            // A UNC path or a drive with a separator after it.
            Some(root) if is_rooted || root.starts_with("\\\\") => (root, rest.to_string()),
            // `C:a`: relative to the drive's directory, which is the current one on that drive.
            Some(root)
                if current_root
                    .as_ref()
                    .is_some_and(|current| current.eq_ignore_ascii_case(&root)) =>
            {
                (
                    current_root.unwrap_or(root),
                    format!("{current_rest}\\{rest}"),
                )
            }
            Some(root) => (root, rest.to_string()),
            // `\a`: on the current drive.
            None if is_rooted => (
                current_root.unwrap_or_else(|| "\\".to_string()),
                rest.into(),
            ),
            None => (
                current_root.unwrap_or_else(|| "\\".to_string()),
                format!("{current_rest}\\{rest}"),
            ),
        }
    }

    /// A Windows path's drive, as `C:\`, or its UNC share, as `\\server\share\`, and the rest.
    fn split_windows_root(self, path: &str) -> (Option<String>, &str) {
        let bytes = path.as_bytes();
        let is_separator = |index: usize| {
            bytes
                .get(index)
                .is_some_and(|&byte| self.is_separator(char::from(byte)))
        };
        if is_separator(0) && is_separator(1) {
            let parts: Vec<&str> = path[2..]
                .splitn(3, |character| self.is_separator(character))
                .collect();
            if let [server, share, ..] = parts.as_slice()
                && !server.is_empty()
                && !share.is_empty()
            {
                let length = 2 + server.len() + 1 + share.len();
                return (
                    Some(format!("\\\\{server}\\{share}\\")),
                    path.get(length..).unwrap_or_default(),
                );
            }
        }
        match bytes {
            [drive, b':', ..] if drive.is_ascii_alphabetic() => {
                (Some(format!("{}:\\", char::from(*drive))), &path[2..])
            }
            _ => (None, path),
        }
    }
}

/// A file's name without its last extension, as std's `Path::file_stem`: `.tla` keeps its dot.
pub fn get_stem(file_name: &str) -> &str {
    match file_name.rsplit_once('.') {
        Some((stem, _)) if !stem.is_empty() => stem,
        _ => file_name,
    }
}

#[cfg(test)]
mod tests {
    use super::Platform::{Unix, Windows};
    use super::get_stem;

    #[test]
    fn names_a_file_without_its_extension_as_std_does() {
        assert_eq!(get_stem("Spec.tla"), "Spec");
        assert_eq!(get_stem("a.b.tla"), "a.b");
        assert_eq!(get_stem(".tla"), ".tla");
        assert_eq!(get_stem("Spec"), "Spec");
    }

    #[test]
    fn splits_lists_by_the_hosts_delimiter() {
        assert_eq!(Unix.delimiter(), ':');
        assert_eq!(Windows.delimiter(), ';');
        assert_eq!(
            "C:\\a;D:\\b".split(Windows.delimiter()).collect::<Vec<_>>(),
            ["C:\\a", "D:\\b"]
        );
    }

    // path.win32.isAbsolute and path.posix.isAbsolute.
    #[test]
    fn tells_absolute_paths_as_node_does() {
        for (path, unix, windows) in [
            ("/a", true, true),
            ("\\a", false, true),
            ("C:\\a", false, true),
            ("c:/a", false, true),
            ("C:a", false, false),
            ("C:", false, false),
            ("\\\\server\\share\\a", false, true),
            ("//server/share", true, true),
            ("a\\b", false, false),
            ("", false, false),
        ] {
            assert_eq!(Unix.is_absolute(path), unix, "{path}");
            assert_eq!(Windows.is_absolute(path), windows, "{path}");
        }
    }

    #[test]
    fn names_the_last_part_after_either_separator_on_windows() {
        assert_eq!(Windows.file_name("C:\\a/b\\Spec"), "Spec");
        // As Java's File.getName: the separators at the end dropped, `.` and `..` kept.
        assert_eq!(Unix.file_name("/a/Spec/"), "Spec");
        assert_eq!(Unix.file_name("/a/Spec//"), "Spec");
        assert_eq!(Unix.file_name("/a/Spec/."), ".");
        assert_eq!(Unix.file_name("/a/Spec/.."), "..");
        assert_eq!(Windows.file_name("C:\\a\\Spec\\"), "Spec");
        assert_eq!(Unix.file_name("a\\b/Spec"), "Spec");
        assert_eq!(Unix.file_name("a\\Spec"), "a\\Spec");
        assert_eq!(Windows.last_separator("a\\b"), Some(1));
        assert!(Windows.has_separator("sub\\Spec"));
        assert!(!Unix.has_separator("sub\\Spec"));
    }

    #[test]
    fn joins_with_a_slash_unless_the_name_is_absolute() {
        assert_eq!(Windows.join("C:\\lib", "M.tla"), "C:\\lib/M.tla");
        assert_eq!(Windows.join("C:\\lib\\", "M.tla"), "C:\\lib\\M.tla");
        assert_eq!(Windows.join("", "M.tla"), "M.tla");
        assert_eq!(Windows.join("C:\\w", "D:\\M.class"), "D:\\M.class");
        assert_eq!(Windows.join("C:\\w", "lib\\M.class"), "C:\\w/lib\\M.class");
        assert_eq!(Unix.join("/w", "/M.class"), "/M.class");
        assert_eq!(Unix.join("lib", "M.tla"), "lib/M.tla");
    }

    // path.win32.resolve and path.posix.resolve, with the first argument the working directory.
    #[test]
    fn resolves_as_node_does() {
        for (current, path, resolved) in [
            ("C:\\w", "a\\..\\b/./c", "C:\\w\\b\\c"),
            ("C:\\w", "D:\\x\\y", "D:\\x\\y"),
            ("C:\\w", "\\x", "C:\\x"),
            ("C:\\w", "C:x", "C:\\w\\x"),
            ("C:\\w", "D:x", "D:\\x"),
            (
                "C:\\w",
                "\\\\server\\share\\x\\..\\y",
                "\\\\server\\share\\y",
            ),
            ("\\\\server\\share\\w", "x", "\\\\server\\share\\w\\x"),
            ("C:\\w", "..\\..\\..", "C:\\"),
            ("C:\\w", "c:/x//y", "c:\\x\\y"),
        ] {
            assert_eq!(Windows.resolve(current, path), resolved, "{current} {path}");
        }
        for (current, path, resolved) in [
            ("/w", "a/../b/./c", "/w/b/c"),
            ("/w", "/x//y/", "/x/y"),
            ("/w", "../../..", "/"),
            ("/w", "a\\b", "/w/a\\b"),
        ] {
            assert_eq!(Unix.resolve(current, path), resolved, "{current} {path}");
        }
    }

    // Paths drawn from the characters that matter to the rules, a few thousand of them: what
    // holds of every path, on both platforms.
    #[test]
    fn keeps_its_rules_for_any_path() {
        let alphabet = ['a', 'B', '/', '\\', ':', '.', 'C', ' '];
        let mut state: u64 = 0x2545_f491_4f6c_dd1d;
        let mut next = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        for _ in 0..5000 {
            let length = (next() % 12) as usize;
            let path: String = (0..length)
                .map(|_| alphabet[(next() % alphabet.len() as u64) as usize])
                .collect();
            for (platform, current) in [(Unix, "/w/x"), (Windows, "C:\\w\\x")] {
                let resolved = platform.resolve(current, &path);
                assert!(
                    platform.is_absolute(&resolved),
                    "{platform:?} {path:?} {resolved:?}"
                );
                assert_eq!(platform.resolve(current, &resolved), resolved, "{path:?}");
                let (separator, rest) = match platform {
                    Unix => ('/', &resolved[1..]),
                    Windows => (
                        '\\',
                        platform
                            .split_windows_root(&resolved)
                            .1
                            .trim_start_matches('\\'),
                    ),
                };
                assert!(
                    rest.is_empty()
                        || rest
                            .split(separator)
                            .all(|part| !matches!(part, "" | "." | "..")),
                    "{platform:?} {path:?} {resolved:?}"
                );
                let name = platform.file_name(&path);
                assert!(!platform.has_separator(name), "{path:?}");
                let trimmed = path.trim_end_matches(|character| platform.is_separator(character));
                assert!(trimmed.ends_with(name), "{path:?}");
                if let Some(end) = platform.last_separator(trimmed) {
                    assert!(platform.is_separator(char::from(path.as_bytes()[end])));
                    assert_eq!(&trimmed[end + 1..], name);
                }
                assert_eq!(platform.join("d", &resolved), resolved);
                assert_eq!(platform.join("", &path), path);
                if platform == Unix {
                    assert_eq!(platform.is_absolute(&path), path.starts_with('/'));
                }
            }
        }
    }
}
