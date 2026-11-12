//! The files tlapm's command line writes, held back until the run is known not to decline: each
//! operation goes into a journal, which the host applies in order once the run ends, and into an
//! overlay, through which the run reads back what it made, wrote, moved or removed. What the
//! overlay doesn't hold, the run reads from the host, as the files were when it started.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use crate::host::{Entry, FileKind, Host};

/// An operation on the files, as the host applies it: `MakeDirectory` makes a directory and those
/// above it that are missing, `Remove` removes a file or a directory with what it holds, and
/// `Copy` copies a file with the time it was last modified.
#[derive(Clone, Debug, PartialEq)]
pub enum FileOperation {
    MakeDirectory(PathBuf),
    Write(PathBuf, Vec<u8>),
    Remove(PathBuf),
    Rename(PathBuf, PathBuf),
    Copy(PathBuf, PathBuf),
}

impl FileOperation {
    /// Why the run declines where the host can't apply the operation. `src/cli/tlapm.ts` gives the
    /// same reasons.
    pub fn get_failure(&self) -> String {
        match self {
            FileOperation::MakeDirectory(path) => {
                format!("a directory tlapm can't make: {}", path.display())
            }
            FileOperation::Write(path, _) | FileOperation::Rename(_, path) => {
                format!("a file tlapm can't write: {}", path.display())
            }
            FileOperation::Remove(path) => format!("a file tlapm can't remove: {}", path.display()),
            FileOperation::Copy(path, _) => {
                format!(
                    "a file tlapm can't copy into its history: {}",
                    path.display()
                )
            }
        }
    }
}

/// What the run has made of a path.
#[derive(Clone, Debug, PartialEq)]
enum Node {
    Removed,
    /// A file, with its bytes, or the file it is a copy of.
    File(Contents),
    /// A directory, `is_new` where it wasn't there before, so that nothing the host held under it
    /// is.
    Directory {
        is_new: bool,
    },
}

#[derive(Clone, Debug, PartialEq)]
enum Contents {
    Bytes(Vec<u8>),
    CopyOf(PathBuf),
}

#[derive(Default)]
pub struct Overlay {
    nodes: RefCell<BTreeMap<PathBuf, Node>>,
    journal: RefCell<Vec<FileOperation>>,
}

/// What the overlay says of a path: what it holds, that nothing is there, or that the host knows.
enum Found {
    Node(Node),
    Missing,
    Underlying,
}

impl Overlay {
    fn find(&self, path: &Path) -> Found {
        let nodes = self.nodes.borrow();
        if let Some(node) = nodes.get(path) {
            return match node {
                Node::Removed => Found::Missing,
                node => Found::Node(node.clone()),
            };
        }
        for ancestor in path.ancestors().skip(1) {
            match nodes.get(ancestor) {
                None => {}
                Some(Node::Directory { is_new: false }) => return Found::Underlying,
                Some(_) => return Found::Missing,
            }
        }
        Found::Underlying
    }

    pub fn get_kind(&self, path: &Path, host: &dyn Host) -> FileKind {
        match self.find(path) {
            Found::Node(Node::File(_)) => FileKind::File,
            Found::Node(_) => FileKind::Directory,
            Found::Missing => FileKind::Absent,
            Found::Underlying => host.kind(path),
        }
    }

    pub fn read(&self, path: &Path, host: &dyn Host) -> Option<Vec<u8>> {
        match self.find(path) {
            Found::Node(Node::File(Contents::Bytes(bytes))) => Some(bytes),
            Found::Node(Node::File(Contents::CopyOf(from))) => self.read(&from, host),
            Found::Node(_) | Found::Missing => None,
            Found::Underlying => host.read_bytes(path),
        }
    }

    /// The entries of a directory, those the run made last modified `now`.
    pub fn list(&self, path: &Path, now: f64, host: &dyn Host) -> Option<Vec<Entry>> {
        let mut entries = match self.find(path) {
            Found::Node(Node::Directory { is_new: true }) => Vec::new(),
            Found::Node(Node::Directory { is_new: false }) | Found::Underlying => {
                if host.kind(path) != FileKind::Directory {
                    return None;
                }
                host.list_directory(path)?
            }
            Found::Node(_) | Found::Missing => return None,
        };
        let nodes = self.nodes.borrow();
        entries.retain(|entry| !matches!(nodes.get(&path.join(&entry.name)), Some(Node::Removed)));
        for (child, node) in nodes.iter() {
            if child.parent() != Some(path) || *node == Node::Removed {
                continue;
            }
            let name = child
                .file_name()
                .map_or_else(String::new, |name| name.to_string_lossy().into_owned());
            entries.retain(|entry| entry.name != name);
            entries.push(Entry {
                name,
                modified: now,
            });
        }
        Some(entries)
    }

    /// Holds that nothing is at the path, where the run knows it from a directory's entries.
    pub fn set_missing(&self, path: &Path) {
        if matches!(self.find(path), Found::Underlying) {
            self.nodes
                .borrow_mut()
                .insert(path.to_path_buf(), Node::Removed);
        }
    }

    fn record(&self, operation: FileOperation) {
        self.journal.borrow_mut().push(operation);
    }

    /// Makes the directory, as `mkdir -p` where `is_recursive` and as `Unix.mkdir` otherwise;
    /// whether it could.
    pub fn create_directory(&self, path: &Path, is_recursive: bool, host: &dyn Host) -> bool {
        let mut missing = Vec::new();
        for ancestor in path.ancestors() {
            if ancestor.as_os_str().is_empty() {
                break;
            }
            match self.get_kind(ancestor, host) {
                FileKind::Directory if ancestor == path => return is_recursive,
                FileKind::Directory => break,
                FileKind::File | FileKind::Other => return false,
                FileKind::Absent if !is_recursive && !missing.is_empty() => return false,
                FileKind::Absent => missing.push(ancestor.to_path_buf()),
            }
        }
        let mut nodes = self.nodes.borrow_mut();
        for directory in missing {
            nodes.insert(directory, Node::Directory { is_new: true });
        }
        self.record(FileOperation::MakeDirectory(path.to_path_buf()));
        true
    }

    fn is_in_directory(&self, path: &Path, host: &dyn Host) -> bool {
        path.parent().is_none_or(|parent| {
            parent.as_os_str().is_empty() || self.get_kind(parent, host) == FileKind::Directory
        })
    }

    pub fn write(&self, path: &Path, bytes: Vec<u8>, host: &dyn Host) -> bool {
        if !self.is_in_directory(path, host) || self.get_kind(path, host) == FileKind::Directory {
            return false;
        }
        self.nodes.borrow_mut().insert(
            path.to_path_buf(),
            Node::File(Contents::Bytes(bytes.clone())),
        );
        self.record(FileOperation::Write(path.to_path_buf(), bytes));
        true
    }

    /// Removes what the path names, a directory with what it holds, as `rm -rf` does.
    pub fn remove(&self, path: &Path, host: &dyn Host) {
        if self.get_kind(path, host) == FileKind::Absent {
            return;
        }
        let mut nodes = self.nodes.borrow_mut();
        nodes.retain(|known, _| !known.starts_with(path));
        nodes.insert(path.to_path_buf(), Node::Removed);
        self.record(FileOperation::Remove(path.to_path_buf()));
    }

    pub fn rename(&self, from: &Path, to: &Path, host: &dyn Host) -> bool {
        if self.get_kind(from, host) != FileKind::File
            || !self.is_in_directory(to, host)
            || self.get_kind(to, host) == FileKind::Directory
        {
            return false;
        }
        let contents = match self.find(from) {
            Found::Node(Node::File(contents)) => contents,
            _ => Contents::CopyOf(from.to_path_buf()),
        };
        let mut nodes = self.nodes.borrow_mut();
        nodes.insert(from.to_path_buf(), Node::Removed);
        nodes.insert(to.to_path_buf(), Node::File(contents));
        self.record(FileOperation::Rename(from.to_path_buf(), to.to_path_buf()));
        true
    }

    pub fn copy(&self, from: &Path, to: &Path, host: &dyn Host) -> bool {
        if self.get_kind(from, host) != FileKind::File
            || !self.is_in_directory(to, host)
            || self.get_kind(to, host) == FileKind::Directory
        {
            return false;
        }
        let contents = match self.find(from) {
            Found::Node(Node::File(contents)) => contents,
            _ => Contents::CopyOf(from.to_path_buf()),
        };
        self.nodes
            .borrow_mut()
            .insert(to.to_path_buf(), Node::File(contents));
        self.record(FileOperation::Copy(from.to_path_buf(), to.to_path_buf()));
        true
    }

    /// The operations, in the order the run made them.
    pub fn into_journal(self) -> Vec<FileOperation> {
        self.journal.into_inner()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::host::{FileDescription, Files, Machine};
    use crate::zone::Zone;
    use std::time::SystemTime;

    struct Disk;

    impl Host for Disk {
        fn read_text(&self, _path: &Path) -> Option<String> {
            None
        }
        fn read_bytes(&self, path: &Path) -> Option<Vec<u8>> {
            (path == Path::new("Spec.tla")).then(|| b"spec".to_vec())
        }
        fn load_module(&self, _: &[&Path], _: &str) -> Result<Option<String>, PathBuf> {
            Ok(None)
        }
        fn load_class(&self, _: &[&Path], _: &str) -> Option<(PathBuf, Vec<u8>)> {
            None
        }
        fn get_file_describer<'h>(&'h self, _: &Files) -> FileDescription<'h> {
            Box::new(|_, _| Ok(String::new()))
        }
        fn get_variable(&self, _: &str) -> Option<String> {
            None
        }
        fn now(&self) -> SystemTime {
            SystemTime::UNIX_EPOCH
        }
        fn zone(&self) -> &Zone {
            unreachable!("the overlay reads no zone")
        }
        fn machine(&self) -> &Machine {
            unreachable!("the overlay reads no machine")
        }
        fn kind(&self, path: &Path) -> FileKind {
            match path.to_str() {
                Some("cache" | "cache/old") => FileKind::Directory,
                Some("cache/old/fingerprints" | "Spec.tla") => FileKind::File,
                _ => FileKind::Absent,
            }
        }
        fn real_path(&self, path: &Path) -> Option<PathBuf> {
            Some(path.to_path_buf())
        }
        fn current_dir(&self) -> PathBuf {
            PathBuf::new()
        }
        fn temp_dir(&self) -> PathBuf {
            PathBuf::new()
        }
        fn list_directory(&self, path: &Path) -> Option<Vec<Entry>> {
            let entry = |name: &str| Entry {
                name: name.to_owned(),
                modified: 1.0,
            };
            match path.to_str()? {
                "cache" => Some(vec![entry("old")]),
                "cache/old" => Some(vec![entry("fingerprints")]),
                _ => None,
            }
        }
    }

    fn names(entries: Option<Vec<Entry>>) -> Vec<String> {
        let mut names: Vec<String> = entries
            .expect("a directory")
            .into_iter()
            .map(|entry| entry.name)
            .collect();
        names.sort();
        names
    }

    #[test]
    fn reads_back_what_it_wrote_moved_and_removed() {
        let overlay = Overlay::default();
        assert!(overlay.create_directory(Path::new("cache/new/deep"), true, &Disk));
        assert!(overlay.write(Path::new("cache/new/deep/f.tmp"), b"x".to_vec(), &Disk));
        assert!(overlay.rename(
            Path::new("cache/new/deep/f.tmp"),
            Path::new("cache/new/deep/f"),
            &Disk
        ));
        assert_eq!(
            overlay.read(Path::new("cache/new/deep/f"), &Disk),
            Some(b"x".to_vec())
        );
        assert_eq!(
            overlay.get_kind(Path::new("cache/new/deep/f.tmp"), &Disk),
            FileKind::Absent
        );
        assert_eq!(
            names(overlay.list(Path::new("cache"), 2.0, &Disk)),
            ["new", "old"]
        );
        overlay.remove(Path::new("cache/old"), &Disk);
        assert_eq!(
            overlay.get_kind(Path::new("cache/old/fingerprints"), &Disk),
            FileKind::Absent
        );
        assert_eq!(names(overlay.list(Path::new("cache"), 2.0, &Disk)), ["new"]);
        assert!(overlay.copy(
            Path::new("Spec.tla"),
            Path::new("cache/new/Spec.tla"),
            &Disk
        ));
        assert_eq!(
            overlay.read(Path::new("cache/new/Spec.tla"), &Disk),
            Some(b"spec".to_vec())
        );
        assert!(!overlay.write(Path::new("missing/f"), b"x".to_vec(), &Disk));
        assert_eq!(
            overlay.into_journal(),
            [
                FileOperation::MakeDirectory("cache/new/deep".into()),
                FileOperation::Write("cache/new/deep/f.tmp".into(), b"x".to_vec()),
                FileOperation::Rename("cache/new/deep/f.tmp".into(), "cache/new/deep/f".into()),
                FileOperation::Remove("cache/old".into()),
                FileOperation::Copy("Spec.tla".into(), "cache/new/Spec.tla".into()),
            ]
        );
    }

    // Unix.mkdir makes one directory, in one that is there.
    #[test]
    fn makes_one_directory_as_unix_mkdir_does() {
        let overlay = Overlay::default();
        assert!(!overlay.create_directory(Path::new("missing/sub"), false, &Disk));
        assert!(!overlay.create_directory(Path::new("cache"), false, &Disk));
        assert!(!overlay.create_directory(Path::new("Spec.tla/sub"), false, &Disk));
        assert!(overlay.create_directory(Path::new("cache/new"), false, &Disk));
        assert!(overlay.create_directory(Path::new("cache/new/sub"), false, &Disk));
        assert!(overlay.create_directory(Path::new("top"), false, &Disk));
        assert!(overlay.create_directory(Path::new("cache"), true, &Disk));
        assert_eq!(overlay.into_journal().len(), 3);
    }

    // What a directory's entries say isn't there, the host isn't asked of again.
    #[test]
    fn knows_a_path_missing_without_the_host() {
        let overlay = Overlay::default();
        overlay.set_missing(Path::new("cache/old"));
        assert_eq!(
            overlay.get_kind(Path::new("cache/old"), &Disk),
            FileKind::Absent
        );
        assert!(overlay.create_directory(Path::new("cache/old/new"), true, &Disk));
        assert_eq!(
            overlay.get_kind(Path::new("cache/old/fingerprints"), &Disk),
            FileKind::Absent
        );
        overlay.set_missing(Path::new("cache/old/new"));
        assert_eq!(
            overlay.get_kind(Path::new("cache/old/new"), &Disk),
            FileKind::Directory
        );
    }

    #[test]
    fn a_directory_made_again_holds_nothing_it_held() {
        let overlay = Overlay::default();
        overlay.remove(Path::new("cache/old"), &Disk);
        assert!(overlay.create_directory(Path::new("cache/old"), false, &Disk));
        assert_eq!(
            overlay.get_kind(Path::new("cache/old/fingerprints"), &Disk),
            FileKind::Absent
        );
        assert_eq!(
            names(overlay.list(Path::new("cache/old"), 2.0, &Disk)),
            Vec::<String>::new()
        );
    }
}
