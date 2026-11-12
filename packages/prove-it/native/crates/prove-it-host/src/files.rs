//! The files a check writes through a host whose files JavaScript holds, as tlapm's command line
//! writes its cache: each operation goes into a journal, which the check's result hands back for
//! JavaScript to apply in order once it is known not to decline, and into an overlay, through which
//! the check reads back what it wrote, moved or removed. What the overlay doesn't hold, the check
//! reads from what JavaScript answered (`sources`), as the files were when the check started.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use prove_it_check::{Entry, PathKind};

use crate::value::HostValue;

/// An operation on the files, as JavaScript applies it: `["mkdir", path]` makes a directory and
/// those above it, `["write", path, bytes]`, `["remove", path]` removes a file or a directory with
/// what it holds, `["rename", from, to]`, and `["copy", from, to]` copies a file with the time it
/// was last modified.
#[derive(Clone, Debug, PartialEq)]
enum Operation {
    Mkdir(PathBuf),
    Write(PathBuf, Vec<u8>),
    Remove(PathBuf),
    Rename(PathBuf, PathBuf),
    Copy(PathBuf, PathBuf),
}

/// What the check has made of a path.
#[derive(Clone, Debug, PartialEq)]
enum Node {
    Removed,
    /// A file, with its bytes where the check knows them: a copy's are JavaScript's to give.
    File(Option<Vec<u8>>),
    /// A directory, `is_new` where it wasn't there before, so that nothing JavaScript held under
    /// it is.
    Directory {
        is_new: bool,
    },
}

/// What the check reads of a path where the overlay doesn't say.
pub trait Underlying {
    fn get_kind(&self, path: &Path) -> Option<PathKind>;
    fn list(&self, path: &Path) -> Option<Vec<Entry>>;
}

#[derive(Default)]
pub struct Overlay {
    nodes: RefCell<BTreeMap<PathBuf, Node>>,
    journal: RefCell<Vec<Operation>>,
}

/// What the overlay says of a path: what it holds, that nothing is there, or that JavaScript
/// knows.
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

    pub fn get_kind(&self, path: &Path, underlying: &dyn Underlying) -> Option<PathKind> {
        match self.find(path) {
            Found::Node(Node::File(_)) => Some(PathKind::File),
            Found::Node(_) => Some(PathKind::Directory),
            Found::Missing => None,
            Found::Underlying => underlying.get_kind(path),
        }
    }

    /// The bytes the check wrote at the path, `Some(None)` where nothing it can read is there, and
    /// None where JavaScript knows.
    pub fn read(&self, path: &Path) -> Option<Option<Vec<u8>>> {
        match self.find(path) {
            Found::Node(Node::File(bytes)) => Some(bytes),
            Found::Node(_) | Found::Missing => Some(None),
            Found::Underlying => None,
        }
    }

    pub fn list(&self, path: &Path, now: f64, underlying: &dyn Underlying) -> Option<Vec<Entry>> {
        let mut entries = match self.find(path) {
            Found::Node(Node::Directory { is_new: true }) => Vec::new(),
            Found::Node(Node::Directory { is_new: false }) | Found::Underlying => {
                if underlying.get_kind(path) != Some(PathKind::Directory) {
                    return None;
                }
                underlying.list(path)?
            }
            Found::Node(_) | Found::Missing => return None,
        };
        entries.retain(|entry| {
            !matches!(
                self.nodes.borrow().get(&path.join(&entry.name)),
                Some(Node::Removed)
            )
        });
        for (child, node) in self.nodes.borrow().iter() {
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

    pub fn create_directory(&self, path: &Path, underlying: &dyn Underlying) -> bool {
        let mut missing = Vec::new();
        for ancestor in path.ancestors() {
            if ancestor.as_os_str().is_empty() {
                break;
            }
            match self.get_kind(ancestor, underlying) {
                Some(PathKind::Directory) => break,
                Some(_) => return false,
                None => missing.push(ancestor.to_path_buf()),
            }
        }
        let mut nodes = self.nodes.borrow_mut();
        for directory in missing {
            nodes.insert(directory, Node::Directory { is_new: true });
        }
        self.journal
            .borrow_mut()
            .push(Operation::Mkdir(path.to_path_buf()));
        true
    }

    fn is_in_directory(&self, path: &Path, underlying: &dyn Underlying) -> bool {
        path.parent().is_none_or(|parent| {
            parent.as_os_str().is_empty()
                || self.get_kind(parent, underlying) == Some(PathKind::Directory)
        })
    }

    pub fn write(&self, path: &Path, bytes: &[u8], underlying: &dyn Underlying) -> bool {
        if !self.is_in_directory(path, underlying)
            || self.get_kind(path, underlying) == Some(PathKind::Directory)
        {
            return false;
        }
        self.nodes
            .borrow_mut()
            .insert(path.to_path_buf(), Node::File(Some(bytes.to_vec())));
        self.journal
            .borrow_mut()
            .push(Operation::Write(path.to_path_buf(), bytes.to_vec()));
        true
    }

    pub fn remove(&self, path: &Path, underlying: &dyn Underlying) -> bool {
        if self.get_kind(path, underlying).is_none() {
            return true;
        }
        let mut nodes = self.nodes.borrow_mut();
        nodes.retain(|known, _| !known.starts_with(path));
        nodes.insert(path.to_path_buf(), Node::Removed);
        self.journal
            .borrow_mut()
            .push(Operation::Remove(path.to_path_buf()));
        true
    }

    pub fn rename(&self, from: &Path, to: &Path, underlying: &dyn Underlying) -> bool {
        if self.get_kind(from, underlying) != Some(PathKind::File)
            || !self.is_in_directory(to, underlying)
            || self.get_kind(to, underlying) == Some(PathKind::Directory)
        {
            return false;
        }
        let bytes = self.read(from).flatten();
        let mut nodes = self.nodes.borrow_mut();
        nodes.insert(from.to_path_buf(), Node::Removed);
        nodes.insert(to.to_path_buf(), Node::File(bytes));
        self.journal
            .borrow_mut()
            .push(Operation::Rename(from.to_path_buf(), to.to_path_buf()));
        true
    }

    pub fn copy(&self, from: &Path, to: &Path, underlying: &dyn Underlying) -> bool {
        if self.get_kind(from, underlying) != Some(PathKind::File)
            || !self.is_in_directory(to, underlying)
            || self.get_kind(to, underlying) == Some(PathKind::Directory)
        {
            return false;
        }
        let bytes = self.read(from).flatten();
        self.nodes
            .borrow_mut()
            .insert(to.to_path_buf(), Node::File(bytes));
        self.journal
            .borrow_mut()
            .push(Operation::Copy(from.to_path_buf(), to.to_path_buf()));
        true
    }

    /// The journal, as the check's result hands it to JavaScript.
    pub fn get_journal(&self) -> HostValue {
        let path = |path: &PathBuf| HostValue::text(&path.to_string_lossy());
        HostValue::Array(
            self.journal
                .borrow()
                .iter()
                .map(|operation| {
                    HostValue::Array(match operation {
                        Operation::Mkdir(target) => vec![HostValue::text("mkdir"), path(target)],
                        Operation::Write(target, bytes) => vec![
                            HostValue::text("write"),
                            path(target),
                            HostValue::Uint8s(bytes.clone()),
                        ],
                        Operation::Remove(target) => vec![HostValue::text("remove"), path(target)],
                        Operation::Rename(from, to) => {
                            vec![HostValue::text("rename"), path(from), path(to)]
                        }
                        Operation::Copy(from, to) => {
                            vec![HostValue::text("copy"), path(from), path(to)]
                        }
                    })
                })
                .collect(),
        )
    }
}

/// The entries of a directory as JavaScript answers `entries:<path>`: each entry's `mtimeMs` and
/// name, every one of them ended by a NUL, which no name holds.
pub fn parse_entries(text: &str) -> Option<Vec<Entry>> {
    let mut fields = text.split('\0');
    let mut entries = Vec::new();
    loop {
        let modified = fields.next()?;
        if modified.is_empty() {
            return fields.next().is_none().then_some(entries);
        }
        let name = fields.next()?;
        entries.push(Entry {
            name: name.to_owned(),
            modified: modified.parse().ok()?,
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct Disk;

    impl Underlying for Disk {
        fn get_kind(&self, path: &Path) -> Option<PathKind> {
            match path.to_str()? {
                "cache" | "cache/old" => Some(PathKind::Directory),
                "cache/old/fingerprints" | "Spec.tla" => Some(PathKind::File),
                _ => None,
            }
        }

        fn list(&self, path: &Path) -> Option<Vec<Entry>> {
            match path.to_str()? {
                "cache" => Some(vec![Entry {
                    name: "old".to_owned(),
                    modified: 1.0,
                }]),
                "cache/old" => Some(vec![Entry {
                    name: "fingerprints".to_owned(),
                    modified: 1.0,
                }]),
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
        assert!(overlay.create_directory(Path::new("cache/new/deep"), &Disk));
        assert!(overlay.write(Path::new("cache/new/deep/f.tmp"), b"x", &Disk));
        assert!(overlay.rename(
            Path::new("cache/new/deep/f.tmp"),
            Path::new("cache/new/deep/f"),
            &Disk
        ));
        assert_eq!(
            overlay.read(Path::new("cache/new/deep/f")),
            Some(Some(b"x".to_vec()))
        );
        assert_eq!(
            overlay.get_kind(Path::new("cache/new/deep/f.tmp"), &Disk),
            None
        );
        assert_eq!(
            names(overlay.list(Path::new("cache"), 2.0, &Disk)),
            ["new", "old"]
        );
        assert!(overlay.remove(Path::new("cache/old"), &Disk));
        assert_eq!(
            overlay.get_kind(Path::new("cache/old/fingerprints"), &Disk),
            None
        );
        assert_eq!(names(overlay.list(Path::new("cache"), 2.0, &Disk)), ["new"]);
        assert!(overlay.copy(
            Path::new("Spec.tla"),
            Path::new("cache/new/Spec.tla"),
            &Disk
        ));
        assert_eq!(overlay.read(Path::new("cache/new/Spec.tla")), Some(None));
        assert_eq!(overlay.read(Path::new("Spec.tla")), None);
        assert!(!overlay.write(Path::new("missing/f"), b"x", &Disk));
        assert_eq!(
            overlay.get_journal(),
            HostValue::Array(vec![
                HostValue::Array(vec![
                    HostValue::text("mkdir"),
                    HostValue::text("cache/new/deep")
                ]),
                HostValue::Array(vec![
                    HostValue::text("write"),
                    HostValue::text("cache/new/deep/f.tmp"),
                    HostValue::Uint8s(b"x".to_vec())
                ]),
                HostValue::Array(vec![
                    HostValue::text("rename"),
                    HostValue::text("cache/new/deep/f.tmp"),
                    HostValue::text("cache/new/deep/f")
                ]),
                HostValue::Array(vec![
                    HostValue::text("remove"),
                    HostValue::text("cache/old")
                ]),
                HostValue::Array(vec![
                    HostValue::text("copy"),
                    HostValue::text("Spec.tla"),
                    HostValue::text("cache/new/Spec.tla")
                ]),
            ])
        );
    }

    #[test]
    fn a_directory_made_again_holds_nothing_it_held() {
        let overlay = Overlay::default();
        assert!(overlay.remove(Path::new("cache/old"), &Disk));
        assert!(overlay.create_directory(Path::new("cache/old"), &Disk));
        assert_eq!(
            overlay.get_kind(Path::new("cache/old/fingerprints"), &Disk),
            None
        );
        assert_eq!(
            names(overlay.list(Path::new("cache/old"), 2.0, &Disk)),
            Vec::<String>::new()
        );
    }

    #[test]
    fn reads_the_entries_javascript_lists() {
        assert_eq!(parse_entries(""), Some(Vec::new()));
        assert_eq!(
            parse_entries("1.5\0a\x002\0b\0"),
            Some(vec![
                Entry {
                    name: "a".to_owned(),
                    modified: 1.5
                },
                Entry {
                    name: "b".to_owned(),
                    modified: 2.0
                },
            ])
        );
        assert_eq!(parse_entries("x\0a\0"), None);
        assert_eq!(parse_entries("1\0"), None);
    }
}
