//! The files and directories a run makes or writes as TLC would, each as it was before the run
//! first touched it. A run that declines hands the model to another checker, which must find the
//! file system as the run found it, so a decline puts back what the run wrote ([`restore`]).
//!
//! Each top-level check keeps a journal of its own ([`mark`] makes it where the thread has none),
//! which its nested scopes share and which the threads it starts take with them ([`current`],
//! [`Journal::enter`]): two checks in one process, as a host runs them, never put back what the
//! other wrote. The journal lets go of what it kept once the check that made it ends without a
//! decline ([`release`]).

use std::cell::RefCell;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, MutexGuard, PoisonError};

enum Before {
    /// A file there, with its bytes, or none.
    File(PathBuf, Option<Vec<u8>>),
    /// A directory the run made.
    Directory(PathBuf),
    /// Where a scope starts ([`mark`]).
    Mark,
}

/// What one top-level check wrote, each file and directory as it was before, shared by the threads
/// of that check.
#[derive(Clone, Default)]
pub struct Journal(Arc<Mutex<Vec<Before>>>);

thread_local! {
    /// The journal of the check this thread runs for.
    static CURRENT: RefCell<Option<Journal>> = const { RefCell::new(None) };
}

impl Journal {
    fn lock(&self) -> MutexGuard<'_, Vec<Before>> {
        self.0.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// Makes this the journal of the thread until what it returns is dropped.
    pub fn enter(&self) -> Entered {
        Entered {
            previous: CURRENT.with(|current| current.replace(Some(self.clone()))),
        }
    }
}

/// A thread's journal while it is kept, and the one before it after.
pub struct Entered {
    previous: Option<Journal>,
}

impl Drop for Entered {
    fn drop(&mut self) {
        let previous = self.previous.take();
        CURRENT.with(|current| *current.borrow_mut() = previous);
    }
}

/// The journal of the check this thread runs for, for a thread it starts to take ([`enter`]).
pub fn current() -> Option<Journal> {
    CURRENT.with(|current| current.borrow().clone())
}

/// Runs `work` with `journal`, the one [`current`] gave the thread that starts this one.
pub fn enter<T>(journal: Option<&Journal>, work: impl FnOnce() -> T) -> T {
    let _entered = journal.map(Journal::enter);
    work()
}

/// Keeps a file as it is before the run writes it: its bytes, or that there is none. A file it
/// can't read, but for one that isn't there, it can't keep, and the run must not write it: the
/// read's error. So too a thread outside any check, whose write nothing could put back.
pub fn keep_file(path: &Path) -> std::io::Result<()> {
    let Some(journal) = current() else {
        return Err(std::io::Error::other("a write outside a check's journal"));
    };
    // The file as the scope found it is kept once.
    if journal
        .lock()
        .iter()
        .rev()
        .take_while(|before| !matches!(before, Before::Mark))
        .any(|before| matches!(before, Before::File(kept, _) if kept == path))
    {
        return Ok(());
    }
    // Only a regular file has bytes to keep: a read of a pipe or a device may never end, and a
    // write to one nothing puts back.
    if std::fs::metadata(path).is_ok_and(|metadata| !metadata.is_file() && !metadata.is_dir()) {
        return Err(std::io::Error::other("a file that isn't a regular file"));
    }
    let (path, before) = match std::fs::read(path) {
        Ok(bytes) => (path.to_path_buf(), Some(bytes)),
        // `read` follows a link: where the link is there and its target isn't, the run makes the
        // target, through the link, and the link stays. What a decline removes is the target.
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            (get_destination(path)?, None)
        }
        // A directory there no write of a file changes: the write fails, as TLC's does.
        Err(error) if error.kind() == std::io::ErrorKind::IsADirectory => return Ok(()),
        Err(error) => return Err(error),
    };
    journal.lock().push(Before::File(path, before));
    Ok(())
}

/// Where a write to `path`, which isn't there, makes a file: `path`, or where the links there lead
/// where the last of them names what isn't there.
fn get_destination(path: &Path) -> std::io::Result<PathBuf> {
    // As many links as Linux follows (`MAXSYMLINKS`).
    const MOST_LINKS: usize = 40;
    let mut destination = path.to_path_buf();
    for _ in 0..=MOST_LINKS {
        match std::fs::symlink_metadata(&destination) {
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(destination),
            Err(error) => return Err(error),
            Ok(metadata) if metadata.file_type().is_symlink() => {
                let target = std::fs::read_link(&destination)?;
                destination = match destination.parent() {
                    Some(parent) if target.is_relative() => parent.join(target),
                    _ => target,
                };
            }
            // `read` found nothing, and yet something is there now.
            Ok(_) => return Err(std::io::Error::other("a file that came as it was read")),
        }
    }
    Err(std::io::Error::other("a chain of links too long to follow"))
}

/// `create_dir_all`, keeping each directory it makes. Outside any check it makes none.
pub fn create_dir_all(path: &Path) -> std::io::Result<()> {
    let Some(journal) = current() else {
        return Err(std::io::Error::other("a write outside a check's journal"));
    };
    let mut missing = Vec::new();
    let mut at = Some(path);
    while let Some(directory) = at.filter(|directory| !directory.as_os_str().is_empty()) {
        if directory.exists() {
            break;
        }
        missing.push(directory.to_path_buf());
        at = directory.parent();
    }
    let result = std::fs::create_dir_all(path);
    let mut journal = journal.lock();
    for directory in missing.into_iter().rev() {
        if directory.is_dir() {
            journal.push(Before::Directory(directory));
        }
    }
    result
}

/// Where a scope's part of its check's journal starts, for [`restore`] to go back to or
/// [`release`] to give up. The outermost scope of a check makes the check's journal and keeps it
/// as the thread's until the mark goes.
pub struct Mark {
    journal: Journal,
    at: usize,
    // Dropped after the rest: the thread's journal as it was before.
    entered: Option<Entered>,
}

/// Marks where a scope starts in the thread's journal, which it makes where there is none.
pub fn mark() -> Mark {
    let (journal, entered) = match current() {
        Some(journal) => (journal, None),
        None => {
            let journal = Journal::default();
            let entered = journal.enter();
            (journal, Some(entered))
        }
    };
    let at = {
        let mut kept = journal.lock();
        kept.push(Before::Mark);
        kept.len() - 1
    };
    Mark {
        journal,
        at,
        entered,
    }
}

/// A file or directory [`restore`] failed to put back, and why.
pub struct Unrestored {
    pub path: PathBuf,
    pub error: std::io::Error,
}

/// Puts back what the scope wrote since `mark`, last first: a file's bytes, or no file, and no
/// directory it made, where it is empty again. What it fails to put back, it returns.
pub fn restore(mark: Mark) -> Vec<Unrestored> {
    let mut unrestored = Vec::new();
    let mut journal = mark.journal.lock();
    while journal.len() > mark.at {
        let (path, result) = match journal.pop() {
            Some(Before::File(path, Some(bytes))) => {
                let result = std::fs::write(&path, bytes);
                (path, result)
            }
            Some(Before::File(path, None)) => {
                let result = std::fs::remove_file(&path).or_else(|error| {
                    // What the run never made there is as it was.
                    match error.kind() {
                        std::io::ErrorKind::NotFound => Ok(()),
                        _ => Err(error),
                    }
                });
                (path, result)
            }
            Some(Before::Directory(path)) => {
                let result = std::fs::remove_dir(&path).or_else(|error| match error.kind() {
                    std::io::ErrorKind::NotFound | std::io::ErrorKind::DirectoryNotEmpty => Ok(()),
                    _ => Err(error),
                });
                (path, result)
            }
            Some(Before::Mark) | None => continue,
        };
        if let Err(error) = result {
            unrestored.push(Unrestored { path, error });
        }
    }
    unrestored
}

/// Gives up what the scope kept since `mark` where it ends without a decline. A scope within
/// another leaves it for that one, which may still decline and put back what the inner one wrote;
/// the outermost scope's check lets go of all it kept.
pub fn release(mark: Mark) {
    let mut journal = mark.journal.lock();
    if mark.entered.is_some() {
        *journal = Vec::new();
    } else if matches!(journal.get(mark.at), Some(Before::Mark)) {
        journal.remove(mark.at);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn directory(name: &str) -> PathBuf {
        let path =
            std::env::temp_dir().join(format!("prove-it-written-{name}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&path);
        std::fs::create_dir_all(&path).expect("a directory for the test");
        path
    }

    fn held(journal: &Journal) -> usize {
        journal.lock().len()
    }

    // Check A's scope opens, check B writes a file and succeeds, then A declines: A puts back only
    // what A wrote, and B's file stays as B wrote it.
    #[test]
    fn a_check_that_declines_puts_back_only_its_own_writes() {
        let root = directory("interleaved");
        let (a_file, b_file) = (root.join("a"), root.join("b"));
        let (a_path, b_path) = (&a_file, &b_file);
        std::fs::write(&a_file, "a before").unwrap();
        std::fs::write(&b_file, "b before").unwrap();
        let (a_opened, a_opened_rx) = std::sync::mpsc::channel();
        let (b_done, b_done_rx) = std::sync::mpsc::channel();
        std::thread::scope(|scope| {
            let a = scope.spawn(move || {
                let mark = mark();
                keep_file(a_path).unwrap();
                std::fs::write(a_path, "a written").unwrap();
                a_opened.send(()).unwrap();
                b_done_rx.recv().unwrap();
                assert!(restore(mark).is_empty());
            });
            let b = scope.spawn(move || {
                a_opened_rx.recv().unwrap();
                let mark = mark();
                keep_file(b_path).unwrap();
                std::fs::write(b_path, "b committed").unwrap();
                release(mark);
                b_done.send(()).unwrap();
            });
            a.join().unwrap();
            b.join().unwrap();
        });
        assert_eq!(std::fs::read_to_string(&a_file).unwrap(), "a before");
        assert_eq!(std::fs::read_to_string(&b_file).unwrap(), "b committed");
        let _ = std::fs::remove_dir_all(root);
    }

    // A device has no bytes to keep, and a read of one may never end: the journal refuses it
    // without reading it.
    #[cfg(unix)]
    #[test]
    fn a_file_that_is_not_regular_is_not_kept() {
        let mark = mark();
        let before = held(&mark.journal);
        assert!(keep_file(Path::new("/dev/zero")).is_err());
        assert_eq!(held(&mark.journal), before);
        release(mark);
    }

    // A thread the check starts takes its journal, and a decline puts back what that thread wrote.
    #[test]
    fn a_thread_a_check_starts_writes_into_its_journal() {
        let root = directory("worker");
        let file = root.join("out");
        let mark = mark();
        let journal = current();
        std::thread::scope(|scope| {
            scope
                .spawn(|| {
                    enter(journal.as_ref(), || {
                        keep_file(&file).unwrap();
                        std::fs::write(&file, "written").unwrap();
                    });
                })
                .join()
                .unwrap();
        });
        assert!(restore(mark).is_empty());
        assert!(!file.exists());
        assert!(current().is_none());
        let _ = std::fs::remove_dir_all(root);
    }

    // A directory where the run would write a file is left to the write, which fails.
    #[test]
    fn a_directory_is_left_to_the_write() {
        let root = directory("is-directory");
        let mark = mark();
        assert!(keep_file(&root).is_ok());
        assert!(restore(mark).is_empty());
        assert!(root.is_dir());
        let _ = std::fs::remove_dir_all(root);
    }

    #[test]
    fn a_write_outside_a_check_is_refused() {
        let root = directory("outside");
        assert!(keep_file(&root.join("out")).is_err());
        let _ = std::fs::remove_dir_all(root);
    }

    // The outermost scope that ends without a decline lets go of the bytes it kept; an inner one
    // leaves them for its parent, which may still put back what the inner one wrote.
    #[test]
    fn a_successful_check_lets_go_of_what_it_kept() {
        let root = directory("release");
        let file = root.join("out");
        std::fs::write(&file, "before").unwrap();
        let outer = mark();
        let journal = current().expect("the check's journal");
        let inner = mark();
        keep_file(&file).unwrap();
        std::fs::write(&file, "inner").unwrap();
        release(inner);
        assert_eq!(held(&journal), 2);
        assert!(restore(outer).is_empty());
        assert_eq!(std::fs::read_to_string(&file).unwrap(), "before");
        assert!(current().is_none());

        let outer = mark();
        let journal = current().expect("the check's journal");
        let inner = mark();
        keep_file(&file).unwrap();
        std::fs::write(&file, "kept").unwrap();
        release(inner);
        release(outer);
        assert_eq!(held(&journal), 0);
        assert!(current().is_none());
        assert_eq!(std::fs::read_to_string(&file).unwrap(), "kept");
        let _ = std::fs::remove_dir_all(root);
    }

    // A link to a file that isn't there leads the write to its target, which a decline removes,
    // and the link stays as it was.
    #[cfg(unix)]
    #[test]
    fn a_dangling_link_stays_and_its_target_goes() {
        let root = directory("dangling");
        let (link, middle, target) = (root.join("out.json"), root.join("middle"), root.join("t"));
        std::os::unix::fs::symlink("middle", &link).unwrap();
        std::os::unix::fs::symlink(&target, &middle).unwrap();
        let mark = mark();
        keep_file(&link).unwrap();
        std::fs::write(&link, "0\n").unwrap();
        assert_eq!(std::fs::read_to_string(&target).unwrap(), "0\n");
        assert!(restore(mark).is_empty());
        assert!(!target.exists());
        assert_eq!(std::fs::read_link(&link).unwrap(), Path::new("middle"));
        assert_eq!(std::fs::read_link(&middle).unwrap(), target);
        let _ = std::fs::remove_dir_all(root);
    }

    // A link that leads to itself is refused before the run writes through it.
    #[cfg(unix)]
    #[test]
    fn a_looping_link_is_refused() {
        let root = directory("loop");
        let link = root.join("out.json");
        std::os::unix::fs::symlink("out.json", &link).unwrap();
        let mark = mark();
        assert!(keep_file(&link).is_err());
        assert!(restore(mark).is_empty());
        assert!(std::fs::symlink_metadata(&link).is_ok());
        let _ = std::fs::remove_dir_all(root);
    }

    // A link to a file that is there keeps the target's bytes, which a decline writes back through
    // the link, which stays.
    #[cfg(unix)]
    #[test]
    fn a_link_to_a_file_is_put_back_through_it() {
        let root = directory("link");
        let (link, target) = (root.join("out.json"), root.join("target"));
        std::fs::write(&target, "before").unwrap();
        std::os::unix::fs::symlink(&target, &link).unwrap();
        let mark = mark();
        keep_file(&link).unwrap();
        std::fs::write(&link, "written").unwrap();
        assert!(restore(mark).is_empty());
        assert!(
            std::fs::symlink_metadata(&link)
                .unwrap()
                .file_type()
                .is_symlink()
        );
        assert_eq!(std::fs::read_to_string(&target).unwrap(), "before");
        let _ = std::fs::remove_dir_all(root);
    }

    // What restore can't put back, it reports.
    #[cfg(unix)]
    #[test]
    fn a_failure_to_put_back_is_reported() {
        let root = directory("unrestored");
        let file = root.join("out");
        let mark = mark();
        keep_file(&file).unwrap();
        // The run made a directory where the file wasn't, which `remove_file` can't take.
        std::fs::create_dir(&file).unwrap();
        let unrestored = restore(mark);
        assert_eq!(unrestored.len(), 1);
        assert_eq!(unrestored[0].path, file);
        let _ = std::fs::remove_dir_all(root);
    }
}
