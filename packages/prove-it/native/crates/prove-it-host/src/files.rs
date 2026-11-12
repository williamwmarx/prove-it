//! The operations on the files tlapm's command line asks for, as the check's result hands them to
//! JavaScript to apply in order (`["mkdir", path]` makes a directory and those above it,
//! `["write", path, bytes]`, `["remove", path]` removes a file or a directory with what it holds,
//! `["rename", from, to]`, and `["copy", from, to]` copies a file with the time it was last
//! modified), and the entries of a directory as JavaScript lists them.

use prove_it_check::{Entry, FileOperation};

use crate::value::HostValue;

/// The operations, as the check's result hands them to JavaScript.
pub fn get_journal(operations: &[FileOperation]) -> HostValue {
    let path = |path: &std::path::Path| HostValue::text(&path.to_string_lossy());
    HostValue::Array(
        operations
            .iter()
            .map(|operation| {
                HostValue::Array(match operation {
                    FileOperation::MakeDirectory(target) => {
                        vec![HostValue::text("mkdir"), path(target)]
                    }
                    FileOperation::Write(target, bytes) => vec![
                        HostValue::text("write"),
                        path(target),
                        HostValue::Uint8s(bytes.clone()),
                    ],
                    FileOperation::Remove(target) => vec![HostValue::text("remove"), path(target)],
                    FileOperation::Rename(from, to) => {
                        vec![HostValue::text("rename"), path(from), path(to)]
                    }
                    FileOperation::Copy(from, to) => {
                        vec![HostValue::text("copy"), path(from), path(to)]
                    }
                })
            })
            .collect(),
    )
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

    #[test]
    fn hands_javascript_the_operations_in_order() {
        assert_eq!(
            get_journal(&[
                FileOperation::MakeDirectory("cache/new".into()),
                FileOperation::Write("cache/new/f".into(), b"x".to_vec()),
                FileOperation::Rename("cache/new/f".into(), "cache/new/g".into()),
                FileOperation::Remove("cache/old".into()),
                FileOperation::Copy("Spec.tla".into(), "cache/new/Spec.tla".into()),
            ]),
            HostValue::Array(vec![
                HostValue::Array(vec![HostValue::text("mkdir"), HostValue::text("cache/new")]),
                HostValue::Array(vec![
                    HostValue::text("write"),
                    HostValue::text("cache/new/f"),
                    HostValue::Uint8s(b"x".to_vec())
                ]),
                HostValue::Array(vec![
                    HostValue::text("rename"),
                    HostValue::text("cache/new/f"),
                    HostValue::text("cache/new/g")
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
