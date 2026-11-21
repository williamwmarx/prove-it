use std::cell::RefCell;
use std::collections::HashMap;

use crate::TlcVersion;

#[derive(Clone, Debug, PartialEq, Eq)]
enum Observation {
    Absent,
    Text(String),
    Unknown,
}

/// Results of module reads the source resolver actually performed. Reading this journal never
/// calls the resolver; a name without an event remains unknown.
#[derive(Default)]
pub struct ModuleSourceReads {
    observations: RefCell<HashMap<String, Observation>>,
}

impl ModuleSourceReads {
    pub fn record(&self, name: &str, result: Result<Option<&str>, ()>) {
        let next = match result {
            Ok(None) => Observation::Absent,
            Ok(Some(text)) => Observation::Text(text.to_owned()),
            Err(()) => Observation::Unknown,
        };
        let mut observations = self.observations.borrow_mut();
        match observations.get_mut(name) {
            Some(known) if *known != next => *known = Observation::Unknown,
            Some(_) => {}
            None => {
                observations.insert(name.to_owned(), next);
            }
        }
    }

    /// The caller supplies actual successful standard-shortcut construction events, including
    /// dependencies. Registry membership or a matching operator name is insufficient.
    pub fn canonical_or_absent<'a>(
        &self,
        modules: impl IntoIterator<Item = &'a str>,
        version: TlcVersion,
    ) -> bool {
        let observations = self.observations.borrow();
        modules
            .into_iter()
            .all(|name| match observations.get(name) {
                Some(Observation::Absent) => true,
                Some(Observation::Text(text)) => {
                    crate::get_standard_module(name, version).is_some_and(|pinned| text == pinned)
                }
                Some(Observation::Unknown) | None => false,
            })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn missing_read_is_unknown() {
        let reads = ModuleSourceReads::default();
        assert!(!reads.canonical_or_absent(["TLC"], TlcVersion::Master));
    }

    #[test]
    fn actual_absence_and_pinned_bytes_are_positive() {
        let reads = ModuleSourceReads::default();
        reads.record("TLC", Ok(None));
        reads.record(
            "Json",
            Ok(crate::get_standard_module("Json", TlcVersion::Master)),
        );
        assert!(reads.canonical_or_absent(["TLC", "Json"], TlcVersion::Master));
    }

    #[test]
    fn custom_standard_source_is_unknown() {
        let reads = ModuleSourceReads::default();
        reads.record("TLC", Ok(Some("---- MODULE TLC ----\nFoo == TRUE\n====")));
        assert!(!reads.canonical_or_absent(["TLC"], TlcVersion::Master));
    }

    #[test]
    fn failed_read_is_unknown_even_after_later_success() {
        let reads = ModuleSourceReads::default();
        reads.record("TLC", Err(()));
        reads.record("TLC", Ok(None));
        assert!(!reads.canonical_or_absent(["TLC"], TlcVersion::Master));
    }

    #[test]
    fn conflicting_reads_remain_unknown() {
        let reads = ModuleSourceReads::default();
        reads.record("TLC", Ok(None));
        reads.record(
            "TLC",
            Ok(crate::get_standard_module("TLC", TlcVersion::Master)),
        );
        reads.record("TLC", Ok(None));
        assert!(!reads.canonical_or_absent(["TLC"], TlcVersion::Master));
    }

    #[test]
    fn every_dependency_needs_an_actual_read() {
        let reads = ModuleSourceReads::default();
        reads.record("TLC", Ok(None));
        assert!(!reads.canonical_or_absent(["TLC", "Naturals"], TlcVersion::Master));
        reads.record("Naturals", Ok(None));
        assert!(reads.canonical_or_absent(["TLC", "Naturals"], TlcVersion::Master));
    }
}
