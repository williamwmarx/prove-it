//! The fingerprint status table used by TLC's depth-first iterative-deepening checker.
//!
//! TLC stores the discovery iteration and two bits per fingerprint (FPIntSet and
//! MemFPIntSet). The leveled bit alternates each iteration, avoiding a table-wide reset.

use std::collections::HashMap;

const DONE: u32 = 1;
const LEVELED: u32 = 2;

#[derive(Default)]
pub struct Statuses {
    values: HashMap<u64, u32>,
    level: u32,
    leveled: u32,
}

impl Statuses {
    pub fn new() -> Self {
        Self {
            level: 1,
            ..Self::default()
        }
    }

    pub fn next_level(&mut self) {
        self.level += 1;
        self.leveled ^= LEVELED;
    }

    /// Insert a fingerprint, or return its old status. Zero means newly inserted.
    pub fn insert(&mut self, fp: u64) -> u32 {
        match self.values.entry(fp) {
            std::collections::hash_map::Entry::Occupied(entry) => *entry.get(),
            std::collections::hash_map::Entry::Vacant(entry) => {
                entry.insert((self.level << 2) | self.leveled);
                0
            }
        }
    }

    pub fn status(&self, fp: u64) -> u32 {
        self.values.get(&fp).copied().unwrap_or(0)
    }

    pub fn completed(&self, status: u32) -> bool {
        status & LEVELED == self.leveled || status & DONE != 0
    }

    pub fn leaf(&self, status: u32) -> bool {
        status == 0 || status >> 2 == self.level
    }

    pub fn discovery_level(status: u32) -> u32 {
        status >> 2
    }

    pub fn done(&mut self, fp: u64) {
        *self.values.get_mut(&fp).expect("inserted fingerprint") |= DONE;
    }

    pub fn levelled(&mut self, fp: u64) {
        let status = self.values.get_mut(&fp).expect("inserted fingerprint");
        *status = (*status & !LEVELED) | self.leveled;
    }

    pub fn is_done(status: u32) -> bool {
        status & DONE != 0
    }
}

#[cfg(test)]
mod tests {
    use super::Statuses;

    #[test]
    fn statuses_follow_tlc_iterations() {
        let mut statuses = Statuses::new();
        assert_eq!(statuses.insert(1), 0);
        assert!(statuses.completed(statuses.status(1)));
        statuses.next_level();
        assert!(!statuses.completed(statuses.status(1)));
        assert!(!statuses.leaf(statuses.status(1)));
        assert_eq!(statuses.insert(2), 0);
        assert!(statuses.leaf(statuses.status(2)));
        statuses.levelled(1);
        assert!(statuses.completed(statuses.status(1)));
        statuses.done(2);
        statuses.next_level();
        assert!(!statuses.completed(statuses.status(1)));
        assert!(statuses.completed(statuses.status(2)));
        assert!(Statuses::is_done(statuses.status(2)));
    }
}

/// The worker's result at a level. Multiple eligible paths require TLC's independently seeded
/// worker random generator, so the caller must decline if its choice can affect output.
#[derive(Debug, PartialEq, Eq)]
pub enum LevelResult<E> {
    Finished { more: bool },
    Ambiguous,
    Stopped(E),
}

/// Run one `DFIDWorker` iteration. `expand` checks a state's successors, updates their statuses,
/// and returns the successors that were incomplete when generated and whether all were non-leaves.
pub fn run_level<S: Clone + PartialEq, E>(
    statuses: &mut Statuses,
    initial: &[(u64, S)],
    limit: u32,
    independent_initials: bool,
    mut expand: impl FnMut(&[S], u32, bool, &mut Statuses) -> Result<(Vec<(u64, S)>, bool), E>,
) -> LevelResult<E> {
    statuses.next_level();
    let mut more = false;
    loop {
        let mut starts = initial
            .iter()
            .filter(|(fp, _)| !statuses.completed(statuses.status(*fp)));
        let Some((fp, state)) = starts.next() else {
            return LevelResult::Finished { more };
        };
        if !independent_initials && starts.any(|(other, value)| other != fp || value != state) {
            return LevelResult::Ambiguous;
        }
        let mut stack = vec![(*fp, state.clone(), Vec::<(u64, S)>::new())];
        let mut leaf = limit < 2;
        let (next, nonleaf) = match expand(std::slice::from_ref(state), 1, leaf, statuses) {
            Ok(v) => v,
            Err(error) => return LevelResult::Stopped(error),
        };
        stack[0].2 = next;
        more |= !nonleaf;
        while !leaf {
            let depth = stack.len() as u32;
            let frame = stack.last_mut().expect("nonempty stack");
            frame.2.retain(|(fp, _)| {
                let status = statuses.status(*fp);
                !statuses.completed(status) && depth < Statuses::discovery_level(status)
            });
            if frame.2.is_empty() {
                statuses.levelled(frame.0);
                stack.pop();
                if stack.is_empty() {
                    break;
                }
                continue;
            }
            let fp = frame.2[0].0;
            if frame
                .2
                .iter()
                .any(|(other, state)| *other != fp || state != &frame.2[0].1)
            {
                return LevelResult::Ambiguous;
            }
            let (fp, state) = frame.2.swap_remove(0);
            leaf = depth >= limit - 1;
            let mut path: Vec<S> = stack.iter().map(|(_, state, _)| state.clone()).collect();
            path.push(state.clone());
            let (next, nonleaf) = match expand(&path, depth + 1, leaf, statuses) {
                Ok(v) => v,
                Err(error) => return LevelResult::Stopped(error),
            };
            more |= !nonleaf;
            stack.push((fp, state, next));
        }
    }
}

#[cfg(test)]
mod traversal_tests {
    use super::{LevelResult, Statuses, run_level};

    #[test]
    fn repeats_the_cycle_at_each_limit() {
        let mut statuses = Statuses::new();
        statuses.insert(0);
        let mut generated = 1;
        let initial = [(0, 0u64)];
        let mut counts = Vec::new();
        for level in 2..=4 {
            counts.push(generated);
            let result: LevelResult<()> = run_level(
                &mut statuses,
                &initial,
                level,
                false,
                |path, _, leaf, statuses| {
                    let state = path.last().unwrap();
                    generated += 1;
                    let successor = (state + 1) % 3;
                    let old = statuses.insert(successor);
                    let all_done = Statuses::is_done(old);
                    let all_nonleaf = !statuses.leaf(old);
                    let next = if statuses.completed(old) {
                        Vec::new()
                    } else {
                        vec![(successor, successor)]
                    };
                    if all_done || (leaf && all_nonleaf) {
                        statuses.done(*state);
                    }
                    Ok((next, all_nonleaf))
                },
            );
            assert_eq!(result, LevelResult::Finished { more: level < 4 });
        }
        assert_eq!(counts, [1, 2, 4]);
        assert_eq!(generated, 7);
    }
}
