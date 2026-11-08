//! What a compiled expression reads: the state variables, the primed variables and the slots of
//! bound names, each sorted, as `Footprint` in `compile.ts`. A memo table keys an expression by
//! the ids its footprint names, in this order.

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Footprint {
    pub vars: Vec<u32>,
    pub primes: Vec<u32>,
    pub slots: Vec<u32>,
}

fn merge_sorted(left: &[u32], right: &[u32]) -> Vec<u32> {
    let mut merged = Vec::with_capacity(left.len() + right.len());
    let (mut left_index, mut right_index) = (0, 0);
    while left_index < left.len() || right_index < right.len() {
        let left_value = left.get(left_index).copied().unwrap_or(u32::MAX);
        let right_value = right.get(right_index).copied().unwrap_or(u32::MAX);
        if left_value <= right_value {
            merged.push(left_value);
            left_index += 1;
            right_index += usize::from(left_value == right_value);
        } else {
            merged.push(right_value);
            right_index += 1;
        }
    }
    merged
}

impl Footprint {
    pub fn var(variable: u32) -> Footprint {
        Footprint {
            vars: vec![variable],
            ..Footprint::default()
        }
    }

    pub fn prime(variable: u32) -> Footprint {
        Footprint {
            primes: vec![variable],
            ..Footprint::default()
        }
    }

    pub fn slot(slot: u32) -> Footprint {
        Footprint {
            slots: vec![slot],
            ..Footprint::default()
        }
    }

    pub fn width(&self) -> usize {
        self.vars.len() + self.primes.len() + self.slots.len()
    }

    pub fn merge(&self, other: &Footprint) -> Footprint {
        Footprint {
            vars: merge_sorted(&self.vars, &other.vars),
            primes: merge_sorted(&self.primes, &other.primes),
            slots: merge_sorted(&self.slots, &other.slots),
        }
    }

    pub fn merge_all<'a>(footprints: impl IntoIterator<Item = &'a Footprint>) -> Footprint {
        footprints
            .into_iter()
            .fold(Footprint::default(), |merged, footprint| {
                merged.merge(footprint)
            })
    }

    pub fn without_slots(&self, slots: &[u32]) -> Footprint {
        Footprint {
            vars: self.vars.clone(),
            primes: self.primes.clone(),
            slots: self
                .slots
                .iter()
                .copied()
                .filter(|slot| !slots.contains(slot))
                .collect(),
        }
    }

    pub fn is_within(&self, outer: &Footprint) -> bool {
        self.vars
            .iter()
            .all(|variable| outer.vars.contains(variable))
            && self
                .primes
                .iter()
                .all(|variable| outer.primes.contains(variable))
            && self.slots.iter().all(|slot| outer.slots.contains(slot))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn merges_sorted_without_duplicates() {
        let left = Footprint {
            vars: vec![1, 3, 5],
            primes: vec![],
            slots: vec![2],
        };
        let right = Footprint {
            vars: vec![2, 3, 6],
            primes: vec![4],
            slots: vec![2, 9],
        };
        let merged = left.merge(&right);
        assert_eq!(merged.vars, vec![1, 2, 3, 5, 6]);
        assert_eq!(merged.primes, vec![4]);
        assert_eq!(merged.slots, vec![2, 9]);
        assert_eq!(merged.without_slots(&[9]).slots, vec![2]);
        assert!(left.without_slots(&[2]).is_within(&merged));
    }
}
