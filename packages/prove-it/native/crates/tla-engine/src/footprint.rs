//! What a compiled expression reads: the state variables, the primed variables and the slots of
//! bound names, each sorted, as `Footprint` in `compile.ts`. A memo table keys an expression by
//! the ids its footprint names, in this order.

use std::sync::Arc;

#[derive(Clone, Debug, Default)]
pub struct Footprint {
    pub vars: Vec<u32>,
    pub primes: Vec<u32>,
    pub slots: Vec<u32>,
    /// Where it reads some of that only through names whose values are bound once
    /// (`Machine::binding`): those names, and what it reads beside them. Its value is a function
    /// of their values and of those reads, which a memo table may key it by instead.
    pub through: Option<Arc<Through>>,
}

/// What an expression reads beside the names bound once it reads, and those names by their
/// number, sorted.
#[derive(Debug, Default)]
pub struct Through {
    pub vars: Vec<u32>,
    pub primes: Vec<u32>,
    pub slots: Vec<u32>,
    pub bindings: Vec<BindingRead>,
}

/// A name bound once, by its number in `Program::bindings`, with what its expression reads.
#[derive(Clone, Debug)]
pub struct BindingRead {
    pub index: u32,
    pub reads: Arc<Footprint>,
}

// What it reads is the same whichever names it reads it through: a recursive definition's body
// compiles until what it reads settles, and binds its names anew each time.
impl PartialEq for Footprint {
    fn eq(&self, other: &Footprint) -> bool {
        self.vars == other.vars && self.primes == other.primes && self.slots == other.slots
    }
}

impl Eq for Footprint {}

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

fn merge_bindings(left: &[BindingRead], right: &[BindingRead]) -> Vec<BindingRead> {
    let mut merged = Vec::with_capacity(left.len() + right.len());
    let (mut left_index, mut right_index) = (0, 0);
    while left_index < left.len() || right_index < right.len() {
        let left_value = left
            .get(left_index)
            .map_or(u32::MAX, |binding| binding.index);
        let right_value = right
            .get(right_index)
            .map_or(u32::MAX, |binding| binding.index);
        if left_value <= right_value {
            merged.push(left[left_index].clone());
            left_index += 1;
            right_index += usize::from(left_value == right_value);
        } else {
            merged.push(right[right_index].clone());
            right_index += 1;
        }
    }
    merged
}

impl Through {
    pub fn width(&self) -> usize {
        self.vars.len() + self.primes.len() + self.slots.len() + self.bindings.len()
    }
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

    /// What a read of a name bound once reads: what its expression does, through the name alone.
    pub fn binding(index: u32, reads: &Footprint) -> Footprint {
        Footprint {
            through: Some(Arc::new(Through {
                bindings: vec![BindingRead {
                    index,
                    reads: Arc::new(reads.clone()),
                }],
                ..Through::default()
            })),
            ..reads.clone()
        }
    }

    /// What it reads, whichever names bound once it reads it through.
    pub fn direct(&self) -> Footprint {
        Footprint {
            through: None,
            ..self.clone()
        }
    }

    /// Whether this is what a read of one name bound once reads, and nothing beside it.
    pub fn is_binding(&self) -> bool {
        self.through.as_deref().is_some_and(|through| {
            through.vars.is_empty()
                && through.primes.is_empty()
                && through.slots.is_empty()
                && through.bindings.len() == 1
        })
    }

    pub fn width(&self) -> usize {
        self.vars.len() + self.primes.len() + self.slots.len()
    }

    // What it reads beside the names bound once it reads, and those names.
    fn beside(&self) -> (&[u32], &[u32], &[u32], &[BindingRead]) {
        match &self.through {
            Some(through) => (
                &through.vars,
                &through.primes,
                &through.slots,
                &through.bindings,
            ),
            None => (&self.vars, &self.primes, &self.slots, &[]),
        }
    }

    pub fn merge(&self, other: &Footprint) -> Footprint {
        let through = (self.through.is_some() || other.through.is_some()).then(|| {
            let (left, right) = (self.beside(), other.beside());
            Arc::new(Through {
                vars: merge_sorted(left.0, right.0),
                primes: merge_sorted(left.1, right.1),
                slots: merge_sorted(left.2, right.2),
                bindings: merge_bindings(left.3, right.3),
            })
        });
        Footprint {
            vars: merge_sorted(&self.vars, &other.vars),
            primes: merge_sorted(&self.primes, &other.primes),
            slots: merge_sorted(&self.slots, &other.slots),
            through,
        }
    }

    pub fn merge_all<'a>(footprints: impl IntoIterator<Item = &'a Footprint>) -> Footprint {
        footprints
            .into_iter()
            .fold(Footprint::default(), |merged, footprint| {
                merged.merge(footprint)
            })
    }

    /// What it reads besides `slots`, as where their names are bound around it. A name bound
    /// once whose expression reads one of them has a value for each value of theirs, so what
    /// that expression reads stands in the name's place.
    pub fn without_slots(&self, slots: &[u32]) -> Footprint {
        let kept = |list: &[u32]| -> Vec<u32> {
            list.iter()
                .copied()
                .filter(|slot| !slots.contains(slot))
                .collect()
        };
        let through = self.through.as_ref().and_then(|through| {
            let mut vars = through.vars.clone();
            let mut primes = through.primes.clone();
            let mut beside = kept(&through.slots);
            let mut bindings = Vec::new();
            for binding in &through.bindings {
                if binding.reads.slots.iter().any(|slot| slots.contains(slot)) {
                    let inner = binding.reads.without_slots(slots);
                    let read = inner.beside();
                    vars = merge_sorted(&vars, read.0);
                    primes = merge_sorted(&primes, read.1);
                    beside = merge_sorted(&beside, read.2);
                    bindings = merge_bindings(&bindings, read.3);
                } else {
                    bindings = merge_bindings(&bindings, std::slice::from_ref(binding));
                }
            }
            (!bindings.is_empty()).then(|| {
                Arc::new(Through {
                    vars,
                    primes,
                    slots: beside,
                    bindings,
                })
            })
        });
        Footprint {
            vars: self.vars.clone(),
            primes: self.primes.clone(),
            slots: kept(&self.slots),
            through,
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
            through: None,
        };
        let right = Footprint {
            vars: vec![2, 3, 6],
            primes: vec![4],
            slots: vec![2, 9],
            through: None,
        };
        let merged = left.merge(&right);
        assert_eq!(merged.vars, vec![1, 2, 3, 5, 6]);
        assert_eq!(merged.primes, vec![4]);
        assert_eq!(merged.slots, vec![2, 9]);
        assert_eq!(merged.without_slots(&[9]).slots, vec![2]);
        assert!(left.without_slots(&[2]).is_within(&merged));
    }

    #[test]
    fn a_name_bound_once_stands_for_what_it_reads_until_a_slot_it_reads_is_bound() {
        let reads = Footprint {
            vars: vec![4],
            primes: vec![],
            slots: vec![7, 8],
            through: None,
        };
        let name = Footprint::binding(3, &reads);
        assert_eq!(name, reads);
        assert!(name.is_binding());
        let user = name.merge(&Footprint::var(1)).merge(&Footprint::slot(8));
        assert_eq!(user.vars, vec![1, 4]);
        assert!(!user.is_binding());
        let through = user.through.clone().expect("the name it reads");
        assert_eq!(
            (&through.vars[..], &through.slots[..], through.width()),
            (&[1][..], &[8][..], 3)
        );
        let outside = user.without_slots(&[9]);
        assert_eq!(outside.through.expect("still the name").bindings.len(), 1);
        let bound = user.without_slots(&[7]);
        assert_eq!((&bound.vars[..], &bound.slots[..]), (&[1, 4][..], &[8][..]));
        assert!(bound.through.is_none());
        assert!(user.direct().through.is_none());
    }
}
