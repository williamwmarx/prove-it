//! Caches of pure computations keyed by the ids of what they read, as `src/engine/memo.ts` keeps
//! them: a [`MemoTable`] of one to six keys, and an [`EpochCache`] for an expression that reads
//! many variables of the current state but no primed one. A table that hits too rarely turns
//! itself off after [`PROBATION`] lookups, as the TypeScript tables do.

use tla_values::Id;

/// An empty entry, which no id is: ids count up from 0 and stop well short of it.
pub const EMPTY: Id = u32::MAX;

const PROBATION: u64 = 1 << 13;
const MINIMUM_HIT_RATE: f64 = 0.2;
const MAXIMUM_ENTRIES: usize = 1 << 22;
// A table of width 1 indexes its values by its key while it has at least one entry for every
// DIRECT_SPARSITY ids its array spans past the first DIRECT_MINIMUM, and never past
// DIRECT_MAXIMUM ids.
const DIRECT_SPARSITY: usize = 16;
const DIRECT_MINIMUM: usize = 1 << 16;
const DIRECT_MAXIMUM: usize = 1 << 23;

const OFFSET_BASIS: u32 = 0x811c_9dc5;

#[inline(always)]
fn fold(hash: u32, key: Id) -> u32 {
    (hash ^ key).wrapping_mul(0x0100_0193)
}

#[inline(always)]
fn hash_keys(keys: &[Id]) -> u32 {
    keys.iter().fold(OFFSET_BASIS, |hash, &key| fold(hash, key))
}

/// One entry of a table of width one or two: its keys packed in one word, so a probe compares
/// once, beside its value.
#[derive(Clone, Copy)]
struct Packed {
    key: u64,
    value: Id,
}

const EMPTY_PACKED: Packed = Packed {
    key: 0,
    value: EMPTY,
};

#[inline(always)]
fn pack(keys: &[Id]) -> u64 {
    match keys {
        [first] => u64::from(*first),
        [first, second] => u64::from(*first) | u64::from(*second) << 32,
        _ => unreachable!("packing more than two keys"),
    }
}

#[inline(always)]
fn mix(key: u64) -> usize {
    (key.wrapping_mul(0x9e37_79b9_7f4a_7c15) >> 32) as usize
}

#[inline(always)]
fn wide_home(keys: &[Id]) -> usize {
    let hash = hash_keys(keys);
    (hash ^ (hash >> 15)) as usize
}

/// A table of the values of one expression, keyed by the ids it reads.
pub struct MemoTable {
    width: usize,
    // A table of width 1 is keyed by one id, so while its keys are dense enough its values are an
    // array indexed by the id, read without hashing or probing.
    direct: Vec<Id>,
    // Width 1 once it isn't direct, and width 2: open addressing over packed keys.
    packed: Vec<Packed>,
    // Widths 3 to 6: open addressing over rows of the value, then the keys.
    wide: Vec<Id>,
    mask: usize,
    size: usize,
    lookups: u64,
    hits: u64,
    is_enabled: bool,
    is_direct: bool,
    // The largest id stored since the table last forgot, so that it forgets only if it must.
    largest: Id,
}

const INITIAL_CAPACITY: usize = 64;

impl MemoTable {
    pub fn new(width: usize) -> MemoTable {
        MemoTable {
            width,
            direct: if width == 1 {
                vec![EMPTY; INITIAL_CAPACITY]
            } else {
                Vec::new()
            },
            packed: if width == 2 {
                vec![EMPTY_PACKED; INITIAL_CAPACITY]
            } else {
                Vec::new()
            },
            wide: if width > 2 {
                vec![EMPTY; INITIAL_CAPACITY * (width + 1)]
            } else {
                Vec::new()
            },
            mask: INITIAL_CAPACITY - 1,
            size: 0,
            lookups: 0,
            hits: 0,
            is_enabled: true,
            is_direct: width == 1,
            largest: 0,
        }
    }

    pub fn width(&self) -> usize {
        self.width
    }

    pub fn is_enabled(&self) -> bool {
        self.is_enabled
    }

    pub fn size(&self) -> usize {
        self.size
    }

    pub fn lookups(&self) -> u64 {
        self.lookups
    }

    pub fn hits(&self) -> u64 {
        self.hits
    }

    fn capacity(&self) -> usize {
        self.mask + 1
    }

    fn grow(&mut self) {
        let capacity = self.capacity() * 2;
        self.mask = capacity - 1;
        if self.width <= 2 {
            let old = std::mem::replace(&mut self.packed, vec![EMPTY_PACKED; capacity]);
            for entry in old.into_iter().filter(|entry| entry.value != EMPTY) {
                let slot = self.free_packed(entry.key);
                self.packed[slot] = entry;
            }
            return;
        }
        let stride = self.width + 1;
        let old = std::mem::replace(&mut self.wide, vec![EMPTY; capacity * stride]);
        for row in old.chunks_exact(stride).filter(|row| row[0] != EMPTY) {
            let slot = self.free_wide(&row[1..]);
            self.wide[slot * stride..(slot + 1) * stride].copy_from_slice(row);
        }
    }

    fn free_packed(&self, key: u64) -> usize {
        let mut slot = mix(key) & self.mask;
        while self.packed[slot].value != EMPTY {
            slot = (slot + 1) & self.mask;
        }
        slot
    }

    fn free_wide(&self, keys: &[Id]) -> usize {
        let stride = self.width + 1;
        let mut slot = wide_home(keys) & self.mask;
        while self.wide[slot * stride] != EMPTY {
            slot = (slot + 1) & self.mask;
        }
        slot
    }

    // Grows a direct table's array to hold the id, or makes the table a hash table when its keys
    // are too sparse for the array that would take.
    fn reserve_direct(&mut self, id: Id) {
        let capacity = (2 * self.direct.len()).max(id as usize + 1);
        if capacity <= DIRECT_MAXIMUM && capacity <= DIRECT_SPARSITY * self.size + DIRECT_MINIMUM {
            self.direct.resize(capacity, EMPTY);
            return;
        }
        let direct = std::mem::take(&mut self.direct);
        self.is_direct = false;
        self.size = 0;
        self.mask = INITIAL_CAPACITY - 1;
        self.packed = vec![EMPTY_PACKED; INITIAL_CAPACITY];
        for (key, &value) in direct.iter().enumerate() {
            if value != EMPTY {
                self.set(&[key as Id], value);
            }
        }
    }

    // Counts a lookup, and says whether the table is on once its probation ends.
    #[inline(always)]
    fn open(&mut self) -> bool {
        self.lookups += 1;
        if self.lookups == PROBATION && (self.hits as f64) < self.lookups as f64 * MINIMUM_HIT_RATE
        {
            self.is_enabled = false;
            self.direct = Vec::new();
            self.packed = Vec::new();
            self.wide = Vec::new();
        }
        self.is_enabled
    }

    // Makes room for a new entry, or says the table takes no more.
    fn claim(&mut self) -> bool {
        if !self.is_enabled || self.size >= MAXIMUM_ENTRIES {
            return false;
        }
        if (self.size + 1) * 2 > self.capacity() {
            self.grow();
        }
        self.size += 1;
        true
    }

    /// Forgets every entry that reads or holds an id from `bound` on, ids a store has let go of.
    pub fn forget_from(&mut self, bound: Id) {
        if self.largest < bound {
            return;
        }
        // What is kept is below the bound, which a later, lower bound may still have to forget.
        self.largest = bound.saturating_sub(1);
        if self.is_direct {
            self.direct.truncate(bound as usize);
            for value in self.direct.iter_mut().filter(|value| **value >= bound) {
                *value = EMPTY;
            }
            self.size = self.direct.iter().filter(|&&value| value != EMPTY).count();
            return;
        }
        let capacity = self.capacity();
        self.size = 0;
        if self.width <= 2 {
            let old = std::mem::replace(&mut self.packed, vec![EMPTY_PACKED; capacity]);
            for entry in old {
                if entry.value < bound
                    && (entry.key as Id) < bound
                    && ((entry.key >> 32) as Id) < bound
                {
                    let slot = self.free_packed(entry.key);
                    self.packed[slot] = entry;
                    self.size += 1;
                }
            }
            return;
        }
        let stride = self.width + 1;
        let old = std::mem::replace(&mut self.wide, vec![EMPTY; capacity * stride]);
        for row in old.chunks_exact(stride) {
            if row.iter().all(|&id| id < bound) {
                let slot = self.free_wide(&row[1..]);
                self.wide[slot * stride..(slot + 1) * stride].copy_from_slice(row);
                self.size += 1;
            }
        }
    }

    /// The value stored for the keys, or [`EMPTY`].
    #[inline]
    pub fn get(&mut self, keys: &[Id]) -> Id {
        if !self.open() {
            return EMPTY;
        }
        let value = if self.is_direct {
            self.direct.get(keys[0] as usize).copied().unwrap_or(EMPTY)
        } else if self.width <= 2 {
            let key = pack(keys);
            let mut slot = mix(key) & self.mask;
            loop {
                let entry = self.packed[slot];
                if entry.value == EMPTY || entry.key == key {
                    break entry.value;
                }
                slot = (slot + 1) & self.mask;
            }
        } else {
            let stride = self.width + 1;
            let mut slot = wide_home(keys) & self.mask;
            loop {
                let row = &self.wide[slot * stride..(slot + 1) * stride];
                // Compared key by key, which beats a call to memcmp for six keys or fewer.
                if row[0] == EMPTY || row[1..].iter().zip(keys).all(|(stored, key)| stored == key) {
                    break row[0];
                }
                slot = (slot + 1) & self.mask;
            }
        };
        if value != EMPTY {
            self.hits += 1;
        }
        value
    }

    /// Stores a value for the keys, unless the table is off or full.
    pub fn set(&mut self, keys: &[Id], value: Id) {
        self.largest = keys
            .iter()
            .fold(self.largest.max(value), |largest, &key| largest.max(key));
        if self.is_direct {
            if !self.is_enabled || self.size >= MAXIMUM_ENTRIES {
                return;
            }
            let key = keys[0];
            if key as usize >= self.direct.len() {
                self.reserve_direct(key);
            }
            if self.is_direct {
                if self.direct[key as usize] == EMPTY {
                    self.size += 1;
                }
                self.direct[key as usize] = value;
                return;
            }
        }
        if !self.claim() {
            return;
        }
        if self.width <= 2 {
            let key = pack(keys);
            let slot = self.free_packed(key);
            self.packed[slot] = Packed { key, value };
            return;
        }
        let stride = self.width + 1;
        let slot = self.free_wide(keys);
        let row = &mut self.wide[slot * stride..(slot + 1) * stride];
        row[0] = value;
        row[1..].copy_from_slice(keys);
    }
}

const EPOCH_ENTRIES: usize = 64;
const EPOCH_MINIMUM_HIT_RATE: f64 = 0.1;
/// How many bound names an epoch cache keys its entries by.
pub const EPOCH_KEYS: usize = 4;

/// A cache of an expression that reads too many state variables for a memo table, but no primed
/// ones, while one state is current. Its value is then a function of the bound names it reads, up
/// to four, which key its entries; an entry from an earlier current state doesn't match. Entries
/// are direct-mapped: a collision overwrites.
pub struct EpochCache {
    epochs: [u64; EPOCH_ENTRIES],
    keys: [[Id; EPOCH_KEYS]; EPOCH_ENTRIES],
    values: [Id; EPOCH_ENTRIES],
    lookups: u64,
    hits: u64,
    is_enabled: bool,
}

impl Default for EpochCache {
    fn default() -> EpochCache {
        EpochCache {
            epochs: [0; EPOCH_ENTRIES],
            keys: [[0; EPOCH_KEYS]; EPOCH_ENTRIES],
            values: [EMPTY; EPOCH_ENTRIES],
            lookups: 0,
            hits: 0,
            is_enabled: true,
        }
    }
}

impl EpochCache {
    pub fn is_enabled(&self) -> bool {
        self.is_enabled
    }

    /// The entry for the keys, where the keys past the bound names read are 0.
    pub fn entry(keys: &[Id; EPOCH_KEYS]) -> usize {
        let hash = hash_keys(keys);
        (hash ^ (hash >> 15)) as usize & (EPOCH_ENTRIES - 1)
    }

    pub fn get(&mut self, epoch: u64, entry: usize, keys: &[Id; EPOCH_KEYS]) -> Id {
        // A cache whose expression is evaluated about once per state only costs.
        self.lookups += 1;
        if self.lookups == PROBATION
            && (self.hits as f64) < self.lookups as f64 * EPOCH_MINIMUM_HIT_RATE
        {
            self.is_enabled = false;
        }
        if self.epochs[entry] != epoch || &self.keys[entry] != keys {
            return EMPTY;
        }
        self.hits += 1;
        self.values[entry]
    }

    pub fn set(&mut self, epoch: u64, entry: usize, keys: &[Id; EPOCH_KEYS], value: Id) {
        self.epochs[entry] = epoch;
        self.keys[entry] = *keys;
        self.values[entry] = value;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stores_and_finds_values_of_every_width() {
        for width in 1..=6 {
            let mut table = MemoTable::new(width);
            for key in 0..1000u32 {
                let keys: Vec<Id> = (0..width as u32).map(|index| key * 7 + index).collect();
                assert_eq!(table.get(&keys), EMPTY);
                table.set(&keys, key);
            }
            for key in 0..1000u32 {
                let keys: Vec<Id> = (0..width as u32).map(|index| key * 7 + index).collect();
                assert_eq!(table.get(&keys), key);
            }
        }
    }

    #[test]
    fn tells_apart_keys_that_differ_only_after_the_first() {
        for width in 2..=6 {
            let mut table = MemoTable::new(width);
            let keys = |first: u32, last: u32| {
                let mut keys = vec![first; width];
                keys[width - 1] = last;
                keys
            };
            for first in 0..40u32 {
                for last in 0..40u32 {
                    table.set(&keys(first, last), first * 40 + last);
                }
            }
            for first in 0..40u32 {
                for last in 0..40u32 {
                    assert_eq!(table.get(&keys(first, last)), first * 40 + last);
                }
            }
            assert_eq!(table.size(), 1600);
        }
    }

    #[test]
    fn a_sparse_direct_table_becomes_a_hash_table() {
        let mut table = MemoTable::new(1);
        table.set(&[5], 1);
        table.set(&[DIRECT_MAXIMUM as Id + 10], 2);
        for key in 100..200 {
            table.set(&[key * 1_000_003], key);
        }
        assert!(!table.is_direct);
        assert_eq!(table.get(&[5]), 1);
        assert_eq!(table.get(&[DIRECT_MAXIMUM as Id + 10]), 2);
        for key in 100..200 {
            assert_eq!(table.get(&[key * 1_000_003]), key);
        }
        assert_eq!(table.size(), 102);
    }

    #[test]
    fn a_table_that_rarely_hits_turns_off() {
        let mut table = MemoTable::new(2);
        for key in 0..PROBATION as u32 {
            assert_eq!(table.get(&[key, key]), EMPTY);
            table.set(&[key, key], key);
        }
        assert!(!table.is_enabled());
        assert_eq!(table.get(&[0, 0]), EMPTY);
    }

    #[test]
    fn forgets_only_the_entries_that_read_or_hold_forgotten_ids() {
        for width in 1..=6 {
            let mut table = MemoTable::new(width);
            let keys = |key: u32| vec![key; width];
            for key in 0..100u32 {
                table.set(&keys(key), 99 - key);
            }
            table.forget_from(60);
            for key in 0..100u32 {
                let expected = if key < 60 && 99 - key < 60 {
                    99 - key
                } else {
                    EMPTY
                };
                assert_eq!(table.get(&keys(key)), expected, "width {width}, key {key}");
            }
            assert_eq!(table.size(), 20);
            // Each entry kept reads or holds an id from 50 on.
            table.forget_from(50);
            for key in 0..100u32 {
                assert_eq!(table.get(&keys(key)), EMPTY, "width {width}, key {key}");
            }
            assert_eq!(table.size(), 0);
        }
    }

    #[test]
    fn an_epoch_cache_answers_only_for_its_epoch() {
        let mut cache = EpochCache::default();
        let keys = [3, 4, 0, 0];
        let entry = EpochCache::entry(&keys);
        cache.set(7, entry, &keys, 42);
        assert_eq!(cache.get(7, entry, &keys), 42);
        assert_eq!(cache.get(8, entry, &keys), EMPTY);
        assert_eq!(cache.get(7, entry, &[3, 5, 0, 0]), EMPTY);
    }
}
