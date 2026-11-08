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

/// A table of the values of one expression, keyed by the ids it reads.
pub struct MemoTable {
    width: usize,
    keys: Vec<Id>,
    values: Vec<Id>,
    mask: usize,
    size: usize,
    lookups: u64,
    hits: u64,
    is_enabled: bool,
    // A table of width 1 is keyed by one id, so while its keys are dense enough its values are an
    // array indexed by the id, read without hashing or probing.
    is_direct: bool,
}

impl MemoTable {
    pub fn new(width: usize) -> MemoTable {
        let capacity = 64;
        MemoTable {
            width,
            keys: vec![0; capacity * width],
            values: vec![EMPTY; capacity],
            mask: capacity - 1,
            size: 0,
            lookups: 0,
            hits: 0,
            is_enabled: true,
            is_direct: width == 1,
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

    fn grow(&mut self) {
        let width = self.width;
        let old_keys = std::mem::take(&mut self.keys);
        let old_values = std::mem::take(&mut self.values);
        let capacity = old_values.len() * 2;
        self.keys = vec![0; capacity * width];
        self.values = vec![EMPTY; capacity];
        self.mask = capacity - 1;
        for (entry, &value) in old_values.iter().enumerate() {
            if value == EMPTY {
                continue;
            }
            let key = &old_keys[entry * width..(entry + 1) * width];
            let hash = hash_keys(key);
            let mut slot = (hash ^ (hash >> 15)) as usize & self.mask;
            while self.values[slot] != EMPTY {
                slot = (slot + 1) & self.mask;
            }
            self.keys[slot * width..(slot + 1) * width].copy_from_slice(key);
            self.values[slot] = value;
        }
    }

    // Grows a direct table's array to hold the id, or makes the table a hash table when its keys
    // are too sparse for the array that would take.
    fn reserve_direct(&mut self, id: Id) {
        let capacity = (2 * self.values.len()).max(id as usize + 1);
        if capacity <= DIRECT_MAXIMUM && capacity <= DIRECT_SPARSITY * self.size + DIRECT_MINIMUM {
            self.values.resize(capacity, EMPTY);
            return;
        }
        let direct = std::mem::take(&mut self.values);
        self.is_direct = false;
        self.size = 0;
        self.values = vec![EMPTY; self.keys.len()];
        for (key, &value) in direct.iter().enumerate() {
            if value != EMPTY {
                self.set(&[key as Id], value);
            }
        }
    }

    // Counts a lookup, and says whether the table is on once its probation ends.
    fn open(&mut self) -> bool {
        self.lookups += 1;
        if self.lookups == PROBATION && (self.hits as f64) < self.lookups as f64 * MINIMUM_HIT_RATE
        {
            self.is_enabled = false;
            self.keys = Vec::new();
            self.values = Vec::new();
        }
        self.is_enabled
    }

    // The empty slot a new entry with this hash goes in, or None when the table takes no more.
    fn claim(&mut self, hash: u32) -> Option<usize> {
        if !self.is_enabled || self.size >= MAXIMUM_ENTRIES {
            return None;
        }
        if (self.size + 1) * 2 > self.values.len() {
            self.grow();
        }
        let mut slot = (hash ^ (hash >> 15)) as usize & self.mask;
        while self.values[slot] != EMPTY {
            slot = (slot + 1) & self.mask;
        }
        self.size += 1;
        Some(slot)
    }

    /// The value stored for the keys, or [`EMPTY`].
    #[inline]
    pub fn get(&mut self, keys: &[Id]) -> Id {
        if !self.open() {
            return EMPTY;
        }
        if self.is_direct {
            let value = self.values.get(keys[0] as usize).copied().unwrap_or(EMPTY);
            if value != EMPTY {
                self.hits += 1;
            }
            return value;
        }
        let width = self.width;
        let hash = hash_keys(keys);
        let mut slot = (hash ^ (hash >> 15)) as usize & self.mask;
        loop {
            let value = self.values[slot];
            if value == EMPTY {
                return EMPTY;
            }
            if &self.keys[slot * width..(slot + 1) * width] == keys {
                self.hits += 1;
                return value;
            }
            slot = (slot + 1) & self.mask;
        }
    }

    /// Stores a value for the keys, unless the table is off or full.
    pub fn set(&mut self, keys: &[Id], value: Id) {
        if self.is_direct {
            if !self.is_enabled || self.size >= MAXIMUM_ENTRIES {
                return;
            }
            let key = keys[0];
            if key as usize >= self.values.len() {
                self.reserve_direct(key);
            }
            if self.is_direct {
                if self.values[key as usize] == EMPTY {
                    self.size += 1;
                }
                self.values[key as usize] = value;
                return;
            }
        }
        let Some(slot) = self.claim(hash_keys(keys)) else {
            return;
        };
        let width = self.width;
        self.keys[slot * width..(slot + 1) * width].copy_from_slice(keys);
        self.values[slot] = value;
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
    fn a_sparse_direct_table_becomes_a_hash_table() {
        let mut table = MemoTable::new(1);
        table.set(&[5], 1);
        table.set(&[DIRECT_MAXIMUM as Id + 10], 2);
        assert!(!table.is_direct);
        assert_eq!(table.get(&[5]), 1);
        assert_eq!(table.get(&[DIRECT_MAXIMUM as Id + 10]), 2);
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
