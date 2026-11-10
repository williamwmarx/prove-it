//! Ported from Z3 (src/util/hashtable.h, src/util/obj_hashtable.h), MIT license, through
//! `hashtable.ts`. Z3's open-addressing table with linear probing. Its iteration order is the slot
//! order, which the model finder depends on, so the AST maps that Z3 iterates use this table.
//!
//! The TypeScript table takes a hash function when it is made; here every call that looks up a key
//! takes the key's hash, which the table keeps beside the key, as Z3's hash entries do, to place it
//! again when it grows. The hash of a key must not change while the key is in the table.

const INITIAL_CAPACITY: usize = 8;
const SMALL_TABLE_CAPACITY: usize = 64;

#[derive(Clone, Copy, PartialEq, Eq)]
enum State {
    Free,
    Deleted,
    Used,
}

/// u_hash: an unsigned key is its own hash.
pub fn get_identity_hash(key: u32) -> u32 {
    key
}

/// obj_map from AST ids (or any `u32` key) to values.
#[derive(Clone)]
pub struct ObjMap<V> {
    states: Vec<State>,
    slots: Vec<Option<(u32, u32, V)>>,
    num_deleted: usize,
    size: usize,
}

impl<V> Default for ObjMap<V> {
    fn default() -> Self {
        ObjMap::new()
    }
}

impl<V> ObjMap<V> {
    pub fn new() -> ObjMap<V> {
        ObjMap {
            states: vec![State::Free; INITIAL_CAPACITY],
            slots: (0..INITIAL_CAPACITY).map(|_| None).collect(),
            num_deleted: 0,
            size: 0,
        }
    }

    pub fn len(&self) -> usize {
        self.size
    }

    pub fn is_empty(&self) -> bool {
        self.size == 0
    }

    fn capacity(&self) -> usize {
        self.states.len()
    }

    fn find_slot(&self, key: u32, hash: u32) -> Option<usize> {
        let mask = self.capacity() - 1;
        let begin = hash as usize & mask;
        for offset in 0..self.capacity() {
            let slot = (begin + offset) & mask;
            match self.states[slot] {
                State::Free => return None,
                State::Used
                    if self.slots[slot]
                        .as_ref()
                        .is_some_and(|entry| entry.0 == key) =>
                {
                    return Some(slot);
                }
                _ => {}
            }
        }
        None
    }

    /// move_table: reinserts the used slots, in slot order, into a table of the new capacity.
    fn move_table(&mut self, capacity: usize) {
        let states = std::mem::replace(&mut self.states, vec![State::Free; capacity]);
        let slots = std::mem::replace(&mut self.slots, (0..capacity).map(|_| None).collect());
        self.num_deleted = 0;
        let mask = capacity - 1;
        for (state, entry) in states.into_iter().zip(slots) {
            if state != State::Used {
                continue;
            }
            let Some(entry) = entry else { continue };
            let mut target = entry.1 as usize & mask;
            while self.states[target] != State::Free {
                target = (target + 1) & mask;
            }
            self.states[target] = State::Used;
            self.slots[target] = Some(entry);
        }
    }

    pub fn contains_key(&self, key: u32, hash: u32) -> bool {
        self.find_slot(key, hash).is_some()
    }

    pub fn get(&self, key: u32, hash: u32) -> Option<&V> {
        let slot = self.find_slot(key, hash)?;
        self.slots[slot].as_ref().map(|entry| &entry.2)
    }

    pub fn get_mut(&mut self, key: u32, hash: u32) -> Option<&mut V> {
        let slot = self.find_slot(key, hash)?;
        self.slots[slot].as_mut().map(|entry| &mut entry.2)
    }

    /// find_core and an assignment to the entry: unlike `insert`, never grows the table.
    pub fn replace(&mut self, key: u32, hash: u32, value: V) {
        if let Some(entry) = self.get_mut(key, hash) {
            *entry = value;
        }
    }

    /// `set`: inserts or overwrites, growing the table first when it is three quarters full.
    pub fn insert(&mut self, key: u32, hash: u32, value: V) {
        if (self.size + self.num_deleted) << 2 > self.capacity() * 3 {
            self.move_table(self.capacity() << 1);
        }
        let mask = self.capacity() - 1;
        let begin = hash as usize & mask;
        let mut deleted_slot = None;
        for offset in 0..self.capacity() {
            let slot = (begin + offset) & mask;
            match self.states[slot] {
                State::Used => {
                    if let Some(entry) = self.slots[slot].as_mut()
                        && entry.0 == key
                    {
                        entry.2 = value;
                        return;
                    }
                }
                State::Free => {
                    let target = deleted_slot.unwrap_or(slot);
                    if deleted_slot.is_some() {
                        self.num_deleted -= 1;
                    }
                    self.states[target] = State::Used;
                    self.slots[target] = Some((key, hash, value));
                    self.size += 1;
                    return;
                }
                State::Deleted => deleted_slot = Some(slot),
            }
        }
        // The growth above leaves a free slot, so the probe always ends at one.
        unreachable!("the hash table is full");
    }

    /// `delete`.
    pub fn remove(&mut self, key: u32, hash: u32) {
        let Some(slot) = self.find_slot(key, hash) else {
            return;
        };
        self.size -= 1;
        self.slots[slot] = None;
        if self.states[(slot + 1) & (self.capacity() - 1)] == State::Free {
            self.states[slot] = State::Free;
            return;
        }
        self.states[slot] = State::Deleted;
        self.num_deleted += 1;
        if self.num_deleted > self.size && self.num_deleted > SMALL_TABLE_CAPACITY {
            self.move_table(self.capacity());
        }
    }

    /// reset: empties the table, halving it when most slots were free.
    pub fn clear(&mut self) {
        if self.size == 0 && self.num_deleted == 0 {
            return;
        }
        let overhead = self
            .states
            .iter()
            .filter(|state| **state == State::Free)
            .count();
        let capacity = if self.capacity() > 16 && overhead << 2 > self.capacity() * 3 {
            self.capacity() >> 1
        } else {
            self.capacity()
        };
        self.states = vec![State::Free; capacity];
        self.slots = (0..capacity).map(|_| None).collect();
        self.size = 0;
        self.num_deleted = 0;
    }

    /// The entries in slot order.
    pub fn iter(&self) -> impl Iterator<Item = (u32, &V)> {
        self.slots
            .iter()
            .filter_map(|entry| entry.as_ref().map(|entry| (entry.0, &entry.2)))
    }

    /// The entries in slot order, values mutable.
    pub fn iter_mut(&mut self) -> impl Iterator<Item = (u32, &mut V)> {
        self.slots
            .iter_mut()
            .filter_map(|entry| entry.as_mut().map(|entry| (entry.0, &mut entry.2)))
    }

    /// The keys in slot order.
    pub fn keys(&self) -> impl Iterator<Item = u32> + '_ {
        self.iter().map(|(key, _)| key)
    }
}

/// obj_hashtable: a set of ASTs in Z3's slot order.
#[derive(Clone, Default)]
pub struct ObjHashtable {
    map: ObjMap<()>,
}

impl ObjHashtable {
    pub fn new() -> ObjHashtable {
        ObjHashtable { map: ObjMap::new() }
    }

    pub fn len(&self) -> usize {
        self.map.len()
    }

    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    pub fn contains(&self, key: u32, hash: u32) -> bool {
        self.map.contains_key(key, hash)
    }

    pub fn insert(&mut self, key: u32, hash: u32) {
        self.map.insert(key, hash, ());
    }

    pub fn remove(&mut self, key: u32, hash: u32) {
        self.map.remove(key, hash);
    }

    /// The keys in slot order.
    pub fn iter(&self) -> impl Iterator<Item = u32> + '_ {
        self.map.keys()
    }
}
