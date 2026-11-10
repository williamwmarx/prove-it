//! A map and a set that iterate in the order their keys were first set, as JavaScript's `Map` and
//! `Set` do, for every `Map` or `Set` of the TypeScript solver that is iterated, spread or turned
//! into an array (design/prover.md 4a). Setting a key it holds keeps the key's place; deleting a
//! key and setting it again moves it to the end. Deleted entries leave holes that iteration skips,
//! and the holes are compacted away once they outnumber the entries.

use std::borrow::Borrow;
use std::collections::HashMap;
use std::hash::Hash;

const MIN_COMPACTED_HOLES: usize = 32;

#[derive(Clone, Debug)]
pub struct OrderedMap<K, V> {
    entries: Vec<Option<(K, V)>>,
    /// Only looked up, never iterated.
    positions: HashMap<K, usize>,
}

impl<K, V> Default for OrderedMap<K, V> {
    fn default() -> Self {
        OrderedMap {
            entries: Vec::new(),
            positions: HashMap::new(),
        }
    }
}

impl<K: Hash + Eq + Clone, V> OrderedMap<K, V> {
    pub fn new() -> Self {
        Self::default()
    }

    /// `size`.
    pub fn len(&self) -> usize {
        self.positions.len()
    }

    pub fn is_empty(&self) -> bool {
        self.positions.is_empty()
    }

    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let position = *self.positions.get(key)?;
        self.entries[position].as_ref().map(|entry| &entry.1)
    }

    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let position = *self.positions.get(key)?;
        self.entries[position].as_mut().map(|entry| &mut entry.1)
    }

    /// `has`.
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.positions.contains_key(key)
    }

    /// `set`: a key it holds keeps its place.
    pub fn insert(&mut self, key: K, value: V) {
        if let Some(entry) = self.get_mut(&key) {
            *entry = value;
            return;
        }
        self.positions.insert(key.clone(), self.entries.len());
        self.entries.push(Some((key, value)));
    }

    /// The value of a key, set to `make()` first when it has none.
    pub fn get_or_insert_with(&mut self, key: K, make: impl FnOnce() -> V) -> &mut V {
        let position = match self.positions.get(&key) {
            Some(position) => *position,
            None => {
                let position = self.entries.len();
                self.positions.insert(key.clone(), position);
                self.entries.push(Some((key, make())));
                position
            }
        };
        self.entries[position]
            .as_mut()
            .map(|entry| &mut entry.1)
            .expect("a key's position holds its entry")
    }

    /// `delete`.
    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let position = self.positions.remove(key)?;
        let value = self.entries[position].take().map(|entry| entry.1);
        let holes = self.entries.len() - self.positions.len();
        if holes > MIN_COMPACTED_HOLES && holes > self.positions.len() {
            self.compact();
        }
        value
    }

    fn compact(&mut self) {
        self.entries.retain(Option::is_some);
        for (position, entry) in self.entries.iter().enumerate() {
            if let Some((key, _)) = entry
                && let Some(slot) = self.positions.get_mut(key)
            {
                *slot = position;
            }
        }
    }

    pub fn clear(&mut self) {
        self.entries.clear();
        self.positions.clear();
    }

    /// The entries in the order their keys were first set.
    pub fn iter(&self) -> impl DoubleEndedIterator<Item = (&K, &V)> {
        self.entries
            .iter()
            .filter_map(|entry| entry.as_ref().map(|(key, value)| (key, value)))
    }

    pub fn iter_mut(&mut self) -> impl DoubleEndedIterator<Item = (&K, &mut V)> {
        self.entries
            .iter_mut()
            .filter_map(|entry| entry.as_mut().map(|(key, value)| (&*key, value)))
    }

    pub fn keys(&self) -> impl DoubleEndedIterator<Item = &K> {
        self.iter().map(|(key, _)| key)
    }

    pub fn values(&self) -> impl DoubleEndedIterator<Item = &V> {
        self.iter().map(|(_, value)| value)
    }

    pub fn values_mut(&mut self) -> impl DoubleEndedIterator<Item = &mut V> {
        self.iter_mut().map(|(_, value)| value)
    }

    /// The first entry, as `map.entries().next()`.
    pub fn first(&self) -> Option<(&K, &V)> {
        self.iter().next()
    }
}

/// A JavaScript `Set` that is iterated: an `OrderedMap` to nothing.
#[derive(Clone, Debug)]
pub struct OrderedSet<K> {
    map: OrderedMap<K, ()>,
}

impl<K> Default for OrderedSet<K> {
    fn default() -> Self {
        OrderedSet {
            map: OrderedMap::default(),
        }
    }
}

impl<K: Hash + Eq + Clone> OrderedSet<K> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn len(&self) -> usize {
        self.map.len()
    }

    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// `has`.
    pub fn contains<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.map.contains_key(key)
    }

    /// `add`: returns whether the key is new.
    pub fn insert(&mut self, key: K) -> bool {
        if self.map.contains_key(&key) {
            return false;
        }
        self.map.insert(key, ());
        true
    }

    /// `delete`: returns whether the key was there.
    pub fn remove<Q>(&mut self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.map.remove(key).is_some()
    }

    pub fn clear(&mut self) {
        self.map.clear();
    }

    pub fn iter(&self) -> impl DoubleEndedIterator<Item = &K> {
        self.map.keys()
    }

    pub fn first(&self) -> Option<&K> {
        self.map.first().map(|(key, _)| key)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn keys_keep_the_order_javascript_gives_them() {
        let mut map = OrderedMap::new();
        for key in [5, 1, 9, 3] {
            map.insert(key, key * 10);
        }
        map.insert(1, 11);
        assert!(map.remove(&9).is_some());
        map.insert(9, 90);
        assert_eq!(
            map.iter()
                .map(|(key, value)| (*key, *value))
                .collect::<Vec<_>>(),
            [(5, 50), (1, 11), (3, 30), (9, 90)]
        );
    }

    #[test]
    fn compaction_keeps_the_order_and_the_lookups() {
        let mut map = OrderedMap::new();
        for key in 0..200 {
            map.insert(key, key);
        }
        for key in (0..200).filter(|key| key % 5 != 0) {
            map.remove(&key);
        }
        map.insert(3, 3);
        let expected: Vec<i32> = (0..200).filter(|key| key % 5 == 0).chain([3]).collect();
        assert_eq!(map.keys().copied().collect::<Vec<_>>(), expected);
        assert!(expected.iter().all(|key| map.get(key) == Some(key)));
        assert!(map.entries.len() < 100);
    }

    #[test]
    fn a_set_adds_a_key_once() {
        let mut set = OrderedSet::new();
        assert!(set.insert("b"));
        assert!(set.insert("a"));
        assert!(!set.insert("b"));
        assert!(set.remove("b"));
        assert!(set.insert("b"));
        assert_eq!(set.iter().copied().collect::<Vec<_>>(), ["a", "b"]);
    }
}
