//! A map that keeps its entries in the order they were first set, as a JavaScript `Map` does:
//! setting a key it holds keeps the key's place, and deleting a key and setting it again moves it
//! to the end. The TypeScript front end iterates its maps of symbols and definitions in that order,
//! and what it builds from them follows it.

use std::hash::Hash;

use crate::hash::FastMap;

#[derive(Clone, Debug)]
pub struct OrderedMap<K, V> {
    entries: Vec<Option<(K, V)>>,
    positions: FastMap<K, usize>,
}

impl<K, V> Default for OrderedMap<K, V> {
    fn default() -> Self {
        OrderedMap {
            entries: Vec::new(),
            positions: FastMap::default(),
        }
    }
}

impl<K: Hash + Eq + Clone, V> OrderedMap<K, V> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn len(&self) -> usize {
        self.positions.len()
    }

    pub fn is_empty(&self) -> bool {
        self.positions.is_empty()
    }

    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: std::borrow::Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let position = *self.positions.get(key)?;
        self.entries[position].as_ref().map(|entry| &entry.1)
    }

    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: std::borrow::Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let position = *self.positions.get(key)?;
        self.entries[position].as_mut().map(|entry| &mut entry.1)
    }

    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: std::borrow::Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.positions.contains_key(key)
    }

    pub fn insert(&mut self, key: K, value: V) {
        match self.positions.get(&key) {
            Some(&position) => self.entries[position] = Some((key, value)),
            None => {
                self.positions.insert(key.clone(), self.entries.len());
                self.entries.push(Some((key, value)));
            }
        }
    }

    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: std::borrow::Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let position = self.positions.remove(key)?;
        self.entries[position].take().map(|entry| entry.1)
    }

    pub fn iter(&self) -> impl Iterator<Item = (&K, &V)> {
        self.entries
            .iter()
            .filter_map(|entry| entry.as_ref().map(|(key, value)| (key, value)))
    }

    pub fn keys(&self) -> impl Iterator<Item = &K> {
        self.iter().map(|entry| entry.0)
    }

    pub fn values(&self) -> impl Iterator<Item = &V> {
        self.iter().map(|entry| entry.1)
    }

    pub fn values_mut(&mut self) -> impl Iterator<Item = &mut V> {
        self.entries
            .iter_mut()
            .filter_map(|entry| entry.as_mut().map(|(_, value)| value))
    }
}

impl<K: Hash + Eq + Clone, V> FromIterator<(K, V)> for OrderedMap<K, V> {
    fn from_iter<I: IntoIterator<Item = (K, V)>>(entries: I) -> Self {
        let mut map = OrderedMap::new();
        for (key, value) in entries {
            map.insert(key, value);
        }
        map
    }
}
