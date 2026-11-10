// Ported from Z3 (src/util/uint_set.h, src/util/heap.h, src/math/lp/stacked_vector.h), MIT
// license, see z3-license.txt. The containers whose iteration order the lp solver depends on.
use std::collections::HashMap;

// indexed_uint_set: insertion order, and a removal moves the last element into the gap.
#[derive(Default, Clone)]
pub struct IndexedUintSet {
    pub elems: Vec<usize>,
    // usize::MAX where TypeScript's array has a hole.
    positions: Vec<usize>,
}

impl IndexedUintSet {
    pub fn new() -> IndexedUintSet {
        IndexedUintSet::default()
    }

    pub fn size(&self) -> usize {
        self.elems.len()
    }

    pub fn has(&self, value: usize) -> bool {
        let position = self.positions.get(value).copied().unwrap_or(usize::MAX);
        position != usize::MAX && position < self.elems.len() && self.elems[position] == value
    }

    pub fn add(&mut self, value: usize) {
        if self.has(value) {
            return;
        }
        if self.positions.len() <= value {
            self.positions.resize(value + 1, usize::MAX);
        }
        self.positions[value] = self.elems.len();
        self.elems.push(value);
    }

    pub fn delete(&mut self, value: usize) {
        let last = *self
            .elems
            .last()
            .expect("an indexed set deletes from a nonempty set");
        if value != last {
            let position = self.positions[value];
            self.positions[last] = position;
            self.elems[position] = last;
            let last_position = self.elems.len() - 1;
            self.positions[value] = last_position;
            self.elems[last_position] = value;
        }
        self.elems.pop();
    }

    pub fn clear(&mut self) {
        self.elems.clear();
    }
}

// heap<lpvar_lt>: the infeasible columns, smallest first.
#[derive(Default)]
pub struct VarHeap {
    values: Vec<usize>,
    // usize::MAX for TypeScript's -1 and its holes.
    positions: Vec<usize>,
}

impl VarHeap {
    pub fn size(&self) -> usize {
        self.values.len()
    }

    pub fn has(&self, value: usize) -> bool {
        let position = self.positions.get(value).copied().unwrap_or(usize::MAX);
        position != usize::MAX && self.values.get(position) == Some(&value)
    }

    pub fn get_min(&self) -> usize {
        self.values[0]
    }

    pub fn iter(&self) -> impl Iterator<Item = usize> + '_ {
        self.values.iter().copied()
    }

    pub fn insert(&mut self, value: usize) {
        self.values.push(value);
        if self.positions.len() <= value {
            self.positions.resize(value + 1, usize::MAX);
        }
        self.positions[value] = self.values.len() - 1;
        self.move_up(self.values.len() - 1);
    }

    pub fn erase(&mut self, value: usize) {
        let position = self.positions[value];
        let last = self
            .values
            .pop()
            .expect("the heap erases from a nonempty heap");
        self.positions[value] = usize::MAX;
        if last == value {
            return;
        }
        self.values[position] = last;
        self.positions[last] = position;
        self.move_up(position);
        self.move_down(self.positions[last]);
    }

    pub fn clear(&mut self) {
        for value in &self.values {
            self.positions[*value] = usize::MAX;
        }
        self.values.clear();
    }

    fn swap(&mut self, first: usize, second: usize) {
        self.values.swap(first, second);
        self.positions[self.values[first]] = first;
        self.positions[self.values[second]] = second;
    }

    fn move_up(&mut self, start: usize) {
        let mut position = start;
        while position > 0 {
            let parent = (position - 1) >> 1;
            if self.values[parent] <= self.values[position] {
                return;
            }
            self.swap(parent, position);
            position = parent;
        }
    }

    fn move_down(&mut self, start: usize) {
        let mut position = start;
        loop {
            let left = 2 * position + 1;
            if left >= self.values.len() {
                return;
            }
            let right = left + 1;
            let child = if right < self.values.len() && self.values[right] < self.values[left] {
                right
            } else {
                left
            };
            if self.values[position] <= self.values[child] {
                return;
            }
            self.swap(position, child);
            position = child;
        }
    }
}

struct StackedLogEntry<T> {
    index: usize,
    value: T,
}

struct StackedScope {
    size: usize,
    log_size: usize,
}

// stacked_vector: a vector whose size and values a pop restores to the matching push.
pub struct StackedVector<T> {
    pub values: Vec<T>,
    log: Vec<StackedLogEntry<T>>,
    scopes: Vec<StackedScope>,
}

impl<T> Default for StackedVector<T> {
    fn default() -> StackedVector<T> {
        StackedVector {
            values: Vec::new(),
            log: Vec::new(),
            scopes: Vec::new(),
        }
    }
}

impl<T: Clone + PartialEq> StackedVector<T> {
    pub fn get(&self, index: usize) -> &T {
        &self.values[index]
    }

    pub fn set(&mut self, index: usize, value: T) {
        if self.values[index] == value {
            return;
        }
        if !self.scopes.is_empty() {
            self.log.push(StackedLogEntry {
                index,
                value: self.values[index].clone(),
            });
        }
        self.values[index] = value;
    }

    pub fn push(&mut self, value: T) {
        self.values.push(value);
    }

    pub fn push_scope(&mut self) {
        self.scopes.push(StackedScope {
            size: self.values.len(),
            log_size: self.log.len(),
        });
    }

    pub fn pop_scope(&mut self, count: usize) {
        let scope_index = self.scopes.len() - count;
        let size = self.scopes[scope_index].size;
        let log_size = self.scopes[scope_index].log_size;
        self.scopes.truncate(scope_index);
        self.values.truncate(size);
        for index in (log_size..self.log.len()).rev() {
            let entry = &self.log[index];
            if entry.index < self.values.len() {
                self.values[entry.index] = entry.value.clone();
            }
        }
        self.log.truncate(log_size);
    }
}

// The anchor of the node list, in the first slot of the links.
const ANCHOR: usize = 0;

struct HashLink<V> {
    key: usize,
    next: Option<usize>,
    // None for the anchor and for a free slot.
    value: Option<V>,
}

// __constrain_hash: a mask for a power of two bucket count, and a remainder otherwise.
fn get_bucket(hash: usize, count: usize) -> usize {
    if count & (count - 1) == 0 {
        hash & (count - 1)
    } else if hash < count {
        hash
    } else {
        hash % count
    }
}

fn is_hash_power_of_two(count: usize) -> bool {
    count > 2 && count & (count - 1) == 0
}

fn is_prime(value: usize) -> bool {
    let mut divisor = 2;
    while divisor * divisor <= value {
        if value.is_multiple_of(divisor) {
            return false;
        }
        divisor += 1;
    }
    value >= 2
}

fn get_next_prime(value: usize) -> usize {
    let mut candidate = value;
    while !is_prime(candidate) {
        candidate += 1;
    }
    candidate
}

// std::unordered_map<unsigned, V> of libc++, which Z3's release build on macOS uses: one list
// threads every node, each bucket points at the node before its first one, a new node goes to the
// front of its bucket, and the table grows to the next prime. The iteration order is the list.
// The nodes are slots of `links`, the anchor the first one; `nodes` finds the slot of a key.
pub struct UnorderedUintMap<V> {
    links: Vec<HashLink<V>>,
    free_links: Vec<usize>,
    buckets: Vec<Option<usize>>,
    nodes: HashMap<usize, usize>,
}

impl<V> Default for UnorderedUintMap<V> {
    fn default() -> UnorderedUintMap<V> {
        UnorderedUintMap {
            links: vec![HashLink {
                key: usize::MAX,
                next: None,
                value: None,
            }],
            free_links: Vec::new(),
            buckets: Vec::new(),
            nodes: HashMap::new(),
        }
    }
}

impl<V> UnorderedUintMap<V> {
    pub fn new() -> UnorderedUintMap<V> {
        UnorderedUintMap::default()
    }

    pub fn size(&self) -> usize {
        self.nodes.len()
    }

    pub fn has(&self, key: usize) -> bool {
        self.nodes.contains_key(&key)
    }

    pub fn get(&self, key: usize) -> Option<&V> {
        self.nodes
            .get(&key)
            .and_then(|link| self.links[*link].value.as_ref())
    }

    pub fn iter(&self) -> impl Iterator<Item = (usize, &V)> + '_ {
        let mut node = self.links[ANCHOR].next;
        std::iter::from_fn(move || {
            let link = &self.links[node?];
            node = link.next;
            Some((
                link.key,
                link.value.as_ref().expect("a node of the list has a value"),
            ))
        })
    }

    // __emplace_unique_key_args: the key is new.
    pub fn insert(&mut self, key: usize, value: V) {
        let link = HashLink {
            key,
            next: None,
            value: Some(value),
        };
        let node = match self.free_links.pop() {
            Some(slot) => {
                self.links[slot] = link;
                slot
            }
            None => {
                self.links.push(link);
                self.links.len() - 1
            }
        };
        let count = self.buckets.len();
        if self.nodes.len() + 1 > count || count == 0 {
            let grown = 2 * count + if is_hash_power_of_two(count) { 0 } else { 1 };
            self.rehash(grown.max(self.nodes.len() + 1));
        }
        self.nodes.insert(key, node);
        let bucket = get_bucket(key, self.buckets.len());
        if let Some(previous) = self.buckets[bucket] {
            self.links[node].next = self.links[previous].next;
            self.links[previous].next = Some(node);
            return;
        }
        self.links[node].next = self.links[ANCHOR].next;
        self.links[ANCHOR].next = Some(node);
        self.buckets[bucket] = Some(ANCHOR);
        if let Some(next) = self.links[node].next {
            let next_bucket = get_bucket(self.links[next].key, self.buckets.len());
            self.buckets[next_bucket] = Some(node);
        }
    }

    // remove: unlinks the node and repairs the buckets of it and of its successor.
    pub fn remove(&mut self, key: usize) {
        let Some(node) = self.nodes.remove(&key) else {
            return;
        };
        let count = self.buckets.len();
        let bucket = get_bucket(key, count);
        let mut previous = self.buckets[bucket].unwrap_or(ANCHOR);
        while self.links[previous].next != Some(node) {
            previous = self.links[previous].next.unwrap_or(ANCHOR);
        }
        let next = self.links[node].next;
        let is_previous_outside =
            previous == ANCHOR || get_bucket(self.links[previous].key, count) != bucket;
        if is_previous_outside
            && next.is_none_or(|next| get_bucket(self.links[next].key, count) != bucket)
        {
            self.buckets[bucket] = None;
        }
        if let Some(next) = next {
            let next_bucket = get_bucket(self.links[next].key, count);
            if next_bucket != bucket {
                self.buckets[next_bucket] = Some(previous);
            }
        }
        self.links[previous].next = next;
        self.links[node].value = None;
        self.links[node].next = None;
        self.free_links.push(node);
    }

    // clear keeps the bucket count.
    pub fn clear(&mut self) {
        self.links.truncate(1);
        self.links[ANCHOR].next = None;
        self.free_links.clear();
        self.buckets.fill(None);
        self.nodes.clear();
    }

    fn rehash(&mut self, requested: usize) {
        let count = if requested == 1 {
            2
        } else if requested & (requested - 1) == 0 {
            requested
        } else {
            get_next_prime(requested)
        };
        if count <= self.buckets.len() {
            return;
        }
        self.buckets = vec![None; count];
        let mut previous = ANCHOR;
        let Some(first) = self.links[previous].next else {
            return;
        };
        let mut previous_bucket = get_bucket(self.links[first].key, count);
        self.buckets[previous_bucket] = Some(previous);
        previous = first;
        let mut current = self.links[first].next;
        while let Some(node) = current {
            let bucket = get_bucket(self.links[node].key, count);
            if bucket == previous_bucket {
                previous = node;
            } else if let Some(head) = self.buckets[bucket] {
                self.links[previous].next = self.links[node].next;
                self.links[node].next = self.links[head].next;
                self.links[head].next = Some(node);
            } else {
                self.buckets[bucket] = Some(previous);
                previous = node;
                previous_bucket = bucket;
            }
            current = self.links[previous].next;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // The order comes from running the same steps through the TypeScript UnorderedUintMap.
    #[test]
    fn iterates_unordered_map_in_libcxx_order() {
        let mut map = UnorderedUintMap::new();
        for key in [5, 3, 17, 2, 11, 8, 0, 23, 13, 4] {
            map.insert(key, key * 10);
        }
        map.remove(17);
        map.remove(5);
        map.insert(6, 60);
        let keys: Vec<usize> = map.iter().map(|entry| entry.0).collect();
        assert_eq!(keys, [6, 4, 23, 8, 0, 11, 13, 2, 3]);
        assert_eq!(map.get(6), Some(&60));
        assert!(!map.has(17));
    }
}
