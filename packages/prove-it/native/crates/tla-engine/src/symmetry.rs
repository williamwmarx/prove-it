//! TLC's symmetry reduction on the engine's states, `symmetry.ts`'s `createCanonicalizer`: each
//! state is replaced by its smallest image under the symmetry group, compared variable by variable
//! in TLC's variable order, as TLCStateMut#fingerPrint picks it. Permuting a value is cached per
//! permutation, by id, so a value is permuted once however many states hold it.
//!
//! A state's values are mostly new, but their parts mostly aren't, so a permutation's image of a
//! state's value is compared with the smallest image so far without building it, from the cached
//! images of its parts. Only the image of a permutation that wins is built.
//!
//! The smallest image is the least in the lexicographic order of the variables, so it is found
//! variable by variable: the least image of the first variable under the whole group, then the
//! least image of the next under the permutations that gave that, and so on. A step depends only
//! on the value and the permutations left, and successors share their parents' values, so each
//! step is remembered. The least image is the same whatever order the permutations are tried in;
//! only the comparisons made differ, which matters where one fails, as one of model values of
//! different types does, so a group that can mix them is tried permutation by permutation, in
//! TLC's order, as the comparisons of unbuilt images above are.

use std::collections::{HashMap, HashSet};
use std::hash::{BuildHasherDefault, Hasher};

use tla_values::store::{Bail, KIND_FUNCTION, KIND_MODEL, KIND_SET, KIND_TUPLE, Outcome};
use tla_values::{Id, Store};

const NONE: Id = u32::MAX;

// The identity, among the permutations left at a step: permutation `index` is `index + 1`.
const IDENTITY: u32 = 0;

/// A multiplicative hash of the integer keys of the remembered steps.
#[derive(Default)]
struct IntegerHasher(u64);

impl Hasher for IntegerHasher {
    fn finish(&self) -> u64 {
        self.0
    }

    fn write(&mut self, bytes: &[u8]) {
        for &byte in bytes {
            self.write_u64(u64::from(byte));
        }
    }

    fn write_u64(&mut self, value: u64) {
        self.0 = (self.0.rotate_left(5) ^ value).wrapping_mul(0x51_7c_c1_b7_27_22_0a_95);
    }
}

/// A symmetry group, each permutation as the model values it moves, each to its image.
pub type Group = Vec<HashMap<Id, Id>>;

/// A symmetry group, each permutation as the names of the model values it moves, each with its
/// image's.
pub type NamedGroup = Vec<Vec<(Vec<u16>, Vec<u16>)>>;

pub struct Canonicalizer {
    permutations: Vec<HashMap<Id, Id>>,
    // TLC sorts each image, which fails where it mixes model values of different types; the images
    // of a group that can mix them are built, so that the engine fails there too.
    is_type_preserving: bool,
    // Each permutation's image of each id permuted so far, or NONE.
    images: Vec<Vec<Id>>,
    // For each permutation and id, the image the id's image last compared larger than, or NONE: a
    // state is generated again and again, and an image that compared equal or smaller is known.
    larger_than: Vec<Vec<Id>>,
    order: Vec<usize>,
    // The parts of the value being compared, and stamps that mark ids by the comparison that saw
    // them, with the position each key was seen at.
    parts: Vec<Id>,
    marks: Vec<u32>,
    positions: Vec<u32>,
    stamp: u32,
    smallest: Vec<Id>,
    // Each set of permutations left at a step, the whole group first, and the index of each.
    survivors: Vec<Vec<u32>>,
    survivor_indices: HashMap<Vec<u32>, u32>,
    // Each step taken, by the value and the permutations left (`step_key`): the least image and the
    // permutations that give it.
    steps: HashMap<u64, (Id, u32), BuildHasherDefault<IntegerHasher>>,
    kept: Vec<u32>,
}

fn step_key(id: Id, survivors: u32) -> u64 {
    u64::from(survivors) << 32 | u64::from(id)
}

fn get(table: &[Id], id: Id) -> Id {
    table.get(id as usize).copied().unwrap_or(NONE)
}

/// The group by the names of the model values each permutation moves, for a reader with another
/// store.
pub fn name_group(store: &Store, group: &[HashMap<Id, Id>]) -> NamedGroup {
    group
        .iter()
        .map(|permutation| {
            let mut pairs: Vec<(Vec<u16>, Vec<u16>)> = permutation
                .iter()
                .map(|(&id, &image)| (store.text_of(id).to_vec(), store.text_of(image).to_vec()))
                .collect();
            pairs.sort_unstable();
            pairs
        })
        .collect()
}

/// The permutations a SYMMETRY definition's value lists (`Tool.getSymmetryPerms`), each as the
/// model values it moves, each to its image. A value that isn't a set of functions of model values,
/// which TLC reports, is the interpreter's to report.
pub fn get_permutations(store: &mut Store, value: Id) -> Outcome<Group> {
    if store.kind_of(value) != KIND_SET {
        return Err(Bail("a symmetry that isn't a set of functions"));
    }
    (0..store.size_of(value))
        .map(|index| {
            let function = store.element_at(value, index);
            if !matches!(store.kind_of(function), KIND_FUNCTION | KIND_TUPLE) {
                return Err(Bail("a symmetry value that isn't a function"));
            }
            let mut permutation = HashMap::new();
            for position in 0..store.size_of(function) {
                let key = store.get_key(function, position);
                let image = store.get_range_value(function, position);
                if !store.is_model_id(key) || !store.is_model_id(image) {
                    return Err(Bail(
                        "a symmetry function of values that aren't model values",
                    ));
                }
                if key != image {
                    permutation.insert(key, image);
                }
            }
            Ok(permutation)
        })
        .collect()
}

/// The group the permutations generate, without the identity, as `symmetry.ts`'s
/// `getSymmetryGroup` closes it: the generators, then each composition of a generator with a
/// member found in the round before.
pub fn close_group(permutations: Group) -> Group {
    let key = |permutation: &HashMap<Id, Id>| {
        let mut pairs: Vec<(Id, Id)> = permutation
            .iter()
            .map(|(&id, &image)| (id, image))
            .collect();
        pairs.sort_unstable();
        pairs
    };
    let mut seen = HashSet::new();
    let mut group: Group = permutations
        .into_iter()
        .filter(|permutation| !permutation.is_empty() && seen.insert(key(permutation)))
        .collect();
    let generators = group.clone();
    let mut start = 0;
    while start < group.len() {
        let end = group.len();
        for generator in &generators {
            for index in start..end {
                let composed = compose(generator, &group[index]);
                if !composed.is_empty() && seen.insert(key(&composed)) {
                    group.push(composed);
                }
            }
        }
        start = end;
    }
    group
}

// The permutation that applies `first`, then `second`.
fn compose(first: &HashMap<Id, Id>, second: &HashMap<Id, Id>) -> HashMap<Id, Id> {
    first
        .keys()
        .chain(second.keys())
        .filter_map(|&id| {
            let image = match first.get(&id) {
                Some(image) => *second.get(image).unwrap_or(image),
                None => *second.get(&id)?,
            };
            (image != id).then_some((id, image))
        })
        .collect()
}

fn put(table: &mut Vec<Id>, id: Id, value: Id, count: usize) {
    if id as usize >= table.len() {
        table.resize((count * 2).max(1024).max(id as usize + 1), NONE);
    }
    table[id as usize] = value;
}

impl Canonicalizer {
    /// A canonicalizer for the group, each permutation as the model values it moves, each to its
    /// image.
    pub fn new(store: &Store, permutations: Group, order: Vec<usize>) -> Self {
        let is_type_preserving = permutations.iter().all(|permutation| {
            permutation
                .iter()
                .all(|(&id, &image)| store.get_model_type(id) == store.get_model_type(image))
        });
        Self::with(permutations, is_type_preserving, order)
    }

    fn with(permutations: Group, is_type_preserving: bool, order: Vec<usize>) -> Self {
        let group: Vec<u32> = (IDENTITY..=permutations.len() as u32).collect();
        Canonicalizer {
            images: vec![Vec::new(); permutations.len()],
            larger_than: vec![Vec::new(); permutations.len()],
            permutations,
            is_type_preserving,
            parts: Vec::new(),
            marks: Vec::new(),
            positions: Vec::new(),
            stamp: 0,
            smallest: vec![NONE; order.len()],
            order,
            survivor_indices: HashMap::from([(group.clone(), 0)]),
            survivors: vec![group],
            steps: HashMap::default(),
            kept: Vec::new(),
        }
    }

    /// The group, each permutation as the model values it moves, each to its image.
    pub fn group(&self) -> &[HashMap<Id, Id>] {
        &self.permutations
    }

    /// A canonicalizer for the same group that has permuted nothing yet, for another thread.
    pub fn fresh(&self) -> Canonicalizer {
        Self::with(
            self.permutations.clone(),
            self.is_type_preserving,
            self.order.clone(),
        )
    }

    /// Forgets the images of ids from `bound` on, and the images that are such ids, which the
    /// store has let go of.
    pub fn forget_from(&mut self, bound: Id) {
        for table in self.images.iter_mut().chain(&mut self.larger_than) {
            table.truncate(bound as usize);
            for image in table.iter_mut().filter(|image| **image >= bound) {
                *image = NONE;
            }
        }
        self.steps
            .retain(|&key, &mut (image, _)| (key as Id) < bound && image < bound);
    }

    fn remember(&mut self, store: &Store, id: Id, index: usize, image: Id) {
        put(&mut self.images[index], id, image, store.value_count());
    }

    fn permute(&mut self, store: &mut Store, id: Id, index: usize) -> Outcome<Id> {
        let kind = store.kind_of(id);
        if kind == KIND_MODEL {
            return Ok(self.permutations[index].get(&id).copied().unwrap_or(id));
        }
        if kind != KIND_SET && kind != KIND_FUNCTION && kind != KIND_TUPLE {
            return Ok(id);
        }
        let known = get(&self.images[index], id);
        if known != NONE {
            return Ok(known);
        }
        let size = store.size_of(id);
        let mut is_moved = false;
        let result = if kind == KIND_SET || kind == KIND_TUPLE {
            let mut images = Vec::with_capacity(size as usize);
            for position in 0..size {
                let element = if kind == KIND_SET {
                    store.element_at(id, position)
                } else {
                    store.get_range_value(id, position)
                };
                let image = self.permute(store, element, index)?;
                is_moved |= image != element;
                images.push(image);
            }
            match (is_moved, kind) {
                (false, _) => id,
                (true, KIND_SET) => store.set_of_range(&images)?,
                (true, _) => store.tuple_of(&images),
            }
        } else {
            let mut keys = Vec::with_capacity(size as usize);
            let mut values = Vec::with_capacity(size as usize);
            for position in 0..size {
                let key = store.get_key(id, position);
                let value = store.get_range_value(id, position);
                keys.push(self.permute(store, key, index)?);
                values.push(self.permute(store, value, index)?);
                is_moved |= keys[position as usize] != key || values[position as usize] != value;
            }
            if is_moved {
                store.function_of(&keys, &values)?
            } else {
                id
            }
        };
        self.remember(store, id, index, result);
        Ok(result)
    }

    fn mark(&mut self, store: &Store, id: Id) {
        if id as usize >= self.marks.len() {
            let capacity = (id as usize + 1).max(store.value_count()) * 2;
            self.marks.resize(capacity.max(1024), 0);
            self.positions.resize(capacity.max(1024), 0);
        }
        self.marks[id as usize] = self.stamp;
    }

    fn is_marked(&self, id: Id) -> bool {
        self.marks.get(id as usize) == Some(&self.stamp)
    }

    fn next_stamp(&mut self) {
        if self.stamp == u32::MAX {
            self.marks.fill(0);
            self.stamp = 0;
        }
        self.stamp += 1;
    }

    fn part(store: &mut Store, kind: u8, id: Id, position: u32) -> Id {
        if kind == KIND_SET {
            store.element_at(id, position)
        } else {
            store.get_key(id, position)
        }
    }

    // How the parts, once sorted, compare in TLC's order with those of smallest, as many and as
    // distinct: two such sequences first differ where the least of the parts in only one of them
    // stands, so the sequence holding it is the smaller.
    fn compare_parts(
        &mut self,
        store: &mut Store,
        size: u32,
        smallest: Id,
        kind: u8,
    ) -> Outcome<i32> {
        self.next_stamp();
        for position in 0..size {
            let part = Self::part(store, kind, smallest, position);
            self.mark(store, part);
        }
        let mut least = NONE;
        for position in 0..size as usize {
            let part = self.parts[position];
            if !self.is_marked(part) && (least == NONE || store.compare(part, least)? < 0) {
                least = part;
            }
        }
        if least == NONE {
            return Ok(0);
        }
        self.next_stamp();
        for position in 0..size as usize {
            let part = self.parts[position];
            self.mark(store, part);
        }
        let mut position = 0;
        while self.is_marked(Self::part(store, kind, smallest, position)) {
            position += 1;
        }
        let other = Self::part(store, kind, smallest, position);
        store.compare(least, other)
    }

    // How the image of a composite value compares with smallest, the image of the same value
    // under another permutation, so of its kind and size.
    fn compare_unbuilt(
        &mut self,
        store: &mut Store,
        id: Id,
        index: usize,
        smallest: Id,
    ) -> Outcome<i32> {
        let kind = store.kind_of(id);
        let size = store.size_of(id);
        if kind == KIND_TUPLE {
            for position in 0..size {
                let image = self.permute(store, store.get_range_value(id, position), index)?;
                let comparison = store.compare(image, store.get_range_value(smallest, position))?;
                if comparison != 0 {
                    return Ok(comparison);
                }
            }
            return Ok(0);
        }
        self.parts.clear();
        for position in 0..size {
            let part = Self::part(store, kind, id, position);
            let image = self.permute(store, part, index)?;
            self.parts.push(image);
        }
        let comparison = self.compare_parts(store, size, smallest, kind)?;
        if comparison != 0 || kind == KIND_SET {
            return Ok(comparison);
        }
        // The domains are the same, so the values compare in the order of its keys, each of
        // which, as a key of smallest, was marked and so has a position.
        for position in 0..size {
            let part = self.parts[position as usize];
            self.positions[part as usize] = position;
        }
        for position in 0..size {
            let key = store.get_key(smallest, position);
            let at = self.positions[key as usize];
            let image = self.permute(store, store.get_range_value(id, at), index)?;
            let comparison = store.compare(image, store.get_range_value(smallest, position))?;
            if comparison != 0 {
                return Ok(comparison);
            }
        }
        Ok(0)
    }

    fn compare_image(
        &mut self,
        store: &mut Store,
        id: Id,
        index: usize,
        smallest: Id,
    ) -> Outcome<i32> {
        let kind = store.kind_of(id);
        if !self.is_type_preserving
            || (kind != KIND_SET && kind != KIND_FUNCTION && kind != KIND_TUPLE)
            || get(&self.images[index], id) != NONE
        {
            let image = self.permute(store, id, index)?;
            return store.compare(image, smallest);
        }
        let known = get(&self.larger_than[index], id);
        if known == smallest {
            return Ok(1);
        }
        // A value compared again, with another image, is worth building.
        if known != NONE {
            let image = self.permute(store, id, index)?;
            return store.compare(image, smallest);
        }
        let comparison = self.compare_unbuilt(store, id, index, smallest)?;
        if comparison > 0 {
            put(
                &mut self.larger_than[index],
                id,
                smallest,
                store.value_count(),
            );
        }
        if comparison == 0 {
            self.remember(store, id, index, smallest);
        }
        Ok(comparison)
    }

    /// Replaces the state with its representative.
    pub fn canonicalize(&mut self, store: &mut Store, state: &mut [Id]) -> Outcome<()> {
        if !self.is_type_preserving {
            return self.canonicalize_in_order(store, state);
        }
        let mut survivors = 0;
        for at in 0..self.order.len() {
            let variable = self.order[at];
            let members = &self.survivors[survivors as usize];
            if members == &[IDENTITY] {
                return Ok(());
            }
            if members.len() == 1 {
                let index = members[0] as usize - 1;
                for rest in at..self.order.len() {
                    let variable = self.order[rest];
                    state[variable] = self.permute(store, state[variable], index)?;
                }
                return Ok(());
            }
            let key = step_key(state[variable], survivors);
            let (image, left) = match self.steps.get(&key) {
                Some(&step) => step,
                None => {
                    let step = self.step(store, state[variable], survivors)?;
                    self.steps.insert(key, step);
                    step
                }
            };
            state[variable] = image;
            survivors = left;
        }
        Ok(())
    }

    // The least image of the value under the permutations left, and the permutations that give it.
    fn step(&mut self, store: &mut Store, id: Id, survivors: u32) -> Outcome<(Id, u32)> {
        let members = std::mem::take(&mut self.survivors[survivors as usize]);
        let least = self.least_image(store, id, &members);
        self.survivors[survivors as usize] = members;
        let least = least?;
        let left = match self.survivor_indices.get(&self.kept) {
            Some(&index) => index,
            None => {
                let index = self.survivors.len() as u32;
                self.survivors.push(self.kept.clone());
                self.survivor_indices.insert(self.kept.clone(), index);
                index
            }
        };
        Ok((least, left))
    }

    fn least_image(&mut self, store: &mut Store, id: Id, members: &[u32]) -> Outcome<Id> {
        self.kept.clear();
        let mut least = NONE;
        for &member in members {
            if member == IDENTITY {
                least = id;
                self.kept.push(member);
                continue;
            }
            let index = member as usize - 1;
            if least == NONE {
                least = self.permute(store, id, index)?;
                self.kept.push(member);
                continue;
            }
            let comparison = self.compare_image(store, id, index, least)?;
            if comparison < 0 {
                least = self.permute(store, id, index)?;
                self.kept.clear();
            }
            if comparison <= 0 {
                self.kept.push(member);
            }
        }
        Ok(least)
    }

    // TLC's own search for the representative, permutation by permutation.
    fn canonicalize_in_order(&mut self, store: &mut Store, state: &mut [Id]) -> Outcome<()> {
        let mut smallest = std::mem::take(&mut self.smallest);
        smallest.copy_from_slice(state);
        for index in 0..self.permutations.len() {
            let mut comparison = 0;
            let mut at = 0;
            while at < self.order.len() && comparison == 0 {
                let variable = self.order[at];
                comparison =
                    match self.compare_image(store, state[variable], index, smallest[variable]) {
                        Ok(comparison) => comparison,
                        Err(bail) => {
                            self.smallest = smallest;
                            return Err(bail);
                        }
                    };
                at += 1;
            }
            if comparison >= 0 {
                continue;
            }
            for rest in at - 1..self.order.len() {
                let variable = self.order[rest];
                smallest[variable] = match self.permute(store, state[variable], index) {
                    Ok(image) => image,
                    Err(bail) => {
                        self.smallest = smallest;
                        return Err(bail);
                    }
                };
            }
        }
        state.copy_from_slice(&smallest);
        self.smallest = smallest;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn model(store: &mut Store, name: &str) -> Id {
        store.model(&name.encode_utf16().collect::<Vec<u16>>())
    }

    // A permutation of model values as a function, as TLC's Permutations gives it.
    fn function(store: &mut Store, pairs: &[(&str, &str)]) -> Id {
        let keys: Vec<Id> = pairs.iter().map(|(key, _)| model(store, key)).collect();
        let images: Vec<Id> = pairs.iter().map(|(_, image)| model(store, image)).collect();
        store.function_of(&keys, &images).expect("a function")
    }

    #[test]
    fn closes_the_group_the_permutations_generate() {
        let mut store = Store::new();
        // Two transpositions of {a, b, c} generate the five permutations that move something.
        let swaps = [
            function(&mut store, &[("a", "b"), ("b", "a"), ("c", "c")]),
            function(&mut store, &[("a", "a"), ("b", "c"), ("c", "b")]),
            function(&mut store, &[("a", "a"), ("b", "b"), ("c", "c")]),
        ];
        let set = store.set_of(&swaps).expect("a set");
        let permutations = get_permutations(&mut store, set).expect("permutations");
        assert_eq!(permutations.len(), 3);
        assert_eq!(close_group(permutations).len(), 5);
    }

    #[test]
    fn picks_the_representative_tlc_picks_permutation_by_permutation() {
        let mut store = Store::new();
        let replicas = ["r1", "r2", "r3"].map(|name| model(&mut store, name));
        let values = ["v1", "v2"].map(|name| model(&mut store, name));
        let generators = [
            function(&mut store, &[("r1", "r2"), ("r2", "r1"), ("r3", "r3")]),
            function(&mut store, &[("r1", "r1"), ("r2", "r3"), ("r3", "r2")]),
            function(&mut store, &[("v1", "v2"), ("v2", "v1")]),
        ];
        let set = store.set_of(&generators).expect("a set");
        let group = close_group(get_permutations(&mut store, set).expect("permutations"));
        assert_eq!(group.len(), 11);
        let mut canonicalizer = Canonicalizer::new(&store, group, vec![2, 0, 1]);
        let mut seed = 7_u64;
        let mut next = |bound: usize| {
            seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            (seed >> 33) as usize % bound
        };
        let mut representatives = HashSet::new();
        for _ in 0..2000 {
            let ballots: Vec<Id> = (0..3)
                .map(|_| store.int(next(3) as i64).expect("an int"))
                .collect();
            let ballots = store.function_of(&replicas, &ballots).expect("a function");
            let messages: Vec<Id> = (0..next(5))
                .map(|_| store.tuple_of(&[replicas[next(3)], values[next(2)]]))
                .collect();
            let messages = store.set_of(&messages).expect("a set");
            let chosen = [values[0], values[1], replicas[0]][next(3)];
            let state = [ballots, messages, chosen];
            let mut in_order = state;
            canonicalizer
                .canonicalize_in_order(&mut store, &mut in_order)
                .expect("a representative");
            let mut by_variable = state;
            canonicalizer
                .canonicalize(&mut store, &mut by_variable)
                .expect("a representative");
            assert_eq!(by_variable, in_order);
            representatives.insert(in_order);
        }
        // The states fall into fewer orbits than there are states.
        assert!(representatives.len() < 1000);
    }

    #[test]
    fn leaves_a_value_that_isnt_a_set_of_permutations_to_the_interpreter() {
        let mut store = Store::new();
        let one = store.int(1).expect("an int");
        let a = model(&mut store, "a");
        let of_ints = store.function_of(&[one], &[a]).expect("a function");
        for value in [
            one,
            store.set_of(&[one]).expect("a set"),
            store.set_of(&[of_ints]).expect("a set"),
        ] {
            assert!(get_permutations(&mut store, value).is_err());
        }
    }
}
