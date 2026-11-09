//! TLC's symmetry reduction on the engine's states, `symmetry.ts`'s `createCanonicalizer`: each
//! state is replaced by its smallest image under the symmetry group, compared variable by variable
//! in TLC's variable order, as TLCStateMut#fingerPrint picks it. Permuting a value is cached per
//! permutation, by id, so a value is permuted once however many states hold it.
//!
//! A state's values are mostly new, but their parts mostly aren't, so a permutation's image of a
//! state's value is compared with the smallest image so far without building it, from the cached
//! images of its parts. Only the image of a permutation that wins is built.

use std::collections::HashMap;

use tla_values::store::{KIND_FUNCTION, KIND_MODEL, KIND_SET, KIND_TUPLE, Outcome};
use tla_values::{Id, Store};

const NONE: Id = u32::MAX;

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
}

fn get(table: &[Id], id: Id) -> Id {
    table.get(id as usize).copied().unwrap_or(NONE)
}

fn put(table: &mut Vec<Id>, id: Id, value: Id, count: usize) {
    if id as usize >= table.len() {
        table.resize((count * 2).max(1024).max(id as usize + 1), NONE);
    }
    table[id as usize] = value;
}

impl Canonicalizer {
    /// A canonicalizer for the group, each permutation as the model values it moves, by name.
    pub fn new(store: &mut Store, group: &[Vec<(Vec<u16>, Vec<u16>)>], order: Vec<usize>) -> Self {
        let permutations: Vec<HashMap<Id, Id>> = group
            .iter()
            .map(|pairs| {
                pairs
                    .iter()
                    .map(|(name, image)| (store.model(name), store.model(image)))
                    .collect()
            })
            .collect();
        let is_type_preserving = permutations.iter().all(|permutation| {
            permutation
                .iter()
                .all(|(&id, &image)| store.get_model_type(id) == store.get_model_type(image))
        });
        let width = order.len();
        Canonicalizer {
            images: vec![Vec::new(); permutations.len()],
            larger_than: vec![Vec::new(); permutations.len()],
            permutations,
            is_type_preserving,
            order,
            parts: Vec::new(),
            marks: Vec::new(),
            positions: Vec::new(),
            stamp: 0,
            smallest: vec![NONE; width],
        }
    }

    /// A canonicalizer for the same group that has permuted nothing yet, for another thread.
    pub fn fresh(&self) -> Canonicalizer {
        Canonicalizer {
            permutations: self.permutations.clone(),
            is_type_preserving: self.is_type_preserving,
            images: vec![Vec::new(); self.permutations.len()],
            larger_than: vec![Vec::new(); self.permutations.len()],
            order: self.order.clone(),
            parts: Vec::new(),
            marks: Vec::new(),
            positions: Vec::new(),
            stamp: 0,
            smallest: vec![NONE; self.order.len()],
        }
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
