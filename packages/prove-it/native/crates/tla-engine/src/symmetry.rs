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
//! only the comparisons made differ, which matters where one can fail. A state is searched
//! variable by variable only where none can: where the group keeps model values' types, and the
//! shape of each of its values (`Shape`) shows that the images of a value compare without
//! failing. Any other state is searched permutation by permutation, in TLC's order.

use std::collections::{HashMap, HashSet};
use std::hash::{BuildHasherDefault, Hasher};

use tla_values::store::{
    Bail, KIND_BOOL, KIND_FUNCTION, KIND_INT, KIND_MODEL, KIND_SET, KIND_STRING, KIND_TUPLE,
    Outcome,
};
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

// A value's shape that some comparison of its images could fail on, and one not yet known.
const UNSAFE: u32 = u32::MAX - 1;
const UNKNOWN: u32 = u32::MAX;

/// What comparing a value with another of its shape meets, from TLC's `compareTo`, as the store
/// follows it: two values of shapes that join compare without failing. A comparison pairs a set's
/// elements by their order, a function's keys and its values by theirs, which a permutation moves,
/// but a record's values by key and a tuple's by position, which it doesn't. A permutation that
/// keeps model values' types keeps a value's shape, so the images of a value of a shape compare
/// with each other without failing.
#[derive(Clone, PartialEq, Eq, Hash)]
enum Shape {
    // The parts of an empty value.
    Any,
    // Untyped model values, which compare with any value, with values of the inner shape. TLC
    // compares a function with keys of such a mix with one over an interval only where the keys
    // are integers (`FcnRcdValue.compareOtherInterval`), failing at a model value, so keys of
    // untyped model values mixed with other than model values make no shape.
    Untyped(u32),
    Bool,
    Int,
    Str,
    // A typed model value, by its type.
    Model(u16),
    // By the shape of the elements.
    Set(u32),
    // By key, sorted by id.
    Record(Vec<(Id, u32)>),
    Tuple(Vec<u32>),
    // By the shape of the keys and of the values.
    Function(u32, u32),
    // An empty function or tuple, which compares with any other by its size.
    EmptyFunction,
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
    // Each permutation's image of each id permuted so far, or NONE, and of each model value the
    // group moves.
    images: Table,
    // For each permutation and id, the image the id's image last compared larger than, or NONE: a
    // state is generated again and again, and an image that compared equal or smaller is known.
    larger_than: Table,
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
    // Each value's shape by id, or UNKNOWN, each shape interned by its index.
    value_shapes: Vec<u32>,
    shapes: Vec<Shape>,
    shape_indices: HashMap<Shape, u32>,
}

fn step_key(id: Id, survivors: u32) -> u64 {
    u64::from(survivors) << 32 | u64::from(id)
}

/// An id for each permutation and id, or NONE, as a row of every permutation's by id, so that the
/// permutations tried one after another for a value find its parts' images on the same lines.
struct Table {
    width: usize,
    // Each id's row, or NONE.
    rows: Vec<u32>,
    cells: Vec<Id>,
}

impl Table {
    fn new(width: usize) -> Self {
        Table {
            width,
            rows: Vec::new(),
            cells: Vec::new(),
        }
    }

    fn get(&self, id: Id, index: usize) -> Id {
        match self.rows.get(id as usize) {
            Some(&row) if row != NONE => self.cells[row as usize * self.width + index],
            _ => NONE,
        }
    }

    // The row of the id, made with every cell `fill` if it has none.
    fn row(&mut self, id: Id, fill: Id, count: usize) -> usize {
        if id as usize >= self.rows.len() {
            self.rows
                .resize((count * 2).max(1024).max(id as usize + 1), NONE);
        }
        if self.rows[id as usize] == NONE {
            self.rows[id as usize] = (self.cells.len() / self.width) as u32;
            self.cells.resize(self.cells.len() + self.width, fill);
        }
        self.rows[id as usize] as usize
    }

    fn put(&mut self, id: Id, index: usize, value: Id, count: usize) {
        let row = self.row(id, NONE, count);
        self.cells[row * self.width + index] = value;
    }

    // Keeps the rows of ids below `bound`, without the cells that are such ids.
    fn forget_from(&mut self, bound: Id) {
        self.rows.truncate(bound as usize);
        let mut cells = Vec::new();
        for row in self.rows.iter_mut().filter(|row| **row != NONE) {
            let start = *row as usize * self.width;
            *row = (cells.len() / self.width) as u32;
            cells.extend(
                self.cells[start..start + self.width]
                    .iter()
                    .map(|&cell| if cell >= bound { NONE } else { cell }),
            );
        }
        self.cells = cells;
    }
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
        let mut images = Table::new(permutations.len());
        for (index, permutation) in permutations.iter().enumerate() {
            for (&id, &image) in permutation {
                let row = images.row(id, id, id as usize + 1);
                images.cells[row * images.width + index] = image;
            }
        }
        Canonicalizer {
            images,
            larger_than: Table::new(permutations.len()),
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
            value_shapes: Vec::new(),
            shapes: Vec::new(),
            shape_indices: HashMap::new(),
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
        self.images.forget_from(bound);
        self.larger_than.forget_from(bound);
        self.steps
            .retain(|&key, &mut (image, _)| (key as Id) < bound && image < bound);
        // A record's shape holds its keys.
        self.value_shapes.clear();
        self.shapes.clear();
        self.shape_indices.clear();
    }

    fn remember(&mut self, store: &Store, id: Id, index: usize, image: Id) {
        self.images.put(id, index, image, store.value_count());
    }

    fn permute(&mut self, store: &mut Store, id: Id, index: usize) -> Outcome<Id> {
        let kind = store.kind_of(id);
        if kind == KIND_MODEL {
            let image = self.images.get(id, index);
            return Ok(if image == NONE { id } else { image });
        }
        if kind != KIND_SET && kind != KIND_FUNCTION && kind != KIND_TUPLE {
            return Ok(id);
        }
        let known = self.images.get(id, index);
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
                // TLC's permutation keeps the function's class.
                (true, _) if store.is_built_as_function(id) => {
                    let image = store.tuple_of(&images);
                    store.mark_built_as_function(image)
                }
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
            || self.images.get(id, index) != NONE
        {
            let image = self.permute(store, id, index)?;
            return store.compare(image, smallest);
        }
        let known = self.larger_than.get(id, index);
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
            self.larger_than
                .put(id, index, smallest, store.value_count());
        }
        if comparison == 0 {
            self.remember(store, id, index, smallest);
        }
        Ok(comparison)
    }

    fn intern_shape(&mut self, shape: Shape) -> u32 {
        if let Some(&index) = self.shape_indices.get(&shape) {
            return index;
        }
        let index = self.shapes.len() as u32;
        self.shapes.push(shape.clone());
        self.shape_indices.insert(shape, index);
        index
    }

    // The shape of a function that isn't a record, by its keys' and values' shapes.
    fn function_shape(&mut self, key: u32, value: u32) -> u32 {
        if key == UNSAFE || value == UNSAFE {
            return UNSAFE;
        }
        if let Shape::Untyped(inner) = self.shapes[key as usize]
            && !matches!(self.shapes[inner as usize], Shape::Any | Shape::Model(_))
        {
            return UNSAFE;
        }
        self.intern_shape(Shape::Function(key, value))
    }

    // The shape that compares as both do, or UNSAFE where a comparison of the two could fail.
    fn join(&mut self, left: u32, right: u32) -> u32 {
        if left == right || left == UNSAFE || right == UNSAFE {
            return if left == UNSAFE { left } else { right };
        }
        let joined = match (&self.shapes[left as usize], &self.shapes[right as usize]) {
            (Shape::Any, _) => return right,
            (_, Shape::Any) => return left,
            (&Shape::Untyped(left), &Shape::Untyped(right)) => {
                Shape::Untyped(self.join(left, right))
            }
            (&Shape::Untyped(inner), _) => Shape::Untyped(self.join(inner, right)),
            (_, &Shape::Untyped(inner)) => Shape::Untyped(self.join(left, inner)),
            (Shape::EmptyFunction, Shape::Record(_) | Shape::Tuple(_) | Shape::Function(..)) => {
                return right;
            }
            (Shape::Record(_) | Shape::Tuple(_) | Shape::Function(..), Shape::EmptyFunction) => {
                return left;
            }
            (&Shape::Set(left), &Shape::Set(right)) => {
                let element = self.join(left, right);
                Shape::Set(element)
            }
            (&Shape::Function(left_key, left_value), &Shape::Function(right_key, right_value)) => {
                let key = self.join(left_key, right_key);
                let value = self.join(left_value, right_value);
                return self.function_shape(key, value);
            }
            (Shape::Tuple(left), Shape::Tuple(right)) => {
                let (left, right) = (left.clone(), right.clone());
                let length = left.len().max(right.len());
                let positions = (0..length)
                    .map(|at| match (left.get(at), right.get(at)) {
                        (Some(&left), Some(&right)) => self.join(left, right),
                        (Some(&only), None) | (None, Some(&only)) => only,
                        (None, None) => unreachable!("a position of neither tuple"),
                    })
                    .collect();
                Shape::Tuple(positions)
            }
            (Shape::Record(left), Shape::Record(right)) => {
                let mut fields = left.clone();
                for &(key, right) in &right.clone() {
                    match fields.binary_search_by_key(&key, |&(key, _)| key) {
                        Ok(at) => fields[at].1 = self.join(fields[at].1, right),
                        Err(at) => fields.insert(at, (key, right)),
                    }
                }
                Shape::Record(fields)
            }
            _ => return UNSAFE,
        };
        let is_unsafe = match &joined {
            Shape::Set(element) | Shape::Untyped(element) => *element == UNSAFE,
            Shape::Tuple(positions) => positions.contains(&UNSAFE),
            Shape::Record(fields) => fields.iter().any(|&(_, shape)| shape == UNSAFE),
            _ => false,
        };
        if is_unsafe {
            UNSAFE
        } else {
            self.intern_shape(joined)
        }
    }

    // The shape of a value, or UNSAFE where comparisons of its images could fail.
    fn shape_of(&mut self, store: &mut Store, id: Id) -> u32 {
        if let Some(&known) = self.value_shapes.get(id as usize)
            && known != UNKNOWN
        {
            return known;
        }
        let kind = store.kind_of(id);
        let size = store.size_of(id);
        let shape = match kind {
            KIND_BOOL => self.intern_shape(Shape::Bool),
            KIND_INT => self.intern_shape(Shape::Int),
            KIND_STRING | KIND_MODEL if !store.is_text_ordered(id) => UNSAFE,
            KIND_STRING => self.intern_shape(Shape::Str),
            KIND_MODEL => match store.get_model_type(id) {
                0 => {
                    let any = self.intern_shape(Shape::Any);
                    self.intern_shape(Shape::Untyped(any))
                }
                model_type => self.intern_shape(Shape::Model(model_type)),
            },
            KIND_SET => {
                let mut element = self.intern_shape(Shape::Any);
                for position in 0..size {
                    let part = self.shape_of(store, store.element_at(id, position));
                    element = self.join(element, part);
                }
                if element == UNSAFE {
                    UNSAFE
                } else {
                    self.intern_shape(Shape::Set(element))
                }
            }
            KIND_FUNCTION | KIND_TUPLE if size == 0 => self.intern_shape(Shape::EmptyFunction),
            KIND_TUPLE => {
                let positions: Vec<u32> = (0..size)
                    .map(|position| self.shape_of(store, store.get_range_value(id, position)))
                    .collect();
                if positions.contains(&UNSAFE) {
                    UNSAFE
                } else {
                    self.intern_shape(Shape::Tuple(positions))
                }
            }
            KIND_FUNCTION if store.is_record(id) => {
                // Records of different keys compare by their keys, which must be ordered.
                let mut fields: Vec<(Id, u32)> = (0..size)
                    .map(|position| {
                        let key = store.get_key(id, position);
                        let value = store.get_range_value(id, position);
                        let shape = match self.shape_of(store, key) {
                            UNSAFE => UNSAFE,
                            _ => self.shape_of(store, value),
                        };
                        (key, shape)
                    })
                    .collect();
                // By key id, which `join` searches by, not TLC's order of the keys.
                fields.sort_unstable_by_key(|&(key, _)| key);
                if fields.iter().any(|&(_, shape)| shape == UNSAFE) {
                    UNSAFE
                } else {
                    self.intern_shape(Shape::Record(fields))
                }
            }
            KIND_FUNCTION => {
                let (mut key, mut value) =
                    (self.intern_shape(Shape::Any), self.intern_shape(Shape::Any));
                for position in 0..size {
                    let key_id = store.get_key(id, position);
                    let key_shape = self.shape_of(store, key_id);
                    key = self.join(key, key_shape);
                    let value_shape = self.shape_of(store, store.get_range_value(id, position));
                    value = self.join(value, value_shape);
                }
                self.function_shape(key, value)
            }
            _ => UNSAFE,
        };
        if id as usize >= self.value_shapes.len() {
            let count = store.value_count();
            self.value_shapes
                .resize((count * 2).max(1024).max(id as usize + 1), UNKNOWN);
        }
        self.value_shapes[id as usize] = shape;
        shape
    }

    /// Replaces the state with its representative.
    pub fn canonicalize(&mut self, store: &mut Store, state: &mut [Id]) -> Outcome<()> {
        if !self.is_type_preserving
            || state
                .iter()
                .any(|&value| self.shape_of(store, value) == UNSAFE)
        {
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
            // TLC keeps the least of the state's images, the identity's included, comparing
            // variable by variable in its order (`TLCStateMut#fingerPrint`).
            let order = [2, 0, 1];
            let mut images = vec![state];
            for index in 0..canonicalizer.permutations.len() {
                images.push(state.map(|value| {
                    canonicalizer
                        .permute(&mut store, value, index)
                        .expect("an image")
                }));
            }
            assert!(images.contains(&by_variable));
            for image in images {
                let comparison = order
                    .iter()
                    .map(|&variable| {
                        store
                            .compare(by_variable[variable], image[variable])
                            .expect("a comparison")
                    })
                    .find(|&comparison| comparison != 0)
                    .unwrap_or(0);
                assert!(comparison <= 0);
            }
            representatives.insert(in_order);
        }
        // The states fall into fewer orbits than there are states.
        assert!(representatives.len() < 1000);
    }

    #[test]
    fn fails_where_tlc_fails_comparing_images() {
        let mut store = Store::new();
        let [a, b, c] = ["a", "b", "c"].map(|name| model(&mut store, name));
        // The swap of a and b first, then that of b and c.
        let swaps = vec![
            HashMap::from([(a, b), (b, a)]),
            HashMap::from([(b, c), (c, b)]),
        ];
        let mut canonicalizer = Canonicalizer::new(&store, close_group(swaps), vec![0, 1]);
        // The first permutation leaves x as it is, so TLC compares the images of y, which hold
        // values at a key it can't compare: 1 and FALSE, say.
        let text = |name: &str| name.encode_utf16().collect::<Vec<u16>>();
        let one = store.int(1).expect("an int");
        let one_tuple = store.tuple_of(&[one]);
        let field = store.str(&text("f"));
        let record = store.function_of(&[field], &[one]).expect("a record");
        let incomparable = [
            (one, store.bool(false)),
            (store.str(&text("s")), one),
            (store.tuple_of(&[]), store.set_of(&[]).expect("a set")),
            (one_tuple, store.set_of(&[one]).expect("a set")),
            (
                record,
                store.function_of(&[a, b], &[one, one]).expect("a function"),
            ),
            (model(&mut store, "A_1"), one),
        ];
        for (first, second) in incomparable {
            let y = store
                .function_of(&[a, b, c], &[first, second, a])
                .expect("a function");
            let mut in_order = [c, y];
            assert!(
                canonicalizer
                    .canonicalize_in_order(&mut store, &mut in_order)
                    .is_err()
            );
            let mut state = [c, y];
            assert!(canonicalizer.canonicalize(&mut store, &mut state).is_err());
        }
    }

    #[test]
    fn joins_records_by_field_whatever_order_their_keys_were_made_in() {
        let mut store = Store::new();
        let text = |name: &str| name.encode_utf16().collect::<Vec<u16>>();
        // TLC's order of the keys is f, g, h, but their ids are made in the order h, f, g.
        let names = [text("f"), text("g"), text("h")];
        store.rank_strings(names.iter().map(Vec::as_slice));
        let [h, f, g] = ["h", "f", "g"].map(|name| store.str(&text(name)));
        let [a, b, c] = ["a", "b", "c"].map(|name| model(&mut store, name));
        let swaps = vec![
            HashMap::from([(a, b), (b, a)]),
            HashMap::from([(b, c), (c, b)]),
        ];
        let mut canonicalizer = Canonicalizer::new(&store, close_group(swaps), vec![0, 1]);
        let one = store.int(1).expect("an int");
        let records: Vec<Id> = [a, b, c]
            .into_iter()
            .zip([one, store.bool(false), a])
            .map(|(model, value)| {
                store
                    .function_of(&[f, g, h], &[model, value, one])
                    .expect("a record")
            })
            .collect();
        let messages = store.set_of(&records).expect("a set");
        let mut in_order = [c, messages];
        assert!(
            canonicalizer
                .canonicalize_in_order(&mut store, &mut in_order)
                .is_err()
        );
        let mut state = [c, messages];
        assert!(canonicalizer.canonicalize(&mut store, &mut state).is_err());
    }

    #[test]
    fn fails_where_tlc_fails_comparing_record_keys_ranked_late() {
        let mut store = Store::new();
        let [a, b, c] = ["a", "b", "c"].map(|name| model(&mut store, name));
        let swaps = vec![
            HashMap::from([(a, b), (b, a)]),
            HashMap::from([(b, c), (c, b)]),
        ];
        let mut canonicalizer = Canonicalizer::new(&store, close_group(swaps), vec![0, 1]);
        // Keys ranked after the order is frozen, as ToString's are, which TLC's order may not
        // follow: comparing records of different keys bails.
        store.freeze_string_order();
        let text = |name: &str| name.encode_utf16().collect::<Vec<u16>>();
        let [f, g] = ["f", "g"].map(|name| {
            store.rank_text(&text(name));
            store.str(&text(name))
        });
        let one = store.int(1).expect("an int");
        let records = [f, g].map(|key| store.function_of(&[key], &[one]).expect("a record"));
        let y = store
            .function_of(&[a, b, c], &[records[0], records[1], a])
            .expect("a function");
        let mut in_order = [c, y];
        assert!(
            canonicalizer
                .canonicalize_in_order(&mut store, &mut in_order)
                .is_err()
        );
        let mut state = [c, y];
        assert!(canonicalizer.canonicalize(&mut store, &mut state).is_err());
    }

    #[test]
    fn keeps_untyped_model_keys_from_mixing_with_other_keys() {
        // TLC compares a function with one over an interval by integer keys only
        // (`FcnRcdValue.compareOtherInterval`), failing at a model value, which the store's order
        // passes: functions whose keys could meet that way go to TLC's loop.
        let mut store = Store::new();
        let [a, b, c] = ["a", "b", "c"].map(|name| model(&mut store, name));
        let typed = model(&mut store, "A_1");
        let swaps = vec![HashMap::from([(a, b), (b, a)])];
        let mut canonicalizer = Canonicalizer::new(&store, close_group(swaps), vec![0]);
        let [one, two] = [1, 2].map(|value| store.int(value).expect("an int"));
        let mixed = store
            .function_of(&[a, two], &[one, one])
            .expect("a function");
        let by_model = store.function_of(&[a], &[one]).expect("a function");
        let by_int = store.function_of(&[two], &[one]).expect("a function");
        let ranging = store
            .function_of(&[a, b, c], &[by_model, by_int, a])
            .expect("a function");
        for value in [mixed, ranging] {
            assert_eq!(canonicalizer.shape_of(&mut store, value), UNSAFE);
        }
        let by_models = store.function_of(&[a, b], &[one, two]).expect("a function");
        let by_any_models = store
            .function_of(&[a, typed], &[one, two])
            .expect("a function");
        let of_models = store.function_of(&[c], &[by_models]).expect("a function");
        for value in [by_models, by_any_models, of_models] {
            assert_ne!(canonicalizer.shape_of(&mut store, value), UNSAFE);
        }
    }

    // A value of mixed kinds, built from `next`, or none where the store refuses one.
    fn mixed_value(
        store: &mut Store,
        next: &mut impl FnMut(usize) -> usize,
        depth: u32,
    ) -> Option<Id> {
        let models = ["a", "b", "c"].map(|name| model(store, name));
        let text = |name: &str| name.encode_utf16().collect::<Vec<u16>>();
        let kind = next(if depth == 0 { 4 } else { 8 });
        let count = match kind {
            0 => return store.int(1 + next(2) as i64).ok(),
            1 => return Some(store.bool(next(2) == 0)),
            2 => return Some(store.str(&text(["s", "t", "u"][next(3)]))),
            3 => return Some(models[next(3)]),
            4 => next(4),
            5 => next(3),
            _ => 3,
        };
        let parts: Vec<Id> = (0..count)
            .map(|_| mixed_value(store, next, depth - 1))
            .collect::<Option<_>>()?;
        match kind {
            4 => store.set_of(&parts).ok(),
            5 => Some(store.tuple_of(&parts)),
            6 => store.function_of(&models, &parts).ok(),
            _ => {
                let keys = ["f", "g", "h"].map(|key| store.str(&text(key)));
                store.function_of(&keys, &parts).ok()
            }
        }
    }

    #[test]
    fn fails_or_not_as_tlc_does_on_values_of_mixed_kinds() {
        let mut store = Store::new();
        // Records' keys whose ids are made against TLC's order of them.
        let text = |name: &str| name.encode_utf16().collect::<Vec<u16>>();
        store.rank_strings([text("f"), text("g"), text("h")].iter().map(Vec::as_slice));
        store.str(&text("h"));
        // And a string ranked after the order is frozen, which compares with no other.
        store.freeze_string_order();
        store.rank_text(&text("u"));
        let [a, b, c] = ["a", "b", "c"].map(|name| model(&mut store, name));
        let swaps = vec![
            HashMap::from([(a, b), (b, a)]),
            HashMap::from([(b, c), (c, b)]),
        ];
        let mut canonicalizer = Canonicalizer::new(&store, close_group(swaps), vec![1, 0]);
        let mut seed = 11_u64;
        let mut next = |bound: usize| {
            seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            (seed >> 33) as usize % bound
        };
        let (mut failures, mut successes) = (0, 0);
        for _ in 0..5000 {
            let (Some(first), Some(second)) = (
                mixed_value(&mut store, &mut next, 2),
                mixed_value(&mut store, &mut next, 2),
            ) else {
                continue;
            };
            let mut in_order = [first, second];
            let expected = canonicalizer
                .canonicalize_in_order(&mut store, &mut in_order)
                .map(|()| in_order);
            let mut state = [first, second];
            let found = canonicalizer
                .canonicalize(&mut store, &mut state)
                .map(|()| state);
            assert_eq!(found.is_ok(), expected.is_ok());
            if let Ok(expected) = expected {
                assert_eq!(found.ok(), Some(expected));
                successes += 1;
            } else {
                failures += 1;
            }
        }
        assert!(failures > 0 && successes > failures);
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
