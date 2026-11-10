//! Classes of values that TLC compares without failing, so that membership in a set can be
//! answered by id.
//!
//! TLC tests membership with `compareTo` (`SetEnumValue.member`, `ValueVec.search`) or `equals`,
//! which fail for values of different kinds, typed model values of different types, a record and
//! a function, and so on. The store reproduces those failures by comparing as TLC does. But equal
//! values have equal ids, so where no comparison on the search's path can fail, membership is an
//! id lookup. A shape is a class of values any two of which compare without failing in
//! `Store::compare` and pass `Store::check_comparable`: the store gives each value its shape, and
//! the join of two shapes is a class holding both, or [`NONE`] where there is none.
//!
//! Why each class compares without failing (`Store::compare`, TLC's `compareTo`):
//! - Booleans with booleans, integers with integers: always.
//! - Strings with strings: unless one was ranked after the order froze, which is no shape.
//! - Model values: an untyped one compares with anything, a typed one with model values of its
//!   type or untyped ones. Ones ranked after the order froze are no shape.
//! - Sets: by size, then element by element in order; the elements share a class.
//! - Tuples: by length, then position by position. Tuples of one length compare their values at
//!   each position, which share a class; ones of different lengths compare no values.
//! - Records: by size, then by keys, which are ordered strings, then by values, only if the keys
//!   are equal: then the values of each key share a class.
//! - Functions that aren't records: by size, then key by key, then value by value; the keys
//!   share a class, as do the values. A function is no record if one key isn't a string.
//! - The empty tuple, the empty function, compares by size alone with any tuple, record or
//!   function, and so is in each of their classes.
//!
//! A tuple, record or function compared with one of another of these families may fail (a record
//! with a tuple of its size compares a string with an integer), so their joins are [`NONE`]. So
//! are a function TLC keeps lazy and Nat, Int and STRING, which the store doesn't classify, a tuple
//! longer than the small integers, whose keys the store interns as it compares, and a function
//! whose keys mix untyped model values with others, which TLC compares with a function over an
//! interval only where the keys are integers (`FcnRcdValue.compareOtherInterval`).

use std::collections::HashMap;

use super::{
    Id, KIND_BOOL, KIND_FUNCTION, KIND_INT, KIND_MODEL, KIND_SET, KIND_STRING, KIND_TUPLE,
    SMALL_INT_MAX, Store,
};

pub(super) type Shape = u32;

/// No class: values that may fail to compare.
pub(super) const NONE: Shape = 0;
// The class of no value, the elements of the empty set and the empty tuple.
const BOTTOM: Shape = 1;
const BOOL: Shape = 2;
const INT: Shape = 3;
const STRING: Shape = 4;
const FIRST_TERM: Shape = 5;
// A value whose shape the store hasn't found yet.
const UNKNOWN: Shape = Shape::MAX;
// The most fields a class of records holds: records of many other keys join to a class of all
// their keys, which would take time and memory in their square, so past this they have none and
// compare as before.
const MAXIMUM_FIELDS: usize = 64;

#[derive(Clone, PartialEq, Eq, Hash)]
enum Term {
    // Model values of a type, by its character.
    Model(u16),
    // The class's values and untyped model values.
    WithUntyped(Shape),
    Set(Shape),
    // Tuples of any length whose values are of a class.
    Sequence(Shape),
    // Tuples of one length, by position, and the empty tuple.
    Tuple(Box<[Shape]>),
    // Records by their keys, ascending by id, and the empty tuple.
    Record(Box<[(Id, Shape)]>),
    // Functions that aren't records, by their keys' and values' classes, and the empty tuple.
    Function(Shape, Shape),
}

/// The store's shapes: each value's, by id, and the terms they name.
#[derive(Default)]
pub(super) struct Shapes {
    of_value: Vec<Shape>,
    terms: Vec<Term>,
    ids: HashMap<Term, Shape>,
    joins: HashMap<(Shape, Shape), Shape>,
}

impl Shapes {
    /// Forgets every value's shape, as when the store's ids or its order of strings change.
    pub(super) fn forget(&mut self) {
        self.of_value.clear();
    }

    /// Forgets the shapes of the values from `id` on, which an overlay numbers anew.
    pub(super) fn forget_from(&mut self, id: Id) {
        self.of_value.truncate(id as usize);
    }

    fn term(&self, shape: Shape) -> Option<&Term> {
        shape
            .checked_sub(FIRST_TERM)
            .map(|index| &self.terms[index as usize])
    }

    fn name(&mut self, term: Term) -> Shape {
        if let Some(&shape) = self.ids.get(&term) {
            return shape;
        }
        let shape = FIRST_TERM + self.terms.len() as Shape;
        self.terms.push(term.clone());
        self.ids.insert(term, shape);
        shape
    }

    // A term over one class, which is no class if that one isn't.
    fn name_over(&mut self, inner: Shape, term: impl FnOnce(Shape) -> Term) -> Shape {
        if inner == NONE {
            return NONE;
        }
        self.name(term(inner))
    }

    // TLC compares a function over an interval with another by its keys only where they are
    // integers, failing at a model value, which the store's order passes: so no class mixes
    // untyped model values with other keys than model values.
    fn name_function(&mut self, keys: Shape, values: Shape) -> Shape {
        if keys == NONE || values == NONE {
            return NONE;
        }
        if let Some(&Term::WithUntyped(inner)) = self.term(keys)
            && inner != BOTTOM
            && !matches!(self.term(inner), Some(Term::Model(_)))
        {
            return NONE;
        }
        self.name(Term::Function(keys, values))
    }

    fn is_function_family(&self, shape: Shape) -> bool {
        matches!(
            self.term(shape),
            Some(Term::Sequence(_) | Term::Tuple(_) | Term::Record(_) | Term::Function(..))
        )
    }

    /// The least class holding both classes' values, or [`NONE`].
    pub(super) fn join(&mut self, left: Shape, right: Shape) -> Shape {
        if left == right {
            return left;
        }
        if left == NONE || right == NONE {
            return NONE;
        }
        if left == BOTTOM {
            return right;
        }
        if right == BOTTOM {
            return left;
        }
        let key = (left.min(right), left.max(right));
        if let Some(&joined) = self.joins.get(&key) {
            return joined;
        }
        let joined = self.join_terms(key.0, key.1);
        self.joins.insert(key, joined);
        joined
    }

    fn join_terms(&mut self, left: Shape, right: Shape) -> Shape {
        let empty_tuple = self.name(Term::Sequence(BOTTOM));
        if left == empty_tuple && self.is_function_family(right) {
            return right;
        }
        if right == empty_tuple && self.is_function_family(left) {
            return left;
        }
        let (Some(left_term), Some(right_term)) = (self.term(left), self.term(right)) else {
            // Scalars of two kinds, or a scalar and a composite value.
            return match (self.term(left), self.term(right)) {
                (Some(Term::WithUntyped(inner)), None) => {
                    let inner = *inner;
                    let joined = self.join(inner, right);
                    self.name_over(joined, Term::WithUntyped)
                }
                (None, Some(Term::WithUntyped(inner))) => {
                    let inner = *inner;
                    let joined = self.join(left, inner);
                    self.name_over(joined, Term::WithUntyped)
                }
                _ => NONE,
            };
        };
        match (left_term.clone(), right_term.clone()) {
            (Term::WithUntyped(left), Term::WithUntyped(right)) => {
                let joined = self.join(left, right);
                self.name_over(joined, Term::WithUntyped)
            }
            (Term::WithUntyped(inner), _) => {
                let joined = self.join(inner, right);
                self.name_over(joined, Term::WithUntyped)
            }
            (_, Term::WithUntyped(inner)) => {
                let joined = self.join(left, inner);
                self.name_over(joined, Term::WithUntyped)
            }
            (Term::Set(left), Term::Set(right)) => {
                let joined = self.join(left, right);
                self.name_over(joined, Term::Set)
            }
            (Term::Sequence(left), Term::Sequence(right)) => {
                let joined = self.join(left, right);
                self.name_over(joined, Term::Sequence)
            }
            (Term::Sequence(inner), Term::Tuple(values))
            | (Term::Tuple(values), Term::Sequence(inner)) => {
                let joined = self.join_all(inner, &values);
                self.name_over(joined, Term::Sequence)
            }
            (Term::Tuple(left), Term::Tuple(right)) if left.len() == right.len() => {
                let mut values = Vec::with_capacity(left.len());
                for (&left, &right) in left.iter().zip(right.iter()) {
                    let joined = self.join(left, right);
                    if joined == NONE {
                        return NONE;
                    }
                    values.push(joined);
                }
                self.name(Term::Tuple(values.into()))
            }
            (Term::Tuple(left), Term::Tuple(right)) => {
                let joined = self.join_all(BOTTOM, &left);
                let joined = self.join_all(joined, &right);
                self.name_over(joined, Term::Sequence)
            }
            (Term::Record(left), Term::Record(right)) => self.join_records(&left, &right),
            (Term::Function(left_keys, left_values), Term::Function(right_keys, right_values)) => {
                let keys = self.join(left_keys, right_keys);
                let values = self.join(left_values, right_values);
                self.name_function(keys, values)
            }
            _ => NONE,
        }
    }

    fn join_all(&mut self, start: Shape, shapes: &[Shape]) -> Shape {
        shapes
            .iter()
            .fold(start, |joined, &shape| self.join(joined, shape))
    }

    // Records of other keys compare no values, so the fields of both, with the classes of the
    // keys they share joined.
    fn join_records(&mut self, left: &[(Id, Shape)], right: &[(Id, Shape)]) -> Shape {
        let mut fields = Vec::with_capacity(left.len().max(right.len()));
        let (mut left_index, mut right_index) = (0, 0);
        while left_index < left.len() || right_index < right.len() {
            let left_field = left.get(left_index).copied();
            let right_field = right.get(right_index).copied();
            let field = match (left_field, right_field) {
                (Some((left_key, left_shape)), Some((right_key, right_shape)))
                    if left_key == right_key =>
                {
                    left_index += 1;
                    right_index += 1;
                    (left_key, self.join(left_shape, right_shape))
                }
                (Some(left_field), Some((right_key, _))) if left_field.0 < right_key => {
                    left_index += 1;
                    left_field
                }
                (Some(left_field), None) => {
                    left_index += 1;
                    left_field
                }
                (_, Some(right_field)) => {
                    right_index += 1;
                    right_field
                }
                (None, None) => unreachable!("a field past both records"),
            };
            if field.1 == NONE || fields.len() == MAXIMUM_FIELDS {
                return NONE;
            }
            fields.push(field);
        }
        self.name(Term::Record(fields.into()))
    }
}

/// The join of the shapes of values, as a walk joins those it assigns to a variable, and the values
/// that widened it: their shapes join to the same class in any store, so another store joins them
/// to take the join over.
pub struct ShapeJoin {
    shape: Shape,
    widening: Vec<Id>,
}

impl Default for ShapeJoin {
    fn default() -> ShapeJoin {
        ShapeJoin {
            shape: BOTTOM,
            widening: Vec::new(),
        }
    }
}

impl ShapeJoin {
    /// Whether any two of the values compare without failing: in `equals` and `compareTo`, and so
    /// in a membership test of one in a set of others.
    pub fn is_comparable(&self) -> bool {
        self.shape != NONE
    }

    /// The values that widened the join, in its store: the last one, where it is no class.
    pub fn widening(&self) -> &[Id] {
        &self.widening
    }
}

impl Store {
    /// Whether TLC's test of `element`'s membership in `set`, a set of the store's own, compares
    /// values that may fail: if not, its answer is whether the set holds the element's id.
    pub(super) fn is_member_by_id(&mut self, element: Id, set: Id) -> bool {
        let set_shape = self.shape_of(set);
        let Some(&Term::Set(elements)) = self.shapes.term(set_shape) else {
            // The empty set, or a set of values that may fail to compare.
            return false;
        };
        let element = self.shape_of(element);
        self.shapes.join(element, elements) != NONE
    }

    /// Joins a value's shape into a join, which stays no class once it is one.
    #[inline]
    pub fn join_shape(&mut self, join: &mut ShapeJoin, id: Id) {
        if join.shape == NONE {
            return;
        }
        let shape = self.shape_of(id);
        if shape == join.shape {
            return;
        }
        let joined = self.shapes.join(join.shape, shape);
        if joined != join.shape {
            join.shape = joined;
            join.widening.push(id);
        }
    }

    fn shape_of(&mut self, id: Id) -> Shape {
        let index = id as usize;
        if let Some(&shape) = self.shapes.of_value.get(index)
            && shape != UNKNOWN
        {
            return shape;
        }
        let shape = self.find_shape(id);
        if self.shapes.of_value.len() <= index {
            self.shapes.of_value.resize(index + 1, UNKNOWN);
        }
        self.shapes.of_value[index] = shape;
        shape
    }

    fn find_shape(&mut self, id: Id) -> Shape {
        let meta = *self.meta(id);
        if self.is_kept_lazy(id) {
            return NONE;
        }
        let is_ordered = |store: &Store| store.text(meta.payload).rank < store.unordered_rank;
        match meta.kind {
            KIND_BOOL => BOOL,
            KIND_INT => INT,
            KIND_STRING if is_ordered(self) => STRING,
            KIND_MODEL if is_ordered(self) => match self.get_model_type(id) {
                0 => self.shapes.name(Term::WithUntyped(BOTTOM)),
                model_type => self.shapes.name(Term::Model(model_type)),
            },
            KIND_SET => {
                let offset = meta.payload as usize;
                let mut joined = BOTTOM;
                for index in 0..meta.size as usize {
                    let shape = self.shape_of(self.word(offset + index));
                    joined = self.shapes.join(joined, shape);
                    if joined == NONE {
                        return NONE;
                    }
                }
                self.shapes.name(Term::Set(joined))
            }
            // The store interns a tuple's keys past the small integers as it compares the tuple.
            KIND_TUPLE if meta.size > SMALL_INT_MAX as u32 => NONE,
            KIND_TUPLE => {
                let offset = meta.payload as usize;
                let mut values = Vec::with_capacity(meta.size as usize);
                for index in 0..meta.size as usize {
                    let shape = self.shape_of(self.word(offset + index));
                    if shape == NONE {
                        return NONE;
                    }
                    values.push(shape);
                }
                match values.first() {
                    None => self.shapes.name(Term::Sequence(BOTTOM)),
                    Some(&first) if values.iter().all(|&shape| shape == first) => {
                        self.shapes.name(Term::Sequence(first))
                    }
                    Some(_) => self.shapes.name(Term::Tuple(values.into())),
                }
            }
            KIND_FUNCTION => {
                let (offset, size) = (meta.payload as usize, meta.size as usize);
                let is_record = self.is_record(id);
                let mut fields = Vec::with_capacity(if is_record { size } else { 0 });
                let (mut keys, mut values) = (BOTTOM, BOTTOM);
                for index in 0..size {
                    let key = self.word(offset + index);
                    let key_shape = self.shape_of(key);
                    let value = self.shape_of(self.word(offset + size + index));
                    if key_shape == NONE || value == NONE {
                        return NONE;
                    }
                    if is_record {
                        fields.push((key, value));
                        continue;
                    }
                    keys = self.shapes.join(keys, key_shape);
                    values = self.shapes.join(values, value);
                    if keys == NONE || values == NONE {
                        return NONE;
                    }
                }
                if is_record {
                    fields.sort_unstable_by_key(|&(key, _)| key);
                    return self.shapes.name(Term::Record(fields.into()));
                }
                self.shapes.name_function(keys, values)
            }
            _ => NONE,
        }
    }
}
