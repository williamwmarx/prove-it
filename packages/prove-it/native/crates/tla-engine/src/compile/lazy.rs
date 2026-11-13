//! The sets TLC keeps lazy, enumerated in TLC's order (DESIGN.md 3.3). Where the TypeScript engine
//! rebuilds the interpreter's value of such a set (`reference`) and asks the interpreter for its
//! elements (`getStreamedElements`, `getQuantifierElements`), this builds a [`Lazy`] of the same
//! shape and enumerates it as `values.ts` does: `enumerate` is `toFiniteSet`'s order (`enumerateSet`),
//! the order a quantifier binds, and `stream` is `getStreamedElements`', the order `x' \in S`
//! assigns, in which a `\cup` the set hasn't cached yields an element of both operands twice.

use std::sync::Arc;

use tla_values::store::{
    EMPTY_SET, KIND_BOOL, KIND_INT, KIND_LAZY_FUNCTION, KIND_MODEL, KIND_SET, KIND_STRING,
    KIND_TUPLE, Outcome, is_function_kind,
};
use tla_values::{Bail, Id};

use super::sets::{is_in_named, not_in};
use crate::machine::Machine;

// Beyond these the interpreter would list more elements than a search can use.
const MAXIMUM_SUBSET_BASE: usize = 20;
/// TLC counts a power set's elements in an int, and fails counting those of SUBSET S where S has
/// this many elements or more (`SubsetValue.size`).
pub(crate) const OVERFLOWING_SUBSET_BASE: usize = 31;
/// What enumerating a set of functions stops with where TLC can't enumerate its domain.
pub(crate) const INFINITE_DOMAIN: &str = "enumerated [D -> R] with D infinite";
pub(crate) const SUBSET_OVERFLOW: &str = "an overflow counting the elements of a power set";
pub(crate) const MAXIMUM_ELEMENTS: f64 = (1u64 << 24) as f64;
/// What printing a set of functions, records or tuples stops with where TLC's `toString`, which
/// PrintT calls unchecked, fails on a part.
pub(crate) const UNSIZED_PRINT: &str = "printed a set with a part TLC can't size";
/// What printing such a set stops with where the engine can't tell whether TLC's `toString` fails.
const UNSURE_PRINT: Bail = Bail("unsupported: printing a set whose part TLC may fail to size");
/// The fewest elements TLC prints a lazy set as written rather than enumerated
/// (`TLCGlobals.enumBound`).
const ENUM_BOUND: u64 = 2000;
/// What streaming a [`Lazy::Kept`] other than as its normalized set stops with.
const KEPT_STREAMED: &str =
    "unsupported: streaming a lazy set TLC may have normalized at an earlier use";

/// What a set expression's value is, as the interpreter builds it.
pub(crate) type Reference = Arc<dyn Fn(&mut Machine<'_>) -> Outcome<Lazy> + Send + Sync>;

/// A filter's test of an element, with its names bound to it.
pub(crate) type Test = Arc<dyn Fn(&mut Machine<'_>, Id) -> Outcome<bool> + Send + Sync>;

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Operator {
    Union,
    Intersection,
    Difference,
}

/// The interpreter's value of a set: a normalized set (TLC's SetEnumValue), or one of the sets
/// TLC implements lazily.
#[derive(Clone)]
pub(crate) enum Lazy {
    Set(Id),
    /// Nat, Int or STRING, which TLC tests for membership and can't enumerate.
    Infinite(&'static str),
    /// Another set TLC can't enumerate, such as `{n \in Nat : p}` or `Seq(S)`, with the
    /// engine's test of membership in it.
    Tested(Test),
    Subset(Box<Lazy>),
    FunctionSet(Box<Lazy>, Box<Lazy>),
    /// The keys in TLC's order, each with its set.
    RecordSet(Vec<Id>, Vec<Lazy>),
    Product(Vec<Lazy>),
    Filtered(Box<Lazy>, Test),
    Operation(Operator, Box<Lazy>, Box<Lazy>),
    /// `UNION S`, with S's elements the sets the engine holds, each enumerated as its normalized
    /// set, or S an [`Lazy::Enumeration`].
    Union(Box<Lazy>),
    /// A set that may stream duplicates, as TLC keeps it for later uses (`LazyValue`, a constant
    /// definition): a use that sizes, compares or fingerprints it caches it as its normalized set
    /// (`convertAndCache`), which the engine doesn't follow, so streaming it stops where it
    /// streams an element twice or out of the normalized set's order.
    Kept(Box<Lazy>),
    /// `{e1, …, en}` as written, some of whose elements are sets TLC keeps lazy: TLC sorts it as
    /// it first enumerates it, which caches each element it compares as the receiver.
    Enumeration(Vec<Lazy>),
}

impl Lazy {
    /// Whether the set is one TLC may stream an element of twice: a UNION or `\cup` it keeps
    /// lazy (`UnionValue`, `SetCupValue`), or a filter, `\cap` or `\` of a set it keeps lazy
    /// (`SetPredValue`, `SetCapValue`, `SetDiffValue`), each enumerating what it is built of as
    /// built. The other sets TLC keeps lazy stream none twice.
    pub(crate) fn may_stream_duplicates(&self) -> bool {
        matches!(
            self,
            Lazy::Union(_) | Lazy::Operation(..) | Lazy::Filtered(..) | Lazy::Kept(_)
        )
    }

    /// Whether streaming the set yields other than its normalized set's elements in order: an
    /// element twice, or one out of order.
    pub(crate) fn streams_unnormalized(&self, machine: &mut Machine<'_>) -> Outcome<bool> {
        let streamed = self.stream(machine)?;
        is_unnormalized(machine, &streamed)
    }

    /// The set as TLC keeps it for later uses.
    pub(crate) fn kept(self) -> Lazy {
        if matches!(self, Lazy::Kept(_)) || !self.may_stream_duplicates() {
            return self;
        }
        Lazy::Kept(Box::new(self))
    }

    fn is_enumerable(&self) -> bool {
        !matches!(self, Lazy::Infinite(_) | Lazy::Tested(_))
    }

    /// Whether the set is or is built of a set TLC can't enumerate.
    pub(crate) fn is_infinite(&self) -> bool {
        match self {
            Lazy::Set(_) => false,
            Lazy::Infinite(_) | Lazy::Tested(_) => true,
            Lazy::Subset(base) | Lazy::Filtered(base, _) | Lazy::Union(base) => base.is_infinite(),
            Lazy::Enumeration(elements) => elements.iter().any(Lazy::is_infinite),
            Lazy::FunctionSet(domain, range) => domain.is_infinite() || range.is_infinite(),
            Lazy::RecordSet(_, sets) | Lazy::Product(sets) => sets.iter().any(Lazy::is_infinite),
            Lazy::Operation(_, left, right) => left.is_infinite() || right.is_infinite(),
            Lazy::Kept(kept) => kept.is_infinite(),
        }
    }

    fn set(machine: &Machine<'_>, id: Id) -> Outcome<Id> {
        if machine.store.kind_of(id) == KIND_SET {
            Ok(id)
        } else {
            Err(Bail("enumerated a non-set"))
        }
    }

    /// A set whose elements are those of a set enumeration in this order.
    fn of(machine: &mut Machine<'_>, elements: &[Id]) -> Outcome<Lazy> {
        Ok(Lazy::Set(machine.store.set_of(elements)?))
    }

    /// `S \cup T`, `S \cap T` or `S \ T` as the interpreter's builtins build it: two set
    /// enumerations combine at once, a set enumeration and another set element by element (a
    /// union only when the enumeration is empty), and anything else lazily, a union with the set
    /// enumeration first.
    pub(crate) fn combine(
        machine: &mut Machine<'_>,
        operator: Operator,
        left: Lazy,
        right: Lazy,
    ) -> Outcome<Lazy> {
        match (left, right) {
            (Lazy::Set(left), Lazy::Set(right)) => {
                let (left, right) = (Self::set(machine, left)?, Self::set(machine, right)?);
                Ok(Lazy::Set(match operator {
                    Operator::Union => machine.store.union(left, right)?,
                    Operator::Intersection => machine.store.intersection(left, right)?,
                    Operator::Difference => machine.store.difference(left, right)?,
                }))
            }
            (Lazy::Set(set), other) => Self::combine_reducible(machine, operator, set, other),
            (other, Lazy::Set(set)) if operator != Operator::Difference => {
                Self::combine_reducible(machine, operator, set, other)
            }
            (left, right) => Ok(Lazy::Operation(operator, Box::new(left), Box::new(right))),
        }
    }

    fn combine_reducible(
        machine: &mut Machine<'_>,
        operator: Operator,
        set: Id,
        other: Lazy,
    ) -> Outcome<Lazy> {
        let set = Self::set(machine, set)?;
        let elements = machine.store.set_elements(set).to_vec();
        if operator == Operator::Union {
            return Ok(if elements.is_empty() {
                other
            } else {
                Lazy::Operation(operator, Box::new(Lazy::Set(set)), Box::new(other))
            });
        }
        let is_kept = operator == Operator::Intersection;
        let mut kept = Vec::new();
        for element in elements {
            if other.contains(machine, element)? == is_kept {
                kept.push(element);
            }
        }
        Self::of(machine, &kept)
    }

    /// `{x \in S : P}` as the interpreter builds it: a set enumeration filtered at once, and any
    /// other set lazily.
    pub(crate) fn filter(machine: &mut Machine<'_>, base: Lazy, test: Test) -> Outcome<Lazy> {
        let Lazy::Set(set) = base else {
            return Ok(Lazy::Filtered(Box::new(base), test));
        };
        let set = Self::set(machine, set)?;
        let mut kept = Vec::new();
        for element in machine.store.set_elements(set).to_vec() {
            if test(machine, element)? {
                kept.push(element);
            }
        }
        Ok(Lazy::Set(machine.store.set_of_sorted(&kept)))
    }

    /// The elements of a set enumeration as TLC holds them once it has sorted them
    /// (`SetEnumValue.normalize`): `ValueVec.sort` inserts each element after the first into
    /// those before it, comparing it as the receiver, which caches a set TLC keeps lazy as its
    /// normalized set, and drops it where it equals one before it. The first is compared only as
    /// the argument, and stays as built.
    fn sort_enumeration(machine: &mut Machine<'_>, elements: &[Lazy]) -> Outcome<Vec<Lazy>> {
        if elements.len() < 2 {
            return Ok(elements.to_vec());
        }
        let mut values = Vec::with_capacity(elements.len());
        for element in elements {
            values.push(match element {
                Lazy::Set(value) => *value,
                _ => {
                    let set = element.enumerate(machine)?;
                    machine.store.set_of(&set)?
                }
            });
        }
        let mut sorted = vec![0];
        for index in 1..values.len() {
            let (mut low, mut high, mut position, mut order) = (0, sorted.len(), 0, 0);
            while low < high {
                position = low + ((high - low) >> 1);
                order = machine
                    .store
                    .compare(values[index], values[sorted[position]])?;
                if order == 0 {
                    break;
                }
                if order < 0 {
                    high = position;
                } else {
                    low = position + 1;
                }
            }
            if order != 0 {
                sorted.insert(if order < 0 { position } else { position + 1 }, index);
            }
        }
        Ok(sorted
            .into_iter()
            .map(|index| match index {
                0 => elements[0].clone(),
                _ => Lazy::Set(values[index]),
            })
            .collect())
    }

    /// The elements in `toFiniteSet`'s order, which a quantifier binds.
    pub(crate) fn enumerate(&self, machine: &mut Machine<'_>) -> Outcome<Vec<Id>> {
        self.elements(machine, false)
    }

    /// The elements in `getStreamedElements`' order, which `x' \in S` assigns.
    pub(crate) fn stream(&self, machine: &mut Machine<'_>) -> Outcome<Vec<Id>> {
        self.elements(machine, true)
    }

    // A set of functions, records or tuples streams the sets it combines (`isStreamedApart`),
    // where enumerating them gives the same elements in the same order unless one streams a
    // union, so streaming each in turn is `streamElements`' choice of the two.
    fn elements(&self, machine: &mut Machine<'_>, is_streamed: bool) -> Outcome<Vec<Id>> {
        match self {
            Lazy::Set(set) => Ok(machine
                .store
                .set_elements(Self::set(machine, *set)?)
                .to_vec()),
            Lazy::Infinite(_) | Lazy::Tested(_) => Err(Bail("enumerated an infinite set")),
            Lazy::Subset(base) => {
                // SubsetValue sizes and lists its base, never streaming it.
                let base = base.elements(machine, false)?;
                if base.len() >= OVERFLOWING_SUBSET_BASE {
                    return Err(Bail(SUBSET_OVERFLOW));
                }
                if base.len() > MAXIMUM_SUBSET_BASE {
                    return Err(Bail("a power set too large to build"));
                }
                let mut subsets = Vec::new();
                for size in 0..=base.len() {
                    let mut indices: Vec<usize> = (0..size).collect();
                    loop {
                        let chosen: Vec<Id> = indices.iter().map(|&index| base[index]).collect();
                        subsets.push(machine.store.set_of(&chosen)?);
                        if !advance_combination(&mut indices, base.len()) {
                            break;
                        }
                    }
                }
                Ok(subsets)
            }
            Lazy::FunctionSet(domain, range) => {
                if self.is_empty(machine)? {
                    return Ok(Vec::new());
                }
                if !domain.is_enumerable() {
                    return Err(Bail(INFINITE_DOMAIN));
                }
                let is_sorted = matches!(**domain, Lazy::Set(_));
                let keys = domain.elements(machine, false)?;
                if keys.is_empty() {
                    return Ok(vec![machine.store.function_of_sorted(&[], &[])]);
                }
                if !range.is_enumerable() {
                    return Err(Bail("enumerated [D -> R] with R infinite"));
                }
                let choices = range.elements(machine, is_streamed)?;
                let lists = vec![choices; keys.len()];
                cartesian(&lists, |values| {
                    let function = if is_sorted {
                        machine.store.function_of_sorted(&keys, values)
                    } else {
                        machine.store.function_of(&keys, values)?
                    };
                    Ok(machine.store.mark_built_as_function(function))
                })
            }
            Lazy::RecordSet(keys, sets) => {
                let Some(lists) = self.components(machine, sets, is_streamed)? else {
                    return Ok(Vec::new());
                };
                cartesian(&lists, |values| {
                    Ok(machine.store.function_of_sorted(keys, values))
                })
            }
            Lazy::Product(factors) => {
                let Some(lists) = self.components(machine, factors, is_streamed)? else {
                    return Ok(Vec::new());
                };
                cartesian(&lists, |values| Ok(machine.store.tuple_of(values)))
            }
            Lazy::Filtered(base, test) => {
                if !base.is_enumerable() {
                    return Err(Bail("filtered an infinite set"));
                }
                let mut kept = Vec::new();
                for element in base.elements(machine, is_streamed)? {
                    if test(machine, element)? {
                        kept.push(element);
                    }
                }
                Ok(kept)
            }
            Lazy::Union(base) => {
                // `getUnionSets`, then each set in turn: streamed, duplicates and all, or merged
                // into the normalized set.
                if !base.is_enumerable() {
                    return Err(Bail("enumerated UNION of an infinite set"));
                }
                let sets = match &**base {
                    Lazy::Enumeration(sets) => Self::sort_enumeration(machine, sets)?,
                    _ => base
                        .elements(machine, is_streamed)?
                        .into_iter()
                        .map(Lazy::Set)
                        .collect(),
                };
                let mut elements = Vec::new();
                let mut union = EMPTY_SET;
                for set in sets {
                    let streamed = set.elements(machine, is_streamed)?;
                    if is_streamed {
                        elements.extend(streamed);
                    } else {
                        let set = machine.store.set_of(&streamed)?;
                        union = machine.store.union(union, set)?;
                    }
                }
                Ok(if is_streamed {
                    elements
                } else {
                    machine.store.set_elements(union).to_vec()
                })
            }
            Lazy::Enumeration(elements) => {
                let sorted = Self::sort_enumeration(machine, elements)?;
                let mut values = Vec::with_capacity(sorted.len());
                for element in sorted {
                    values.push(match element {
                        Lazy::Set(value) => value,
                        _ => {
                            let set = element.enumerate(machine)?;
                            machine.store.set_of(&set)?
                        }
                    });
                }
                Ok(values)
            }
            Lazy::Operation(Operator::Union, left, right) => {
                if !left.is_enumerable() || !right.is_enumerable() {
                    return Err(Bail("enumerated a union with an infinite set"));
                }
                let left = left.elements(machine, is_streamed)?;
                let right = right.elements(machine, is_streamed)?;
                if is_streamed {
                    return Ok([left, right].concat());
                }
                sorted_union(machine, left, right)
            }
            Lazy::Kept(kept) => {
                if !is_streamed {
                    return kept.enumerate(machine);
                }
                let streamed = kept.stream(machine)?;
                if is_unnormalized(machine, &streamed)? {
                    return Err(Bail(KEPT_STREAMED));
                }
                Ok(streamed)
            }
            Lazy::Operation(operator, left, right) => {
                let is_left_enumerated = *operator == Operator::Difference || left.is_enumerable();
                let (enumerated, other) = if is_left_enumerated {
                    (left, right)
                } else {
                    (right, left)
                };
                if !enumerated.is_enumerable() {
                    return Err(Bail("enumerated an operation on infinite sets"));
                }
                let is_kept = *operator == Operator::Intersection;
                let mut kept = Vec::new();
                for element in enumerated.elements(machine, is_streamed)? {
                    if other.contains(machine, element)? == is_kept {
                        kept.push(element);
                    }
                }
                Ok(kept)
            }
        }
    }

    // The elements of each set a set of records or tuples combines, or None for an empty one:
    // TLC decides that it's empty first, and then enumerates its sets in turn.
    fn components(
        &self,
        machine: &mut Machine<'_>,
        sets: &[Lazy],
        is_streamed: bool,
    ) -> Outcome<Option<Vec<Vec<Id>>>> {
        if self.is_empty(machine)? {
            return Ok(None);
        }
        let mut lists = Vec::with_capacity(sets.len());
        for set in sets {
            if !set.is_enumerable() {
                return Err(Bail("enumerated a product of an infinite set"));
            }
            let elements = set.elements(machine, is_streamed)?;
            if elements.is_empty() {
                return Ok(None);
            }
            lists.push(elements);
        }
        Ok(Some(lists))
    }

    // `isEmptySet`.
    pub(crate) fn is_empty(&self, machine: &mut Machine<'_>) -> Outcome<bool> {
        Ok(match self {
            Lazy::Set(set) => machine.store.size_of(Self::set(machine, *set)?) == 0,
            Lazy::Infinite(_) | Lazy::Subset(_) => false,
            Lazy::Enumeration(elements) => elements.is_empty(),
            Lazy::FunctionSet(domain, range) => {
                !domain.is_empty(machine)? && range.is_empty(machine)?
            }
            Lazy::RecordSet(_, sets) | Lazy::Product(sets) => {
                for set in sets {
                    if set.is_empty(machine)? {
                        return Ok(true);
                    }
                }
                false
            }
            // `UnionValue.isEmpty`: each set of the union is.
            Lazy::Union(base) if base.is_enumerable() => {
                for set in base.enumerate(machine)? {
                    let set = Self::set(machine, set)?;
                    if machine.store.size_of(set) != 0 {
                        return Ok(false);
                    }
                }
                true
            }
            Lazy::Kept(kept) => kept.is_empty(machine)?,
            Lazy::Tested(_) | Lazy::Filtered(..) | Lazy::Operation(..) | Lazy::Union(_) => {
                self.enumerate(machine)?.is_empty()
            }
        })
    }

    /// TLC's `size` of the set, which sets of functions, records and tuples answer from their
    /// parts: an empty part decides before one TLC can't enumerate, or one too large to, is
    /// asked, and a range of one element makes one function whatever the domain
    /// (`SetOfFcnsValue.size`, `SetOfRcdsValue.size`, `SetOfTuplesValue.size`).
    pub(crate) fn size(&self, machine: &mut Machine<'_>) -> Outcome<u64> {
        const OVERFLOW: Bail = Bail("a lazy set too large to count");
        let bounded = |size: u64| {
            if size > i32::MAX as u64 {
                Err(OVERFLOW)
            } else {
                Ok(size)
            }
        };
        match self {
            Lazy::Set(set) => Ok(u64::from(machine.store.size_of(Self::set(machine, *set)?))),
            Lazy::Infinite(_) | Lazy::Tested(_) => {
                Err(Bail("counted the elements of an infinite set"))
            }
            Lazy::Subset(base) => {
                let size = base.size(machine)?;
                if size >= 31 {
                    return Err(Bail(SUBSET_OVERFLOW));
                }
                Ok(1 << size)
            }
            Lazy::FunctionSet(domain, range) => {
                if domain.is_empty(machine)? {
                    return Ok(1);
                }
                if range.is_empty(machine)? {
                    return Ok(0);
                }
                let range = range.size(machine)?;
                if range == 1 {
                    return Ok(1);
                }
                let domain = domain.size(machine)?;
                (0..domain).try_fold(1u64, |size, _| bounded(size * range))
            }
            Lazy::RecordSet(_, sets) | Lazy::Product(sets) => {
                if self.is_empty(machine)? {
                    return Ok(0);
                }
                sets.iter()
                    .try_fold(1u64, |size, set| bounded(size * set.size(machine)?))
            }
            Lazy::Kept(kept) => kept.size(machine),
            Lazy::Filtered(..) | Lazy::Operation(..) | Lazy::Union(_) | Lazy::Enumeration(_) => {
                let elements = self.enumerate(machine)?;
                let set = machine.store.set_of(&elements)?;
                Ok(u64::from(machine.store.size_of(set)))
            }
        }
    }

    /// Membership as the interpreter tests it (`isElementOf`), failing where it fails.
    pub(crate) fn contains(&self, machine: &mut Machine<'_>, element: Id) -> Outcome<bool> {
        let kind = machine.store.kind_of(element);
        match self {
            Lazy::Set(set) => {
                let set = Self::set(machine, *set)?;
                machine.store.is_member(element, set)
            }
            // Seq(S) holds sequences of S's elements, which its reference doesn't keep.
            Lazy::Infinite(name) => is_in_named(machine, name, element),
            Lazy::Tested(test) => test(machine, element),
            Lazy::Subset(base) => {
                if kind != KIND_SET {
                    return Err(Bail("a membership in SUBSET of a non-set"));
                }
                for index in 0..machine.store.size_of(element) {
                    let value = machine.store.element_at(element, index);
                    if !base.contains(machine, value)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Lazy::FunctionSet(domain, range) => {
                if !is_function_kind(kind) {
                    return not_in(
                        machine,
                        element,
                        "a mistyped membership in a set of functions",
                    );
                }
                let keys = domain.enumerate(machine)?;
                let domain = machine.store.set_of(&keys)?;
                let size = machine.store.size_of(element);
                if size != machine.store.size_of(domain) {
                    return Ok(false);
                }
                for index in 0..size {
                    let key = machine.store.get_key(element, index);
                    let expected = machine.store.element_at(domain, index);
                    if key != expected && machine.store.compare(key, expected)? != 0 {
                        return Ok(false);
                    }
                }
                for index in 0..size {
                    let value = machine.store.get_range_value(element, index);
                    if !range.contains(machine, value)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Lazy::RecordSet(keys, sets) => {
                let size = machine.store.size_of(element);
                let is_record = is_function_kind(kind)
                    && (0..size).all(|index| {
                        let key = machine.store.get_key(element, index);
                        machine.store.kind_of(key) == KIND_STRING
                    });
                if !is_record {
                    return not_in(
                        machine,
                        element,
                        "a mistyped membership in a set of records",
                    );
                }
                if size as usize != keys.len() {
                    return Ok(false);
                }
                for (&key, set) in keys.iter().zip(sets) {
                    let position = machine.store.find_key(element, key)?;
                    if position < 0 {
                        return Ok(false);
                    }
                    let value = machine.store.get_range_value(element, position as u32);
                    if !set.contains(machine, value)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Lazy::Product(factors) => {
                if kind != KIND_TUPLE {
                    // A function over integers other than 1..n isn't a tuple, and isn't one of
                    // the set's; anything else fails.
                    let size = machine.store.size_of(element);
                    let is_integer_function = is_function_kind(kind)
                        && (0..size).all(|index| {
                            let key = machine.store.get_key(element, index);
                            machine.store.kind_of(key) == KIND_INT
                        });
                    return if is_integer_function {
                        Ok(false)
                    } else {
                        not_in(machine, element, "a mistyped membership in a set of tuples")
                    };
                }
                if machine.store.size_of(element) as usize != factors.len() {
                    return Ok(false);
                }
                for (index, factor) in factors.iter().enumerate() {
                    let value = machine.store.get_range_value(element, index as u32);
                    if !factor.contains(machine, value)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Lazy::Filtered(base, test) => {
                Ok(base.contains(machine, element)? && test(machine, element)?)
            }
            Lazy::Kept(kept) => kept.contains(machine, element),
            Lazy::Enumeration(_) => {
                let elements = self.enumerate(machine)?;
                let set = machine.store.set_of(&elements)?;
                machine.store.is_member(element, set)
            }
            Lazy::Union(base) => {
                if !base.is_enumerable() {
                    return Err(Bail("a membership in UNION of an infinite set"));
                }
                for set in base.enumerate(machine)? {
                    let set = Self::set(machine, set)?;
                    if machine.store.is_member(element, set)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            Lazy::Operation(operator, left, right) => {
                let is_left = left.contains(machine, element)?;
                Ok(match operator {
                    Operator::Union => is_left || right.contains(machine, element)?,
                    Operator::Intersection => is_left && right.contains(machine, element)?,
                    Operator::Difference => is_left && !right.contains(machine, element)?,
                })
            }
        }
    }
}

/// What TLC found a set of functions, records or tuples it prints to hold, from its parts, before
/// it enumerated any (`Lazy::check_printed`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PrintedSet {
    /// None, as a part is empty, or the range of functions of a nonempty domain is.
    Empty,
    /// The one function of an empty domain.
    OfEmptyFunction,
    /// What enumerating it gives.
    Enumerated,
}

// What TLC's `toString` of a set of functions, records or tuples asks of its parts, unchecked as
// PrintT prints: `Err(UNSIZED_PRINT)` where TLC fails, `Err(UNSURE_PRINT)` where the engine can't
// tell, and otherwise the answer.
impl Lazy {
    /// Whether TLC's `toString` of this set of functions, records or tuples prints it, as PrintT
    /// calls it unchecked: it sizes the parts in order up to an empty one, failing on a part it
    /// can't size, and below `ENUM_BOUND` elements enumerates the set, which first tests each part
    /// for emptiness up to an empty one, failing on a non-set (`SetOfTuplesValue.toString` and
    /// `elements`, and their siblings for records and functions). `Err(UNSIZED_PRINT)` where TLC
    /// fails, and otherwise what TLC found the set to hold before it enumerated any part.
    pub(crate) fn check_printed(&self, machine: &mut Machine<'_>) -> Outcome<PrintedSet> {
        let size = match self {
            Lazy::RecordSet(_, parts) | Lazy::Product(parts) => {
                let mut size: u64 = 1;
                for part in parts {
                    let part = part.printed_size(machine)?;
                    if part == 0 {
                        size = 0;
                        break;
                    }
                    size = size.saturating_mul(part);
                }
                size
            }
            Lazy::FunctionSet(domain, range) => {
                if domain.printed_is_empty(machine)? {
                    1
                } else {
                    let domain = domain.printed_size(machine)?;
                    let range = range.printed_size(machine)?;
                    (0..domain.min(32)).fold(1u64, |size, _| size.saturating_mul(range))
                }
            }
            _ => return Err(UNSURE_PRINT),
        };
        if size >= ENUM_BOUND {
            return Ok(PrintedSet::Enumerated);
        }
        match self {
            Lazy::RecordSet(_, parts) | Lazy::Product(parts) => {
                for part in parts {
                    if part.printed_is_empty(machine)? {
                        return Ok(PrintedSet::Empty);
                    }
                }
            }
            Lazy::FunctionSet(domain, _) if domain.printed_is_empty(machine)? => {
                return Ok(PrintedSet::OfEmptyFunction);
            }
            Lazy::FunctionSet(_, range) if range.printed_is_empty(machine)? => {
                return Ok(PrintedSet::Empty);
            }
            _ => {}
        }
        Ok(PrintedSet::Enumerated)
    }

    /// TLC's `isFinite` of the set: `None` where TLC fails, as it does asking whether
    /// `{x \in S : p}` is finite for an infinite S, or where the engine can't tell what TLC
    /// answers.
    pub(crate) fn is_finite(&self, machine: &mut Machine<'_>) -> Option<bool> {
        self.finiteness(machine).flatten()
    }

    // TLC's `isFinite`: `None` where TLC may fail, `Some(None)` where it answers without failing
    // but the engine can't tell which way, as for Seq(S), which is finite where S is empty.
    fn finiteness(&self, machine: &mut Machine<'_>) -> Option<Option<bool>> {
        let is_empty = |set: &Lazy, machine: &mut Machine<'_>| set.printed_is_empty(machine).ok();
        Some(match self {
            Lazy::Set(id) => {
                if machine.store.kind_of(*id) != KIND_SET {
                    return None;
                }
                Some(true)
            }
            Lazy::Enumeration(_) => Some(true),
            // Nat, Int and STRING (`UserValue.isFinite`), and Seq(S), whose S isn't held.
            Lazy::Infinite(name) => (*name != "Seq").then_some(false),
            Lazy::Tested(_) | Lazy::Union(_) => return None,
            Lazy::Subset(base) | Lazy::Kept(base) => base.finiteness(machine)?,
            // `SetOfFcnsValue.isFinite`: the first of these that holds.
            Lazy::FunctionSet(domain, range) => {
                let is_finite_domain = domain.finiteness(machine)?;
                let is_empty_domain = Some(is_empty(domain, machine)?);
                let is_finite_range = range.finiteness(machine)?;
                let is_empty_range = Some(is_empty(range, machine)?);
                let is_range_of_one = if is_finite_range == Some(false) {
                    Some(false)
                } else {
                    Some(range.printed_size(machine).ok()? == 1)
                };
                any([
                    all([is_finite_domain, is_empty_domain]),
                    all([is_finite_range, is_empty_range]),
                    all([is_finite_domain, is_finite_range]),
                    all([is_finite_range, is_range_of_one]),
                ])
            }
            // `SetOfRcdsValue.isFinite` and `SetOfTuplesValue.isFinite`: a finite empty part, or
            // every part finite.
            Lazy::RecordSet(_, parts) | Lazy::Product(parts) => {
                let mut empty_parts = Vec::with_capacity(parts.len());
                let mut finite_parts = Vec::with_capacity(parts.len());
                for part in parts {
                    let is_finite = part.finiteness(machine)?;
                    finite_parts.push(is_finite);
                    empty_parts.push(all([is_finite, Some(is_empty(part, machine)?)]));
                }
                any([any(empty_parts), all(finite_parts)])
            }
            // `SetPredValue.isFinite`, which fails where S isn't finite.
            Lazy::Filtered(base, _) => match base.finiteness(machine)? {
                Some(true) => Some(true),
                _ => return None,
            },
            // `SetCupValue.isFinite`, `SetCapValue.isFinite` and `SetDiffValue.isFinite`, which
            // answer as the set enumeration TLC reduces the operation to does.
            Lazy::Operation(operator, left, right) => {
                let is_left_finite = left.finiteness(machine)?;
                match (operator, is_left_finite) {
                    (Operator::Union, Some(false)) => Some(false),
                    (Operator::Union, _) => all([is_left_finite, right.finiteness(machine)?]),
                    (Operator::Intersection | Operator::Difference, Some(true)) => Some(true),
                    (Operator::Intersection, _) => match right.finiteness(machine)? {
                        Some(true) => Some(true),
                        _ => return None,
                    },
                    (Operator::Difference, _) => match right.finiteness(machine)? {
                        Some(true) => is_left_finite,
                        _ => return None,
                    },
                }
            }
        })
    }

    // A part's `size`: a set's count, a function's, tuple's or record's number of keys, and a
    // failure for any other value or a set TLC can't enumerate.
    fn printed_size(&self, machine: &mut Machine<'_>) -> Outcome<u64> {
        match self {
            Lazy::Set(id) => {
                let kind = machine.store.kind_of(*id);
                if kind == KIND_SET || kind == KIND_TUPLE || is_function_kind(kind) {
                    Ok(u64::from(machine.store.size_of(*id)))
                } else if matches!(kind, KIND_INT | KIND_STRING | KIND_BOOL | KIND_MODEL) {
                    Err(Bail(UNSIZED_PRINT))
                } else {
                    Err(UNSURE_PRINT)
                }
            }
            // `UserValue.size`: Nat, Int, STRING and Seq(S).
            Lazy::Infinite(_) => Err(Bail(UNSIZED_PRINT)),
            Lazy::Subset(base) => match base.printed_size(machine)? {
                size if size < 31 => Ok(1 << size),
                _ => Err(UNSURE_PRINT),
            },
            Lazy::FunctionSet(..) | Lazy::RecordSet(..) | Lazy::Product(..) => {
                self.size(machine).map_err(|_| UNSURE_PRINT)
            }
            _ => Err(UNSURE_PRINT),
        }
    }

    // A part's `isEmpty` (`Value.isEmpty`), which fails on any value but a set.
    fn printed_is_empty(&self, machine: &mut Machine<'_>) -> Outcome<bool> {
        match self {
            Lazy::Set(id) => {
                if machine.store.kind_of(*id) == KIND_SET {
                    Ok(machine.store.size_of(*id) == 0)
                } else if matches!(
                    machine.store.kind_of(*id),
                    KIND_INT | KIND_STRING | KIND_BOOL | KIND_MODEL | KIND_TUPLE
                ) || is_function_kind(machine.store.kind_of(*id))
                    || machine.store.kind_of(*id) == KIND_LAZY_FUNCTION
                {
                    Err(Bail(UNSIZED_PRINT))
                } else {
                    Err(UNSURE_PRINT)
                }
            }
            // Nat, Int, STRING and Seq(S) aren't empty (`UserValue.isEmpty`), nor is SUBSET S.
            Lazy::Infinite(_) | Lazy::Subset(_) => Ok(false),
            Lazy::FunctionSet(..) | Lazy::RecordSet(..) | Lazy::Product(..) => {
                self.is_empty(machine).map_err(|_| UNSURE_PRINT)
            }
            _ => Err(UNSURE_PRINT),
        }
    }
}

// Kleene's conjunction, of values `None` leaves unknown: false where one is, true where all are.
fn all(values: impl IntoIterator<Item = Option<bool>>) -> Option<bool> {
    let mut result = Some(true);
    for value in values {
        match value {
            Some(false) => return Some(false),
            None => result = None,
            Some(true) => {}
        }
    }
    result
}

// Kleene's disjunction: true where one is, false where all are.
fn any(values: impl IntoIterator<Item = Option<bool>>) -> Option<bool> {
    let mut result = Some(false);
    for value in values {
        match value {
            Some(true) => return Some(true),
            None => result = None,
            Some(false) => {}
        }
    }
    result
}

// Whether elements streamed differ from their normalized set's, in order.
fn is_unnormalized(machine: &mut Machine<'_>, elements: &[Id]) -> Outcome<bool> {
    let set = machine.store.set_of(elements)?;
    Ok(machine.store.set_elements(set) != elements)
}

// The next combination of `indices.len()` positions below `length`, in lexicographic order.
fn advance_combination(indices: &mut [usize], length: usize) -> bool {
    let count = indices.len();
    for position in (0..count).rev() {
        if indices[position] < length - count + position {
            indices[position] += 1;
            for next in position + 1..count {
                indices[next] = indices[next - 1] + 1;
            }
            return true;
        }
    }
    false
}

// The value `build` makes of every combination of one element from each list, the last list
// turning fastest.
fn cartesian(lists: &[Vec<Id>], mut build: impl FnMut(&[Id]) -> Outcome<Id>) -> Outcome<Vec<Id>> {
    let total: f64 = lists.iter().map(|list| list.len() as f64).product();
    if total > MAXIMUM_ELEMENTS {
        return Err(Bail("a lazy set too large to enumerate"));
    }
    let mut combinations = Vec::with_capacity(total as usize);
    let mut positions = vec![0usize; lists.len()];
    let mut values = Vec::with_capacity(lists.len());
    for _ in 0..total as usize {
        values.clear();
        values.extend(
            lists
                .iter()
                .zip(&positions)
                .map(|(list, &position)| list[position]),
        );
        combinations.push(build(&values)?);
        for index in (0..lists.len()).rev() {
            positions[index] += 1;
            if positions[index] < lists[index].len() {
                break;
            }
            positions[index] = 0;
        }
    }
    Ok(combinations)
}

// `getSortedUnion`: a merge of the two lists by TLC's order, an element of both kept once, from
// the left. The lists of lazy sets need not be in TLC's order, which the merge doesn't check.
fn sorted_union(machine: &mut Machine<'_>, left: Vec<Id>, right: Vec<Id>) -> Outcome<Vec<Id>> {
    if left.is_empty() {
        return Ok(right);
    }
    if right.is_empty() {
        return Ok(left);
    }
    let mut merged = Vec::with_capacity(left.len() + right.len());
    let (mut left_index, mut right_index) = (0, 0);
    while left_index < left.len() && right_index < right.len() {
        let order = machine
            .store
            .compare(left[left_index], right[right_index])?;
        if order < 0 {
            merged.push(left[left_index]);
            left_index += 1;
        } else if order > 0 {
            merged.push(right[right_index]);
            right_index += 1;
        } else {
            merged.push(left[left_index]);
            left_index += 1;
            right_index += 1;
        }
    }
    merged.extend_from_slice(&left[left_index..]);
    merged.extend_from_slice(&right[right_index..]);
    Ok(merged)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::machine::Program;
    use tla_values::Store;

    // UNION {{1, 2}, {2, 3}}, kept lazy: it streams each set in turn, 2 twice, and enumerates the
    // normalized union.
    #[test]
    fn streams_each_set_of_a_union_in_turn() {
        let program = Program::default();
        let mut store = Store::new();
        store.reset(std::iter::empty::<&[u16]>());
        let mut machine = Machine::new(&program, store);
        let integers: Vec<Id> = (0..=3)
            .map(|value| machine.store.int(value).expect("an integer"))
            .collect();
        let left = machine.store.set_of(&integers[1..3]).expect("a set");
        let right = machine.store.set_of(&integers[2..4]).expect("a set");
        let sets = machine.store.set_of(&[right, left]).expect("a set");
        let union = Lazy::Union(Box::new(Lazy::Set(sets)));
        let [zero, one, two, three] = integers[..] else {
            panic!("four integers");
        };
        assert_eq!(
            union.stream(&mut machine).ok(),
            Some(vec![one, two, two, three])
        );
        assert_eq!(
            union.enumerate(&mut machine).ok(),
            Some(vec![one, two, three])
        );
        assert_eq!(union.contains(&mut machine, three).ok(), Some(true));
        assert_eq!(union.contains(&mut machine, zero).ok(), Some(false));
        assert_eq!(union.is_empty(&mut machine).ok(), Some(false));
        let of_integers = Lazy::Union(Box::new(Lazy::Set(left)));
        assert!(of_integers.stream(&mut machine).is_err());
        let infinite = Lazy::Union(Box::new(Lazy::Infinite("Nat")));
        assert!(infinite.enumerate(&mut machine).is_err());
    }

    // A set kept for later uses streams only where it streams its normalized set's elements in
    // order, and a set that streams none twice isn't kept.
    #[test]
    fn streams_a_kept_set_only_as_its_normalized_set() {
        let program = Program::default();
        let mut store = Store::new();
        store.reset(std::iter::empty::<&[u16]>());
        let mut machine = Machine::new(&program, store);
        let integers: Vec<Id> = (1..=4)
            .map(|value| machine.store.int(value).expect("an integer"))
            .collect();
        let [one, two, three, four] = integers[..] else {
            panic!("four integers");
        };
        let mut union = |left: &[Id], right: &[Id]| {
            let left = machine.store.set_of(left).expect("a set");
            let right = machine.store.set_of(right).expect("a set");
            let sets = machine.store.set_of(&[left, right]).expect("a set");
            Lazy::Union(Box::new(Lazy::Set(sets))).kept()
        };
        let overlapping = union(&[one, two], &[two, three]);
        let apart = union(&[one, two], &[three, four]);
        let unsorted = union(&[three], &[one, two]);
        assert!(matches!(overlapping, Lazy::Kept(_)));
        assert!(overlapping.stream(&mut machine).is_err());
        assert!(unsorted.stream(&mut machine).is_err());
        assert_eq!(
            overlapping.enumerate(&mut machine).ok(),
            Some(vec![one, two, three])
        );
        assert_eq!(
            apart.stream(&mut machine).ok(),
            Some(vec![one, two, three, four])
        );
        assert!(matches!(
            Lazy::Subset(Box::new(Lazy::Set(EMPTY_SET))).kept(),
            Lazy::Subset(_)
        ));
    }

    // `SetOfFcnsValue.size` and its like: an empty part decides before a part TLC can't enumerate
    // is asked, and a range of one element makes one function.
    #[test]
    fn sizes_a_set_by_its_parts_as_tlc_does() {
        let program = Program::default();
        let mut store = Store::new();
        store.reset(std::iter::empty::<&[u16]>());
        let mut machine = Machine::new(&program, store);
        let integers: Vec<Id> = (1..=3)
            .map(|value| machine.store.int(value).expect("an integer"))
            .collect();
        let nat = || Box::new(Lazy::Infinite("Nat"));
        let empty = || Box::new(Lazy::Set(EMPTY_SET));
        let one = machine.store.set_of(&integers[..1]).expect("a set");
        let three = machine.store.set_of(&integers).expect("a set");
        let mut size = |set: Lazy| set.size(&mut machine).ok();
        assert_eq!(size(Lazy::FunctionSet(nat(), empty())), Some(0));
        assert_eq!(size(Lazy::FunctionSet(empty(), nat())), Some(1));
        assert_eq!(
            size(Lazy::FunctionSet(nat(), Box::new(Lazy::Set(one)))),
            Some(1)
        );
        assert_eq!(
            size(Lazy::FunctionSet(
                Box::new(Lazy::Set(three)),
                Box::new(Lazy::Set(three))
            )),
            Some(27)
        );
        assert_eq!(
            size(Lazy::FunctionSet(nat(), Box::new(Lazy::Set(three)))),
            None
        );
        assert_eq!(size(Lazy::Product(vec![*nat(), *empty()])), Some(0));
        assert_eq!(
            size(Lazy::Product(vec![Lazy::Set(three), Lazy::Set(three)])),
            Some(9)
        );
        assert_eq!(size(Lazy::Subset(Box::new(Lazy::Set(three)))), Some(8));
    }

    // `SetOfTuplesValue.toString` and its siblings, which PrintT calls unchecked: the parts are
    // sized in order up to an empty one, so a part TLC can't size fails only before it, and the
    // set it then enumerates tests each part for emptiness, which fails on a non-set.
    #[test]
    fn prints_a_set_by_its_parts_as_tlc_does() {
        let program = Program::default();
        let mut store = Store::new();
        store.reset(std::iter::empty::<&[u16]>());
        let mut machine = Machine::new(&program, store);
        let integers: Vec<Id> = (1..=3)
            .map(|value| machine.store.int(value).expect("an integer"))
            .collect();
        let int = || Lazy::Infinite("Int");
        let empty = || Lazy::Set(EMPTY_SET);
        let three = Lazy::Set(machine.store.set_of(&integers).expect("a set"));
        let number = Lazy::Set(integers[0]);
        let tuple = Lazy::Set(machine.store.tuple_of(&integers[..1]));
        let mut printed = |set: Lazy| match set.check_printed(&mut machine) {
            Ok(_) => "prints",
            Err(Bail(reason)) if reason == UNSIZED_PRINT => "fails",
            Err(_) => "unsure",
        };
        assert_eq!(printed(Lazy::Product(vec![int(), empty()])), "fails");
        assert_eq!(printed(Lazy::Product(vec![empty(), int()])), "prints");
        assert_eq!(
            Lazy::Product(vec![empty(), number.clone()])
                .check_printed(&mut machine)
                .ok(),
            Some(PrintedSet::Empty)
        );
        assert_eq!(
            Lazy::FunctionSet(Box::new(empty()), Box::new(tuple.clone()))
                .check_printed(&mut machine)
                .ok(),
            Some(PrintedSet::OfEmptyFunction)
        );
        assert_eq!(
            Lazy::Product(vec![three.clone(), three.clone()])
                .check_printed(&mut machine)
                .ok(),
            Some(PrintedSet::Enumerated)
        );
        let mut printed = |set: Lazy| match set.check_printed(&mut machine) {
            Ok(_) => "prints",
            Err(Bail(reason)) if reason == UNSIZED_PRINT => "fails",
            Err(_) => "unsure",
        };
        assert_eq!(printed(Lazy::Product(vec![three.clone(), int()])), "fails");
        assert_eq!(
            printed(Lazy::Product(vec![number.clone(), empty()])),
            "fails"
        );
        assert_eq!(
            printed(Lazy::Product(vec![three.clone(), tuple.clone()])),
            "fails"
        );
        assert_eq!(
            printed(Lazy::Product(vec![three.clone(), three.clone()])),
            "prints"
        );
        assert_eq!(
            printed(Lazy::RecordSet(Vec::new(), vec![int(), empty()])),
            "fails"
        );
        assert_eq!(
            printed(Lazy::FunctionSet(Box::new(int()), Box::new(empty()))),
            "fails"
        );
        assert_eq!(
            printed(Lazy::FunctionSet(Box::new(empty()), Box::new(int()))),
            "prints"
        );
        assert_eq!(
            printed(Lazy::FunctionSet(Box::new(tuple), Box::new(three.clone()))),
            "fails"
        );
        assert_eq!(
            printed(Lazy::FunctionSet(Box::new(three.clone()), Box::new(number))),
            "fails"
        );
        assert_eq!(
            printed(Lazy::Product(vec![
                Lazy::Product(vec![int(), empty()]),
                int()
            ])),
            "prints"
        );
    }
}
