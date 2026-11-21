//! Sets: what TLC keeps lazily, enumerated and tested for membership, and the set operators.

use std::cmp::Ordering;
use std::rc::Rc;

use crate::eval::Predicate;
use crate::print::{format_pretty, format_value, print_order};
use crate::value::{
    Class, Evaluated, Lazy, SetClass, Value, compare, elements, equals, fail, fail_coded,
    fail_runtime, failing_comparisons, find_key, is_enumerable, mark_unnormalized, print_failure,
    set_of, unnormalized, unsorted_failure,
};

/// The reason for a union of a value that isn't a set, which TLC fails to enumerate.
pub(crate) const UNION_NON_SET: &str = "enumerated the union of a value that isn't a set";
/// The reason for a union whose first set TLC doesn't enumerate, which TLC fails to enumerate.
pub(crate) const UNION_FIRST_NON_SET: &str = "enumerated a union with a set TLC doesn't enumerate";

/// Whether `UnionValue.elements` fails at once on a value: a union of a value that isn't
/// `Enumerable`, or whose first element isn't.
pub(crate) fn is_failing_union(value: &Value) -> bool {
    let Value::Lazy(lazy) = value else {
        return false;
    };
    let Lazy::Union(sets) = &***lazy else {
        return false;
    };
    !is_enumerable(sets)
        || elements(sets).is_ok_and(|sets| sets.first().is_some_and(|set| !is_enumerable(set)))
}

/// How many elements the evaluator enumerates of a lazy set before it gives up, as the engine
/// refuses a power set past 2^20.
const MAXIMUM_ENUMERATION: usize = 1 << 20;

fn checked_size(size: usize, factor: usize) -> Evaluated<usize> {
    match size.checked_mul(factor) {
        Some(size) if size <= MAXIMUM_ENUMERATION => Ok(size),
        _ => fail("a set too large to enumerate"),
    }
}

thread_local! {
    static ORDERED_WALKS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static COMBINATION_SORT_FAILURES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// How many times the evaluator walked a power set's elements other than to print them: TLC
/// walks a `SubsetValue` in an order of its own (`SubsetValue.elements`), where the evaluator
/// walks it sorted, so what the walk meets first may differ.
pub(crate) fn ordered_walks() -> usize {
    ORDERED_WALKS.with(|walks| walks.get())
}

fn count_ordered_walk() {
    ORDERED_WALKS.with(|walks| walks.set(walks.get() + 1));
}

/// Runs `print`, a value's text, which TLC writes of the normalized set whatever order it walks
/// it in (`SubsetValue.toString` prints `toSetEnum`, which `SetEnumValue.toString` normalizes),
/// so it isn't an ordered walk.
pub(crate) fn unordered<T>(print: impl FnOnce() -> T) -> T {
    let walks = ordered_walks();
    let text = print();
    ORDERED_WALKS.with(|count| count.set(walks));
    text
}

/// How many times the evaluator failed to sort what a lazy intersection, union or difference
/// enumerates (`sorted_combination`).
pub(crate) fn combination_sort_failures() -> usize {
    COMBINATION_SORT_FAILURES.with(std::cell::Cell::get)
}

/// The elements of a lazy set in TLC's order.
pub fn enumerate(lazy: &Lazy) -> Evaluated<Vec<Value>> {
    let elements = enumerate_lazy(lazy)?;
    if matches!(lazy, Lazy::Subset(_)) {
        count_ordered_walk();
    }
    Ok(elements)
}

fn enumerate_lazy(lazy: &Lazy) -> Evaluated<Vec<Value>> {
    // The Enumerators of `SetOfFcnsValue`, `SetOfRcdsValue` and `SetOfTuplesValue` take each
    // range's or component's first element, and a null one, an INSTANCE's THEOREM or ASSUME
    // literal TLC did not initialize, ends the enumeration: TLC enumerates nothing where the
    // evaluator would build the elements. `[{} -> T]` is `{<<>>}` whatever T is: its Enumerator
    // reads no range where the domain is empty.
    let null_parts = match lazy {
        Lazy::FunctionSet(domain, range) => {
            crate::value::contains_uninitialized(range) && !crate::eval::is_empty(domain)?
        }
        Lazy::RecordSet(fields, _) => fields
            .iter()
            .any(|(_, set)| crate::value::contains_uninitialized(set)),
        Lazy::Product(factors) => factors.iter().any(crate::value::contains_uninitialized),
        _ => false,
    };
    if null_parts {
        return fail(
            "enumerated a set of functions, records or tuples over a set holding an INSTANCE fact literal TLC did not initialize",
        );
    }
    match lazy {
        Lazy::Nat | Lazy::Int | Lazy::Real | Lazy::Strings | Lazy::Seq(_) | Lazy::Any => {
            fail("enumerated an infinite set")
        }
        // `SubsetValue.elementsNormalized` sizes the base first, which a base TLC can't count
        // fails, before it enumerates it.
        Lazy::Subset(base) => {
            cardinality(base)?;
            let base = elements(base)?;
            if base.len() > 20 {
                return fail("a power set too large to build");
            }
            let mut subsets = Vec::with_capacity(1 << base.len());
            for mask in 0u32..(1 << base.len()) {
                let subset = (0..base.len())
                    .filter(|&bit| mask & (1 << bit) != 0)
                    .map(|bit| base[bit].clone())
                    .collect();
                subsets.push(Value::set(subset));
            }
            sorted(subsets)
        }
        Lazy::FunctionSet(domain_set, range) => {
            // `SetOfFcnsValue.elements` asks whether the set is empty first (`Value.isEmpty`):
            // its domain isn't, and its range is, which fails on a range that isn't a set.
            if !crate::eval::is_empty(domain_set)? && crate::eval::is_empty(range)? {
                return Ok(Vec::new());
            }
            // A domain its own parts empty holds nothing to enumerate, whatever they are, so the
            // set holds the empty function alone.
            // `DomIVEnumerator` gives a function over the empty interval as its domain.
            if crate::eval::is_empty(domain_set)? {
                return Ok(vec![match domain_set {
                    Value::Interval(low, _, _) => {
                        Value::over_interval(*low, Vec::new(), Class::Plain)
                    }
                    _ => Value::function(Vec::new(), Vec::new(), Class::Plain),
                }]);
            }
            if is_infinite(domain_set) {
                return fail_runtime(
                    "enumerated an infinite set",
                    format!(
                        "Attempted to enumerate a set of the form [D -> R],but the domain D:\n{}\ncannot be enumerated.",
                        format_value(domain_set)
                    ),
                );
            }
            let domain = elements(domain_set)?;
            if !domain.is_empty() && is_infinite(range) {
                return fail_runtime(
                    "enumerated an infinite set",
                    format!(
                        "Attempted to enumerate a set of the form [D -> R],but the range R:\n{}\ncannot be enumerated.",
                        format_value(range)
                    ),
                );
            }
            // Over an empty domain the set holds the empty function alone, whatever the range.
            // TLC enumerates the range once for each element of the domain
            // (`SetOfFcnsValue.Enumerator`), so a lazy range gives each its own values, which a
            // dumped trace writes apart.
            let ranges = domain
                .iter()
                .map(|_| elements(range))
                .collect::<Evaluated<Vec<_>>>()?;
            let tuples = product(&ranges)?;
            // A function over an interval keeps it as its domain. Any other is a `FcnRcdValue`
            // over the domain TLC normalized, which it holds as normalized (`Enumerator`,
            // `FcnProduct`: `new FcnRcdValue(dom, elems, true)`), so it searches its keys in
            // that order.
            let build = |values: Vec<Value>| match domain_set {
                Value::Interval(low, _, _) => Value::over_interval(*low, values, Class::Plain),
                _ => {
                    let function = Value::function(domain.to_vec(), values, Class::Plain);
                    if let Value::Function(built) = &function {
                        built.search.set(crate::value::Search::Sorted);
                    }
                    function
                }
            };
            sorted(tuples.into_iter().map(build).collect())
        }
        Lazy::RecordSet(fields, _) => {
            let sets = component_elements(fields.iter().map(|(_, set)| set), |index, set| {
                format!(
                    "Attempted to enumerate a set of the form [l1 : v1, ..., ln : vn],\nbut can't enumerate the value of the `{}' field:\n{}",
                    String::from_utf16_lossy(&fields[index].0.units),
                    format_value(set)
                )
            })?;
            let domain: Vec<Value> = fields
                .iter()
                .map(|(name, _)| Value::Str(Rc::clone(name)))
                .collect();
            sorted(
                product(&sets)?
                    .into_iter()
                    .map(|values| Value::function(domain.clone(), values, Class::Record))
                    .collect(),
            )
        }
        Lazy::Product(factors) => {
            let sets = component_elements(factors.iter(), |index, factor| {
                format!(
                    "Attempted to enumerate a set of the form s1 \\X s2 ... \\X sn,\nbut can't enumerate s{index}:\n{}",
                    format_value(factor)
                )
            })?;
            sorted(product(&sets)?.into_iter().map(Value::tuple).collect())
        }
        // An intersection, a union or a difference TLC normalizes as it collects what its
        // Enumerator streams (`toSetEnum`), as it does a filter's.
        Lazy::Cap(..) | Lazy::Cup(..) | Lazy::Diff(..) | Lazy::Union(_) => {
            // `toSetEnum` collects them (`ValueVec.addElement`), up to its bound.
            let mut all = Vec::new();
            stream_lazy(lazy, &mut |element| {
                crate::value::push_set_element(&mut all, element.clone())?;
                Ok(true)
            })?;
            sorted_combination(all)
        }
        // `SetPredValue.Enumerator`: the set, which TLC must enumerate, filtered by the predicate,
        // which only the evaluator tests: a lazy filter is of a set it fails to enumerate.
        Lazy::Filter(base, predicate) => {
            if let Some(converted) = predicate.converted() {
                return Ok(converted.to_vec());
            }
            if let Some(filtered) = predicate.filtered() {
                return sorted_combination(filtered.to_vec());
            }
            if !is_enumerable(base) {
                return fail_runtime(
                    "enumerated a filter of a set TLC doesn't enumerate",
                    format!(
                        "Attempted to enumerate {{ x \\in S : p(x) }} when S:\n{}\nis not enumerable",
                        format_pretty(base)
                    ),
                );
            }
            // `SetPredValue.Enumerator` tests each element as it streams the set, before a
            // consumer normalizes what it collects.
            stream(base)?;
            fail("enumerated a lazy filter")
        }
    }
}

/// The elements of a set in the order TLC's `elements()` streams them, unnormalized: a set
/// enumeration's normalized (`SetEnumValue.Enumerator`), an interval's in order, an intersection's,
/// a union's, a difference's and a UNION's as their Enumerators take them from the sets they are
/// made of, and a filter's as it tests its set's. TLC normalizes what a consumer collects of them
/// (`toSetEnum`) in that order, which decides which two elements it compares first, and tests or
/// binds them in that order where it streams them.
pub(crate) fn stream(set: &Value) -> Evaluated<Rc<Vec<Value>>> {
    if !is_streamed(set) {
        return elements(set);
    }
    let mut all = Vec::new();
    stream_until(set, &mut |element| {
        all.push(element.clone());
        Ok(true)
    })?;
    Ok(Rc::new(all))
}

// Whether TLC streams a set otherwise than the set enumeration it normalizes it into: a lazy
// intersection, union, difference or UNION, or a filter the evaluator filtered ahead.
fn is_streamed(set: &Value) -> bool {
    let Value::Lazy(lazy) = set else {
        return false;
    };
    !is_empty_by_argument(set)
        && match &***lazy {
            Lazy::Cap(..) | Lazy::Cup(..) | Lazy::Diff(..) | Lazy::Union(_) => true,
            Lazy::Filter(_, predicate) => {
                predicate.converted().is_none() && predicate.filtered().is_some()
            }
            _ => false,
        }
}

/// Streams a set's elements in TLC's order (`stream`) to `visit`, up to one it answers false for,
/// as a consumer that stops early takes them from the Enumerators, each of which tests or takes
/// an element only as it is asked for the next (`isSubsetEq`). False where `visit` stopped it.
pub(crate) fn stream_until(
    set: &Value,
    visit: &mut dyn FnMut(&Value) -> Evaluated<bool>,
) -> Evaluated<bool> {
    // `IntervalValue.Enumerator` walks the interval without counting it, as far as the
    // evaluator walks one.
    if let Value::Interval(low, high, _) = set {
        crate::value::check_walk(*low, *high)?;
        for (index, key) in (*low..=*high).enumerate() {
            if index >= crate::value::MAXIMUM_WALK {
                return fail("an interval too large to build");
            }
            if !visit(&Value::Int(key))? {
                return Ok(false);
            }
        }
        return Ok(true);
    }
    if !is_streamed(set) {
        return visit_all(&elements(set)?, visit);
    }
    // A failure within the set's methods heads TLC's report with the set, as its `elements`
    // does (`comparing`).
    crate::value::comparing(set, || stream_streamed(set, visit))
}

fn stream_streamed(
    set: &Value,
    visit: &mut dyn FnMut(&Value) -> Evaluated<bool>,
) -> Evaluated<bool> {
    let Value::Lazy(lazy) = set else {
        unreachable!("a streamed set is lazy");
    };
    stream_lazy(lazy, visit)
}

// `stream_until` of a lazy set TLC isn't sure to find empty by its parts.
fn stream_lazy(lazy: &Lazy, visit: &mut dyn FnMut(&Value) -> Evaluated<bool>) -> Evaluated<bool> {
    start_lazy(lazy)?;
    match lazy {
        // `SetCapValue.Enumerator`: the first operand TLC can enumerate, filtered by the other.
        Lazy::Cap(left, right) => {
            let (enumerated, tested) = if is_enumerable(left) {
                (left, right)
            } else {
                (right, left)
            };
            stream_until(enumerated, &mut |element| {
                if is_member(element, tested)? {
                    visit(element)
                } else {
                    Ok(true)
                }
            })
        }
        // `UnionValue.Enumerator`: each element of the set in turn.
        Lazy::Union(sets) => {
            let sets = elements(sets)?;
            for (index, inner) in sets.iter().enumerate() {
                if index > 0 && !is_enumerable(inner) {
                    return fail("enumerated a union with a later set TLC doesn't enumerate");
                }
                if !stream_until(inner, visit)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        // `SetCupValue.Enumerator`: the first operand's elements, then the second's.
        Lazy::Cup(left, right) => {
            if !stream_until(left, visit)? {
                return Ok(false);
            }
            stream_until(right, visit)
        }
        // `SetDiffValue.Enumerator`: the first operand, filtered by the second.
        Lazy::Diff(left, right) => stream_until(left, &mut |element| {
            if is_member(element, right)? {
                Ok(true)
            } else {
                visit(element)
            }
        }),
        // A filter the evaluator filtered ahead, in the order of its set's stream.
        Lazy::Filter(_, predicate) => match predicate.filtered() {
            Some(filtered) => visit_all(filtered, visit),
            None => unreachable!("a streamed filter is filtered ahead"),
        },
        _ => unreachable!("a streamed set is a combination of sets or a filter"),
    }
}

// The text of a value an Enumerator's failure names (`Values.ppr(set.toString())`), which fails
// where TLC's `toString` of it does, as a set enumeration it can't sort.
fn shown(value: &Value) -> Evaluated<String> {
    crate::eval::check_to_string(value, true)?;
    Ok(format_pretty(value))
}

// What TLC's `elements()` of a set does as it makes the Enumerator, before it gives any element:
// `SetEnumValue.Enumerator` normalizes the set, `SetCupValue.Enumerator` checks that both operands
// are enumerable and starts the first and then the second, `SetCapValue`'s, `SetDiffValue`'s and
// `SetPredValue`'s check and start the set they enumerate, `UnionValue`'s starts the set of sets
// and checks and starts the first of them, and a set of functions, records or tuples asks
// whether it is empty.
fn start(set: &Value) -> Evaluated<()> {
    match set {
        Value::Set(_) | Value::Unsorted(_) => elements(set).map(|_| ()),
        Value::Lazy(lazy) if !is_empty_by_argument(set) => start_lazy(lazy),
        _ => Ok(()),
    }
}

fn start_lazy(lazy: &Lazy) -> Evaluated<()> {
    match lazy {
        Lazy::Cup(left, right) => {
            if !is_enumerable(left) || !is_enumerable(right) {
                return fail_runtime(
                    "enumerated S \\cup T, not both of which TLC enumerates",
                    format!(
                        "Attempted to enumerate S \\cup T when S:\n{}\nand T:\n{}\nare not both enumerable",
                        shown(left)?,
                        shown(right)?
                    ),
                );
            }
            start_part(left)?;
            start_part(right)
        }
        Lazy::Cap(left, right) => {
            if is_enumerable(left) {
                start_part(left)
            } else if is_enumerable(right) {
                start_part(right)
            } else {
                fail_runtime(
                    "enumerated S \\cap T, neither of which TLC enumerates",
                    format!(
                        "Attempted to enumerate S \\cap T when neither S:\n{}\nnor T:\n{}\nis enumerable",
                        shown(left)?,
                        shown(right)?
                    ),
                )
            }
        }
        Lazy::Diff(left, _) => {
            if !is_enumerable(left) {
                return fail_runtime(
                    "enumerated S \\ T, whose S TLC doesn't enumerate",
                    format!(
                        "Attempted to enumerate S \\ T when S:\n{}\nis not enumerable.",
                        shown(left)?
                    ),
                );
            }
            start_part(left)
        }
        Lazy::Filter(base, _) => {
            if !is_enumerable(base) {
                return fail_runtime(
                    "enumerated a filter of a set TLC doesn't enumerate",
                    format!(
                        "Attempted to enumerate {{ x \\in S : p(x) }} when S:\n{}\nis not enumerable",
                        shown(base)?
                    ),
                );
            }
            start_part(base)
        }
        // The Enumerator's constructor fails on a value that isn't `Enumerable`, which a value TLC
        // overrides isn't either, and words it with its own default `toString`, Object's: the
        // class and an identity hash, whatever hash a run prints.
        Lazy::Union(sets) => {
            if !is_enumerable(sets) {
                if matches!(sets, Value::Null) {
                    return fail("enumerated the union of a set TLC doesn't enumerate");
                }
                return fail_runtime(
                    UNION_NON_SET,
                    "Attempted to enumerate the nonenumerable set:\n\
                     tlc2.value.impl.UnionValue$Enumerator@1b6d3586"
                        .into(),
                );
            }
            match elements(sets)?.first() {
                Some(first) if !is_enumerable(first) => fail_runtime(
                    UNION_FIRST_NON_SET,
                    "Attempted to enumerate UNION(s), but some element of s is nonenumerable."
                        .into(),
                ),
                Some(first) => start_part(first),
                None => Ok(()),
            }
        }
        // `SetOfFcnsValue.elements`, `SetOfRcdsValue.elements` and `SetOfTuplesValue.elements`
        // first ask whether the set is empty (`Value.isEmpty`), which fails on a part that isn't
        // a set, and their Enumerators then check and start each part they enumerate.
        Lazy::FunctionSet(domain, range) => {
            if (!crate::eval::is_empty(domain)? && crate::eval::is_empty(range)?)
                || matches!(domain, Value::Interval(..))
            {
                return Ok(());
            }
            if is_infinite(domain) {
                return fail_runtime(
                    "enumerated an infinite set",
                    format!(
                        "Attempted to enumerate a set of the form [D -> R],but the domain D:\n{}\ncannot be enumerated.",
                        format_value(domain)
                    ),
                );
            }
            if elements(domain)?.is_empty() {
                return Ok(());
            }
            if is_infinite(range) {
                return fail_runtime(
                    "enumerated an infinite set",
                    format!(
                        "Attempted to enumerate a set of the form [D -> R],but the range R:\n{}\ncannot be enumerated.",
                        format_value(range)
                    ),
                );
            }
            start_part(range)
        }
        Lazy::RecordSet(fields, _) => {
            if is_any_part_empty(fields.iter().map(|(_, field)| field))? {
                return Ok(());
            }
            for (name, field) in fields {
                if is_infinite(field) {
                    return fail_runtime(
                        "enumerated an infinite set",
                        format!(
                            "Attempted to enumerate a set of the form [l1 : v1, ..., ln : vn],\nbut can't enumerate the value of the `{}' field:\n{}",
                            String::from_utf16_lossy(&name.units),
                            format_value(field)
                        ),
                    );
                }
                start_part(field)?;
            }
            Ok(())
        }
        Lazy::Product(factors) => {
            if is_any_part_empty(factors.iter())? {
                return Ok(());
            }
            for (index, factor) in factors.iter().enumerate() {
                if is_infinite(factor) {
                    return fail_runtime(
                        "enumerated an infinite set",
                        format!(
                            "Attempted to enumerate a set of the form s1 \\X s2 ... \\X sn,\nbut can't enumerate s{index}:\n{}",
                            format_value(factor)
                        ),
                    );
                }
                start_part(factor)?;
            }
            Ok(())
        }
        _ => Ok(()),
    }
}

// `Value.isEmpty` of a set of records or tuples: whether a part is empty, asking each in turn up
// to an empty one, which fails on a part that isn't a set.
fn is_any_part_empty<'v>(mut parts: impl Iterator<Item = &'v Value>) -> Evaluated<bool> {
    parts.try_fold(false, |is_empty, part| {
        Ok(is_empty || crate::eval::is_empty(part)?)
    })
}

// `start` of a set another's Enumerator starts, which heads TLC's report of a failure within it
// with the set, as its `elements` does (`comparing`).
fn start_part(set: &Value) -> Evaluated<()> {
    if matches!(set, Value::Lazy(_)) {
        crate::value::comparing(set, || start(set))
    } else {
        start(set)
    }
}

/// TLC's `normalize` of a set, which a CHOOSE asks of its set before it enumerates it
/// (`OPCODE_bc`): a set enumeration sorts itself, and a lazy intersection, difference, filter,
/// power set, or set of functions, records or tuples normalizes the sets it is made of, where
/// it hasn't converted itself yet; a union of its own or of a set of sets normalizes nothing.
pub(crate) fn normalize_parts(set: &Value) -> Evaluated<()> {
    match set {
        Value::Set(_) | Value::Unsorted(_) => elements(set).map(|_| ()),
        Value::Lazy(lazy) => match &***lazy {
            Lazy::Cap(left, right) | Lazy::Diff(left, right) | Lazy::FunctionSet(left, right) => {
                normalize_parts(left)?;
                normalize_parts(right)
            }
            Lazy::Filter(base, _) | Lazy::Subset(base) => normalize_parts(base),
            Lazy::RecordSet(fields, _) => {
                fields.iter().try_for_each(|(_, set)| normalize_parts(set))
            }
            Lazy::Product(factors) => factors.iter().try_for_each(normalize_parts),
            _ => Ok(()),
        },
        _ => Ok(()),
    }
}

fn visit_all(
    elements: &[Value],
    visit: &mut dyn FnMut(&Value) -> Evaluated<bool>,
) -> Evaluated<bool> {
    for element in elements {
        if !visit(element)? {
            return Ok(false);
        }
    }
    Ok(true)
}

/// How many elements TLC's enumeration of a set yields (`elements()`), duplicates and all:
/// exactly so many, or at most so many where it tests each first, as an intersection or a
/// difference does; `None` for one it can't enumerate.
#[derive(Clone, Copy)]
enum Streamed {
    Exact(u128),
    AtMost(u128),
}

fn streamed(set: &Value) -> Option<Streamed> {
    use Streamed::{AtMost, Exact};
    let combined = |parts: &mut dyn Iterator<Item = Option<Streamed>>| {
        let (mut size, mut is_exact) = (1u128, true);
        for part in parts {
            match part? {
                // An empty part empties the set before TLC enumerates any (`isEmpty`).
                Exact(0) => return Some(Exact(0)),
                Exact(part) => size = size.saturating_mul(part),
                AtMost(part) => {
                    size = size.saturating_mul(part);
                    is_exact = false;
                }
            }
        }
        Some(if is_exact { Exact(size) } else { AtMost(size) })
    };
    let bound = |streamed: Streamed| match streamed {
        Exact(size) | AtMost(size) => size,
    };
    match set {
        Value::Set(elements) => Some(Exact(elements.len() as u128)),
        Value::Interval(low, high, _) => Some(Exact(
            (i64::from(*high) - i64::from(*low) + 1).max(0) as u128,
        )),
        Value::Lazy(lazy) => match &***lazy {
            Lazy::Product(factors) => combined(&mut factors.iter().map(streamed)),
            Lazy::RecordSet(fields, _) => {
                combined(&mut fields.iter().map(|(_, set)| streamed(set)))
            }
            // `SetOfFcnsValue`'s enumerators take the domain's normalized set and enumerate the
            // range once for each of its elements.
            Lazy::FunctionSet(domain, range) => {
                let domain = match domain {
                    Value::Set(elements) => elements.len(),
                    Value::Interval(low, high, _) => {
                        (i64::from(*high) - i64::from(*low) + 1).max(0) as usize
                    }
                    _ => return None,
                };
                if domain == 0 {
                    return Some(Exact(1));
                }
                combined(&mut (0..domain.min(128)).map(|_| streamed(range)))
            }
            // `SetCupValue.Enumerator` and `UnionValue.Enumerator`: each set in turn, an element
            // of two as often as it is in them.
            Lazy::Cup(left, right) => {
                let (left, right) = (streamed(left)?, streamed(right)?);
                let size = bound(left).saturating_add(bound(right));
                Some(match (left, right) {
                    (Exact(_), Exact(_)) => Exact(size),
                    _ => AtMost(size),
                })
            }
            Lazy::Union(sets) => {
                let Value::Set(sets) = sets else {
                    return None;
                };
                let (mut size, mut is_exact) = (0u128, true);
                for set in sets.iter() {
                    let set = streamed(set)?;
                    is_exact &= matches!(set, Exact(_));
                    size = size.saturating_add(bound(set));
                }
                Some(if is_exact { Exact(size) } else { AtMost(size) })
            }
            // `SetCapValue.Enumerator` and `SetDiffValue.Enumerator`: the set they enumerate,
            // each element tested in the other.
            Lazy::Cap(left, right) => {
                let enumerated = if is_enumerable(left) { left } else { right };
                Some(AtMost(bound(streamed(enumerated)?)))
            }
            Lazy::Diff(left, _) => Some(AtMost(bound(streamed(left)?))),
            // `SubsetValue.Enumerator` of a base it normalizes first.
            Lazy::Subset(base) => match base {
                Value::Set(_) | Value::Interval(..) => match streamed(base)? {
                    Exact(size) if size < 127 => Some(Exact(1 << size)),
                    _ => None,
                },
                _ => None,
            },
            Lazy::Nat
            | Lazy::Int
            | Lazy::Real
            | Lazy::Strings
            | Lazy::Seq(_)
            | Lazy::Any
            | Lazy::Filter(..) => None,
        },
        _ => None,
    }
}

/// Fails where TLC fails to enumerate a bound of a quantifier, a CHOOSE or a set map in normalized
/// order (`Tool.contexts`, OPCODE_bc): `EnumerableValue.elements(Ordering.NORMALIZED)` builds a
/// set it keeps lazy, other than a power set, which enumerates itself in that order, into a set
/// enumeration (`toSetEnum`), whose ValueVec fails once it holds `TLCGlobals.setBound` elements
/// and is given another, duplicates and all (`ValueVec.ensureCapacity`). An interval builds its
/// array at once, and a set enumeration is built already. Where TLC tests each element first,
/// how many it adds is TLC's alone past the bound.
pub(crate) fn check_enumerated_bound(set: &Value) -> Evaluated<()> {
    let Value::Lazy(lazy) = set else {
        return Ok(());
    };
    if !matches!(
        &***lazy,
        Lazy::Product(_)
            | Lazy::RecordSet(..)
            | Lazy::FunctionSet(..)
            | Lazy::Cup(..)
            | Lazy::Cap(..)
            | Lazy::Diff(..)
            | Lazy::Union(_)
    ) {
        return Ok(());
    }
    check_counted_parts(set)?;
    match streamed(set) {
        Some(Streamed::Exact(size)) if size > tla_values::SET_BOUND as u128 => {
            Err(crate::value::set_bound_exceeded())
        }
        Some(Streamed::AtMost(size)) if size > tla_values::SET_BOUND as u128 => count_tested(lazy),
        _ => Ok(()),
    }
}

// `toSetEnum` makes the set's Enumerator before it adds any element to its ValueVec, so a set of
// functions, records or tuples asks whether it is empty (`Value.isEmpty`) before the bound can
// pass, which counts an interval part (`IntervalValue.size`) and fails past 2^31 - 1 elements,
// as does the start of any set enumerated in turn that holds one (`start`).
fn check_counted_parts(set: &Value) -> Evaluated<()> {
    if !holds_uncounted_part(set) {
        return Ok(());
    }
    // `UnionValue.Enumerator` starts each set in turn only as it passes the elements of those
    // before it, which the bound may stop first.
    if let Value::Lazy(lazy) = set
        && let Lazy::Union(Value::Set(sets)) = &***lazy
        && sets.iter().skip(1).any(holds_uncounted_part)
    {
        return fail("a union TLC counts an interval within past its first set");
    }
    start_part(set)
}

/// Whether a set is, or is built of, a set of functions, records or tuples with an interval part
/// of more than 2^31 - 1 elements, which TLC fails to count as it asks whether the set is empty.
pub(crate) fn holds_uncounted_part(set: &Value) -> bool {
    let is_uncounted = |part: &Value| {
        matches!(part, Value::Interval(low, high, _)
            if crate::value::interval_size(*low, *high).is_err())
            || holds_uncounted_part(part)
    };
    let Value::Lazy(lazy) = set else {
        return false;
    };
    match &***lazy {
        Lazy::Product(factors) => factors.iter().any(is_uncounted),
        Lazy::RecordSet(fields, _) => fields.iter().any(|(_, part)| is_uncounted(part)),
        Lazy::FunctionSet(domain, range) => is_uncounted(domain) || is_uncounted(range),
        Lazy::Cap(left, right) | Lazy::Cup(left, right) | Lazy::Diff(left, right) => {
            holds_uncounted_part(left) || holds_uncounted_part(right)
        }
        Lazy::Union(Value::Set(sets)) => sets.iter().any(holds_uncounted_part),
        Lazy::Subset(set) | Lazy::Seq(set) | Lazy::Union(set) | Lazy::Filter(set, _) => {
            holds_uncounted_part(set)
        }
        Lazy::Nat | Lazy::Int | Lazy::Real | Lazy::Strings | Lazy::Any => false,
    }
}

/// Where TLC's `elements` of `set` fails as it starts, asking a set of functions, records or
/// tuples it enumerates whether it is empty, which counts an interval part it can't count, the
/// values the failure passes through, `set` first (`emptiness_chain`): `SetCupValue.Enumerator`
/// starts S and then T, `SetDiffValue.Enumerator` starts S, and `UnionValue.Enumerator` the first
/// set of a set of one, each `elements` throwing the failure on with its value's source. `None`
/// where the evaluator doesn't follow where it fails.
pub(crate) fn uncounted_chain(set: &Value) -> Option<Vec<Value>> {
    let Value::Lazy(lazy) = set else {
        return None;
    };
    let through = |inner: &Value| {
        uncounted_chain(inner).map(|chain| std::iter::once(set.clone()).chain(chain).collect())
    };
    match &***lazy {
        Lazy::Product(_) | Lazy::RecordSet(..) | Lazy::FunctionSet(..) => {
            emptiness_chain(set).ok().flatten()
        }
        Lazy::Union(Value::Set(sets)) if sets.len() == 1 => through(sets.iter().next()?),
        Lazy::Cup(left, right) if is_enumerable(left) && is_enumerable(right) => {
            if holds_uncounted_part(left) {
                through(left)
            } else if is_counted(left) {
                through(right)
            } else {
                None
            }
        }
        Lazy::Diff(left, _) if is_enumerable(left) => through(left),
        _ => None,
    }
}

/// Whether TLC enumerates a set without counting an interval it can't: a set enumeration, an
/// interval of at most 2^31 - 1 elements, or a set of functions, records or tuples of those.
pub(crate) fn is_counted(set: &Value) -> bool {
    match set {
        Value::Set(_) => true,
        Value::Interval(low, high, _) => crate::value::interval_size(*low, *high).is_ok(),
        Value::Lazy(lazy) => match &***lazy {
            Lazy::Product(factors) => factors.iter().all(is_counted),
            Lazy::RecordSet(fields, _) => fields.iter().all(|(_, part)| is_counted(part)),
            Lazy::FunctionSet(domain, range) => is_counted(domain) && is_counted(range),
            _ => false,
        },
        _ => false,
    }
}

/// Where TLC's `elements` of a set of functions, records or tuples fails as it asks whether the
/// set is empty (`Value.isEmpty`), counting an interval part of more than 2^31 - 1 elements, the
/// values the failure passes through, `set` first: `isEmpty` asks each part in turn up to an empty
/// one, a nested set of functions, records or tuples in its own `isEmpty`. `Ok(None)` where it
/// doesn't fail so; `Err` where a part is one the evaluator doesn't follow `isEmpty` of.
pub(crate) fn emptiness_chain(set: &Value) -> Result<Option<Vec<Value>>, ()> {
    let Value::Lazy(lazy) = set else {
        return Err(());
    };
    let parts: Vec<&Value> = match &***lazy {
        Lazy::Product(factors) => factors.iter().collect(),
        Lazy::RecordSet(fields, _) => fields.iter().map(|(_, part)| part).collect(),
        Lazy::FunctionSet(domain, range) => vec![domain, range],
        _ => return Err(()),
    };
    let is_function_set = matches!(&***lazy, Lazy::FunctionSet(..));
    for (index, part) in parts.into_iter().enumerate() {
        let chain = match part {
            Value::Set(_) => None,
            Value::Interval(low, high, _) => crate::value::interval_size(*low, *high)
                .is_err()
                .then(Vec::new),
            Value::Lazy(inner) => match &***inner {
                Lazy::Nat
                | Lazy::Int
                | Lazy::Real
                | Lazy::Strings
                | Lazy::Seq(_)
                | Lazy::Subset(_) => None,
                Lazy::Product(_) | Lazy::RecordSet(..) | Lazy::FunctionSet(..) => {
                    emptiness_chain(part)?
                }
                _ => return Err(()),
            },
            _ => return Err(()),
        };
        if let Some(chain) = chain {
            return Ok(Some(std::iter::once(set.clone()).chain(chain).collect()));
        }
        // `[S -> T]` is empty where S isn't and T is, so it asks T only past a nonempty S; a
        // product or a set of records stops at an empty part.
        let is_empty = crate::eval::is_empty(part).map_err(|_| ())?;
        if is_empty && (!is_function_set || index == 0) {
            return Ok(None);
        }
    }
    Ok(None)
}

// `SetCapValue.Enumerator` and `SetDiffValue.Enumerator`: the elements of the set they enumerate
// that the test keeps, which go into the ValueVec in turn. Followed where that set yields its
// normalized set's elements in their order and no test fails.
fn count_tested(lazy: &Lazy) -> Evaluated<()> {
    const UNSURE: &str = "a bound TLC tests the elements of past TLCGlobals.setBound";
    let (enumerated, tested, is_kept) = match lazy {
        Lazy::Cap(left, right) if is_enumerable(left) => (left, right, true),
        Lazy::Cap(left, right) => (right, left, true),
        Lazy::Diff(left, right) => (left, right, false),
        _ => return fail(UNSURE),
    };
    let is_in_order = |set: &Value| matches!(set, Value::Set(_) | Value::Interval(..));
    let is_simple = match enumerated {
        Value::Lazy(inner) => match &***inner {
            Lazy::Product(factors) => factors.iter().all(is_in_order),
            _ => false,
        },
        set => is_in_order(set),
    };
    if !is_simple {
        return fail(UNSURE);
    }
    let mut kept = 0usize;
    for element in elements(enumerated)?.iter() {
        match is_member(element, tested) {
            Ok(is_member) if is_member == is_kept => {
                kept += 1;
                if kept > tla_values::SET_BOUND {
                    return Err(crate::value::set_bound_exceeded());
                }
            }
            Ok(_) => {}
            Err(_) => return fail(UNSURE),
        }
    }
    Ok(())
}

// The sets TLC overrides with Java classes it can't enumerate: Nat, Int, Real and STRING.
/// The set of functions TLC fails to enumerate (`SetOfFcnsValue.Enumerator`), its domain, or its
/// range where its domain isn't empty, infinite, that a set is or that a lazy filter filters.
pub(crate) fn unenumerable_function_set(set: &Value) -> Option<Value> {
    let Value::Lazy(lazy) = set else {
        return None;
    };
    match &***lazy {
        Lazy::Filter(base, _) => unenumerable_function_set(base),
        Lazy::FunctionSet(domain, range)
            if !is_empty_by_argument(domain)
                && (is_infinite(domain)
                    || is_infinite(range)
                        && elements(domain).is_ok_and(|domain| !domain.is_empty())) =>
        {
            Some(set.clone())
        }
        _ => None,
    }
}

/// The values whose `elements` a failure to enumerate `set` passes through, `set` first, as
/// TLC's enumerators fail as they are built (`Enumerator`'s constructor in `SetOfTuplesValue`,
/// `SetOfRcdsValue`, `SetOfFcnsValue`, `SetPredValue`, `SetDiffValue`, `SetCapValue`,
/// `SetCupValue` and `UnionValue`): each `elements` catches the failure and throws it on as a
/// FingerprintException headed by its value where that has a source. `Ok(None)` where TLC
/// builds the enumerator, or where it fails before it calls `elements`, on an overridden set it
/// can't enumerate; `Err` where the enumerator takes elements as it is built, which the
/// evaluator doesn't place.
pub(crate) fn enumeration_chain(set: &Value) -> Result<Option<Vec<Value>>, ()> {
    let Value::Lazy(lazy) = set else {
        return match set {
            Value::Set(_) | Value::Interval(..) => Ok(None),
            _ => Err(()),
        };
    };
    let fails = |inner: Option<Vec<Value>>| {
        Ok(inner.map(|inner| std::iter::once(set.clone()).chain(inner).collect()))
    };
    let is_plain = |value: &Value| matches!(value, Value::Set(_) | Value::Interval(..));
    match &***lazy {
        lazy if lazy.is_overridden() => Ok(None),
        Lazy::Filter(base, _) | Lazy::Diff(base, _) => {
            if !is_enumerable(base) {
                fails(Some(Vec::new()))
            } else {
                fails(enumeration_chain(base)?)
            }
        }
        Lazy::Cap(left, right) => {
            if is_enumerable(left) {
                fails(enumeration_chain(left)?)
            } else if is_enumerable(right) {
                fails(enumeration_chain(right)?)
            } else {
                fails(Some(Vec::new()))
            }
        }
        Lazy::Cup(left, right) => {
            if !is_enumerable(left) || !is_enumerable(right) {
                return fails(Some(Vec::new()));
            }
            match enumeration_chain(left)? {
                Some(chain) => fails(Some(chain)),
                None => fails(enumeration_chain(right)?),
            }
        }
        // The enumerator enumerates each set and takes its first element before the next set, a
        // first element a lazy set may fail to give otherwise.
        Lazy::Product(_) | Lazy::RecordSet(..) => {
            let components: Vec<&Value> = match &***lazy {
                Lazy::Product(sets) => sets.iter().collect(),
                Lazy::RecordSet(fields, _) => fields.iter().map(|(_, value)| value).collect(),
                _ => unreachable!(),
            };
            if is_empty_by_argument(set) {
                return Ok(None);
            }
            for component in components {
                if !is_enumerable(component) {
                    return fails(Some(Vec::new()));
                }
                if !is_plain(component) {
                    return match enumeration_chain(component)? {
                        Some(chain) => fails(Some(chain)),
                        None => Err(()),
                    };
                }
            }
            Ok(None)
        }
        // The enumerator converts the domain (`toSetEnum`), which sizes a power set, and then
        // enumerates the range once for each element of a domain that has one.
        Lazy::FunctionSet(domain, range) => {
            // A lazy domain's `toSetEnum` enumerates it (`elements`), whose enumerator may fail as
            // it is built; an overridden set's gives null, which TLC reports itself.
            if matches!(domain, Value::Lazy(_))
                && let Some(chain) = enumeration_chain(domain)?
            {
                fails(Some(chain))
            } else if unenumerable_function_set(set).is_some() {
                fails(Some(Vec::new()))
            } else if let Some(chain) = failing_power_set(domain)? {
                fails(Some(chain))
            } else if is_plain(domain)
                && !is_empty(domain)
                && let Some(chain) = failing_power_set(range)?
            {
                fails(Some(chain))
            } else if is_plain(domain) && is_plain(range) {
                Ok(None)
            } else if is_unenumerable_filter(domain)
                || (is_plain(domain) && !is_empty(domain) && is_unenumerable_filter(range))
            {
                // `elements` asks whether the set is empty first (`Value.isEmpty`), which
                // enumerates such a filter, and fails in the filter's own Enumerator, whose value
                // `CallStackTool` copied without its source.
                fails(Some(Vec::new()))
            } else {
                Err(())
            }
        }
        // The enumerator takes the first set, which it enumerates as it is built.
        Lazy::Union(sets) => {
            if !is_enumerable(sets) {
                return fails(Some(Vec::new()));
            }
            // A power set the enumerator enumerates fails as it sizes its base.
            if let Some(chain) = failing_power_set(sets)? {
                return fails(Some(chain));
            }
            let Value::Set(inner) = sets else {
                return Err(());
            };
            match inner.iter().next() {
                None => Ok(None),
                Some(first) if !is_enumerable(first) => fails(Some(Vec::new())),
                Some(first) => fails(enumeration_chain(first)?),
            }
        }
        // `SubsetValue.elements` sizes its base (`elementsNormalized`), as `toSetEnum` sizes the
        // power set by its base (`SubsetValue.size`): a base TLC can't count fails there, and
        // each power set the failure passes through throws it on with its source.
        Lazy::Subset(base) => match base_size_chain(base)? {
            Some(chain) => fails(Some(chain)),
            None if is_plain(base) => Ok(None),
            None => Err(()),
        },
        _ => Err(()),
    }
}

// The power sets nested in `base` whose `size` a failure to count `base` passes through, the
// outermost first, then an overridden set that fails, where TLC can't count it: an overridden
// set (`UserValue.size`), an interval of more than 2^31 - 1 elements (`IntervalValue.size`), or
// the power set of either. `Ok(None)` where TLC counts it, a set enumeration or an interval;
// `Err` where the evaluator doesn't follow how TLC counts it.
fn base_size_chain(base: &Value) -> Result<Option<Vec<Value>>, ()> {
    match base {
        Value::Set(_) => Ok(None),
        Value::Interval(low, high, _) => {
            Ok((crate::value::interval_size(*low, *high).is_err()).then(Vec::new))
        }
        Value::Lazy(lazy) => match &***lazy {
            // `UserValue.size` throws the failure on with the set's source, where it has one.
            Lazy::Nat | Lazy::Int | Lazy::Real | Lazy::Strings | Lazy::Seq(_) => {
                Ok(Some(vec![base.clone()]))
            }
            // `SubsetValue.size` sizes its own base.
            Lazy::Subset(inner) => Ok(base_size_chain(inner)?
                .map(|chain| std::iter::once(base.clone()).chain(chain).collect())),
            _ => Err(()),
        },
        _ => Err(()),
    }
}

// Where `set` is a power set, the values its enumeration fails through as it sizes its base
// (`enumeration_chain`), or `Err` where it doesn't fail so; `Ok(None)` where it isn't one.
fn failing_power_set(set: &Value) -> Result<Option<Vec<Value>>, ()> {
    match set {
        Value::Lazy(lazy) if matches!(***lazy, Lazy::Subset(_)) => match enumeration_chain(set)? {
            Some(chain) => Ok(Some(chain)),
            None => Err(()),
        },
        _ => Ok(None),
    }
}

// A filter of an overridden set, whose Enumerator fails at once (`SetPredValue.Enumerator`), or a
// filter of such a filter, whose Enumerator makes the one of the filter it filters as it is made.
pub(crate) fn is_unenumerable_filter(set: &Value) -> bool {
    matches!(set, Value::Lazy(lazy) if matches!(&***lazy,
        Lazy::Filter(base @ Value::Lazy(inner), _)
            if (inner.is_overridden() && !matches!(&***inner, Lazy::Any))
                || is_unenumerable_filter(base)))
}

/// Where `set` is a power set whose base TLC can't count, the values a failure to count it passes
/// through, `set` first, as `SubsetValue.size` throws it on (`enumeration_chain`).
pub(crate) fn power_set_sizing_chain(set: &Value) -> Option<Vec<Value>> {
    match set {
        Value::Lazy(lazy) if matches!(***lazy, Lazy::Subset(_)) => enumeration_chain(set).ok()?,
        _ => None,
    }
}

/// Whether a set is, or is built of, a power set TLC keeps lazy (`SubsetValue`), which a failure
/// to count its base may pass through.
pub(crate) fn holds_power_set(set: &Value) -> bool {
    match set {
        Value::Set(elements) => elements.iter().any(holds_power_set),
        Value::Unsorted(elements) => elements.iter().any(holds_power_set),
        Value::Lazy(lazy) => match &***lazy {
            Lazy::Subset(_) => true,
            Lazy::FunctionSet(left, right)
            | Lazy::Cap(left, right)
            | Lazy::Cup(left, right)
            | Lazy::Diff(left, right) => holds_power_set(left) || holds_power_set(right),
            Lazy::RecordSet(fields, _) => fields.iter().any(|(_, set)| holds_power_set(set)),
            Lazy::Product(sets) => sets.iter().any(holds_power_set),
            Lazy::Seq(set) | Lazy::Union(set) | Lazy::Filter(set, _) => holds_power_set(set),
            Lazy::Nat | Lazy::Int | Lazy::Real | Lazy::Strings | Lazy::Any => false,
        },
        _ => false,
    }
}

/// Whether the values a failure to enumerate a set passes through (`enumeration_chain`) end at
/// a power set, whose base TLC failed to count, or at the overridden base of one.
pub(crate) fn ends_sizing_base(chain: &[Value]) -> bool {
    let is_power_set =
        |value: &Value| matches!(value, Value::Lazy(lazy) if matches!(***lazy, Lazy::Subset(_)));
    match chain {
        [.., last] if is_power_set(last) => true,
        [.., power_set, Value::Lazy(base)] => base.is_overridden() && is_power_set(power_set),
        _ => false,
    }
}

fn is_infinite(set: &Value) -> bool {
    matches!(set, Value::Lazy(lazy) if matches!(***lazy, Lazy::Nat | Lazy::Int | Lazy::Real | Lazy::Strings))
}

// The elements of each set a set of records or tuples combines, as `getComponentElements` reads
// them: TLC's message for the first it can't enumerate, and no combinations past an empty one.
fn component_elements<'a>(
    sets: impl Iterator<Item = &'a Value>,
    describe: impl Fn(usize, &Value) -> String,
) -> Evaluated<Vec<Rc<Vec<Value>>>> {
    // TLC finds the set empty by a component that is, before it enumerates any
    // (`SetOfRcdsValue.elements`, `SetOfTuplesValue.elements`): `isEmpty` asks each in turn up to
    // an empty one, which fails on one that isn't a set (`Value.isEmpty`).
    let sets: Vec<&Value> = sets.collect();
    for set in &sets {
        if crate::eval::is_empty(set)? {
            return Ok(vec![Rc::new(Vec::new())]);
        }
    }
    let mut lists = Vec::new();
    for (index, set) in sets.into_iter().enumerate() {
        if is_infinite(set) {
            return fail_runtime("enumerated an infinite set", describe(index, set));
        }
        let elements = elements(set)?;
        if elements.is_empty() {
            return Ok(vec![elements]);
        }
        lists.push(elements);
    }
    Ok(lists)
}

// The elements an intersection, a union or a difference enumerates, sorted: TLC streams them
// unsorted (`SetCapValue`'s, `UnionValue`'s, `SetCupValue`'s and `SetDiffValue`'s Enumerator)
// and sorts them, together with whatever else its consumer collects, only where that consumer
// normalizes, so a failure to sort them may not be TLC's, which the count records.
fn sorted_combination(values: Vec<Value>) -> Evaluated<Vec<Value>> {
    let sorted = sorted(values);
    if sorted.is_err() {
        COMBINATION_SORT_FAILURES.with(|count| count.set(count.get() + 1));
    }
    sorted
}

fn sorted(values: Vec<Value>) -> Evaluated<Vec<Value>> {
    match set_of(values)? {
        Value::Set(elements) => Ok(match Rc::try_unwrap(elements) {
            Ok(set) => Rc::unwrap_or_clone(set.elements),
            Err(set) => set.elements.as_ref().clone(),
        }),
        _ => unreachable!("set_of makes a set"),
    }
}

// Every choice of one element from each set, the last set varying fastest.
fn product(sets: &[Rc<Vec<Value>>]) -> Evaluated<Vec<Vec<Value>>> {
    let mut size = 1;
    for set in sets {
        size = checked_size(size, set.len())?;
    }
    let mut choices = Vec::with_capacity(size);
    let mut positions = vec![0; sets.len()];
    if sets.iter().any(|set| set.is_empty()) {
        return Ok(choices);
    }
    loop {
        choices.push(
            positions
                .iter()
                .zip(sets)
                .map(|(&position, set)| set[position].clone())
                .collect(),
        );
        let mut level = sets.len();
        loop {
            if level == 0 {
                return Ok(choices);
            }
            level -= 1;
            positions[level] += 1;
            if positions[level] < sets[level].len() {
                break;
            }
            positions[level] = 0;
        }
    }
}

/// TLC's `member`: whether a value is in a set, failing where TLC can't tell.
// TLC's `EC.TLC_MODULE_CHECK_MEMBER_OF`, for a value that can't be an element of a set of the
// standard modules.
fn mistyped(value: &Value, set: &str) -> Evaluated<bool> {
    if let Some(error) = print_failure(value) {
        return Err(error);
    }
    fail_coded(
        format!("a mistyped membership in {set}"),
        2158,
        format!(
            "Attempted to check if the value:\n{}\nis an element of {set}.",
            format_value(value)
        ),
    )
}

/// The sets nested in `set` whose own membership tests a failing `is_member(value, set)` was in,
/// outermost first: the values whose `member` TLC's failure passes through after `set`'s, and the
/// element and the set of the test that fails itself. `None` where the failure isn't followed to
/// the set whose own test fails.
pub fn failing_sets(value: &Value, set: &Value) -> Option<(Vec<Value>, Value, Value)> {
    let own = || Some((Vec::new(), value.clone(), set.clone()));
    let Value::Lazy(lazy) = set else {
        return own();
    };
    // `UnionValue.member` asks each set of the union in turn, and fails in the one that fails.
    if let Lazy::Union(sets) = &***lazy {
        for inner in elements(sets).ok()?.iter() {
            match is_member(value, inner) {
                Ok(true) => return None,
                Ok(false) => {}
                Err(_) => return nested_failure(value, inner),
            }
        }
        return None;
    }
    // `SetCupValue.member` asks its first set, then its second.
    if let Lazy::Cup(first, second) = &***lazy {
        for inner in [first, second] {
            match is_member(value, inner) {
                Ok(true) => return None,
                Ok(false) => {}
                Err(_) => return nested_failure(value, inner),
            }
        }
        return None;
    }
    // `SetCapValue.member` and `SetDiffValue.member` ask their first set, then, where it holds
    // the value, their second.
    if let Lazy::Cap(first, second) | Lazy::Diff(first, second) = &***lazy {
        for inner in [first, second] {
            match is_member(value, inner) {
                Ok(true) => {}
                Ok(false) => return None,
                Err(_) => return nested_failure(value, inner),
            }
        }
        return None;
    }
    // `SetPredValue.member` asks its base set first: a filter `CallStackTool` copied has no
    // source, and the FingerprintException of its base passes through it.
    if let Lazy::Filter(base, _) = &***lazy {
        is_member(value, base).err()?;
        return nested_failure(value, base);
    }
    // Each element a nested set tests, in the order `is_member` tests them.
    let tested: Vec<(Value, &Value)> = match (&***lazy, value) {
        (Lazy::FunctionSet(domain, range), Value::Function(function)) => {
            // `SetOfFcnsValue.member` compares its domain with the function's, which fails in the
            // domain's method, or for a function over an interval, a tuple's, in the interval's
            // (`fcn.intv.equals`), which has no source.
            if equals(&Value::set(function.domain.clone()), domain).is_err() {
                let sets = if function.interval.is_some() {
                    Vec::new()
                } else {
                    vec![domain.clone()]
                };
                return Some((sets, value.clone(), set.clone()));
            }
            function
                .range
                .iter()
                .map(|element| (element.clone(), range))
                .collect()
        }
        (Lazy::RecordSet(fields, _), Value::Function(function)) => {
            let positions: Option<Vec<usize>> = fields
                .iter()
                .map(|(name, _)| find_key(function, &Value::Str(Rc::clone(name))).ok()?)
                .collect();
            // A function without the fields fails the set's own test: a value that isn't a record.
            let Some(positions) = positions else {
                return own();
            };
            positions
                .into_iter()
                .zip(fields)
                .map(|(position, (_, set))| (function.range[position].clone(), set))
                .collect()
        }
        (Lazy::Product(factors), _) => match as_tuple(value) {
            Some(tuple) if tuple.len() == factors.len() => {
                tuple.iter().cloned().zip(factors).collect()
            }
            _ => return None,
        },
        (Lazy::Seq(base), _) => as_tuple(value)?
            .iter()
            .map(|element| (element.clone(), base))
            .collect(),
        // `SubsetValue.member` tests each element of an enumerable value in its base, and fails
        // itself on another.
        (Lazy::Subset(_), _) if !is_enumerable(value) => return own(),
        (Lazy::Subset(base), _) => elements(value)
            .ok()?
            .iter()
            .map(|element| (element.clone(), base))
            .collect(),
        // The failure is in the set's own test: a mistyped value.
        (
            Lazy::Nat | Lazy::Int | Lazy::Strings | Lazy::FunctionSet(..) | Lazy::RecordSet(..),
            _,
        ) => return own(),
        _ => return None,
    };
    for (element, nested) in tested {
        match is_member(&element, nested) {
            Ok(true) => {}
            Ok(false) => return None,
            Err(_) => return nested_failure(&element, nested),
        }
    }
    None
}

// `failing_sets` of a nested set whose test of `value` fails, after the nested set.
fn nested_failure(value: &Value, nested: &Value) -> Option<(Vec<Value>, Value, Value)> {
    // A nested product or Seq(S) fails in its own test on a value that isn't a tuple.
    let is_own = matches!(nested, Value::Lazy(lazy) if matches!(***lazy, Lazy::Product(_) | Lazy::Seq(_)))
        && as_tuple(value).is_none();
    let (sets, element, set) = if is_own {
        (Vec::new(), value.clone(), nested.clone())
    } else {
        failing_sets(value, nested)?
    };
    Some((
        std::iter::once(nested.clone()).chain(sets).collect(),
        element,
        set,
    ))
}

/// Where `SubsetValue.member` fails enumerating a set enumeration TLC holds unnormalized, which
/// normalizes it in its own method: the element, or the power sets nested in `set` whose
/// `member` tests the element's elements, outermost first, then the element of those that fails
/// so. `None` where the membership fails otherwise or doesn't fail.
pub fn unnormalized_subset_member(value: &Value, set: &Value) -> Option<Vec<Value>> {
    let Value::Lazy(lazy) = set else {
        return None;
    };
    let Lazy::Subset(base) = &***lazy else {
        return None;
    };
    if matches!(value, Value::Unsorted(_)) {
        return Some(vec![value.clone()]);
    }
    if !matches!(value, Value::Set(_)) {
        return None;
    }
    for element in elements(value).ok()?.iter() {
        match is_member(element, base) {
            Ok(true) => {}
            Ok(false) => return None,
            Err(_) => {
                let inner = unnormalized_subset_member(element, base)?;
                return Some(std::iter::once(base.clone()).chain(inner).collect());
            }
        }
    }
    None
}

/// The sets whose `member` a failing enumeration of `set` fails in, outermost first: TLC
/// enumerates S \cap T and S \ T by S's elements, each tested in T (`SetCapValue.elements`,
/// `SetDiffValue.elements`), whose own method adds no frame, and S \cup T by S's, then T's.
/// `None` where the enumeration fails otherwise or doesn't fail.
pub fn failing_enumeration(set: &Value) -> Option<Vec<Value>> {
    let Value::Lazy(lazy) = set else {
        return None;
    };
    match &***lazy {
        Lazy::Cap(first, second) | Lazy::Diff(first, second) => {
            if elements(first).is_err() {
                return failing_enumeration(first);
            }
            for element in elements(first).ok()?.iter() {
                if is_member(element, second).is_err() {
                    return nested_failure(element, second).map(|(sets, ..)| sets);
                }
            }
            None
        }
        Lazy::Cup(first, second) => {
            if elements(first).is_err() {
                return failing_enumeration(first);
            }
            failing_enumeration(second)
        }
        _ => None,
    }
}

/// The values in whose methods TLC's search of a set enumeration for `value` fails
/// (`ValueVec.search`), outermost first, or none where the search doesn't fail so: a sorted set's
/// binary search fails in `value`'s `compareTo`, and one TLC holds unnormalized in its elements'
/// `equals`.
pub fn failing_search(value: &Value, set: &Value) -> Vec<Value> {
    if !matches!(set, Value::Set(_) | Value::Unsorted(_)) {
        return Vec::new();
    }
    failing_comparisons(|| is_member(value, set))
        .err()
        .unwrap_or_default()
}

/// The set whose method fails where TLC's `cap` or `diff` of a set enumeration or an interval
/// fails testing its elements, as it holds them, in the other operand (`SetEnumValue.cap`,
/// `IntervalValue.diff`), or its `cup` with another set enumeration enumerating it or testing its
/// elements in itself (`SetEnumValue.cup`), with the element its `member` tests.
pub fn failing_operation(
    received: &Value,
    other: &Value,
    is_union: bool,
) -> Option<(Value, Option<Value>)> {
    if !is_reducible(received) {
        return None;
    }
    if is_union && matches!(other, Value::Unsorted(_)) {
        return Some((other.clone(), None));
    }
    if is_union && !is_reducible(other) {
        return None;
    }
    let (enumerated, tested) = if is_union {
        (other, received)
    } else {
        (received, other)
    };
    // A set enumeration TLC can't normalize is Reducible as written (`SetEnumValue.cap` and
    // `diff` walk its elements as built).
    let held = match (enumerated, unnormalized(enumerated)) {
        (Value::Unsorted(written), _) => written.to_vec(),
        (_, Some(written)) => written,
        (_, None) => elements(enumerated).ok()?.to_vec(),
    };
    held.into_iter()
        .find(|element| is_member(element, tested).is_err())
        .map(|element| (tested.clone(), Some(element)))
}

/// A lazy filter's test of an element of its base, which only the evaluator can make.
pub type Filter<'a> = dyn FnMut(&Value, &Value, &Predicate) -> Evaluated<bool> + 'a;

pub fn is_member(value: &Value, set: &Value) -> Evaluated<bool> {
    is_member_filtered(value, set, &mut |_, _, _| {
        fail("a lazy filter's membership outside the evaluator")
    })
}

/// Membership in a set, with `filter` testing an element of a lazy filter nested in it.
pub fn is_member_filtered(
    value: &Value,
    set: &Value,
    test_filter: &mut Filter<'_>,
) -> Evaluated<bool> {
    member_filtered(value, set, test_filter, false)
}

pub(crate) fn member_filtered(
    value: &Value,
    set: &Value,
    test_filter: &mut Filter<'_>,
    closed: bool,
) -> Evaluated<bool> {
    // TLC tests a set it holds unnormalized element by element, as it built it, asking each
    // element whether it equals the value (`ValueVec.search`), one it can't normalize too.
    let written = match set {
        Value::Unsorted(values) => Some(values.to_vec()),
        _ => unnormalized(set),
    };
    if let Some(written) = written {
        for element in &written {
            if equals(element, value)? {
                return Ok(true);
            }
        }
        return Ok(false);
    }
    match set {
        Value::Set(elements) => {
            let (mut low, mut high) = (0, elements.len());
            while low < high {
                let middle = low + (high - low) / 2;
                match compare(value, &elements[middle])? {
                    Ordering::Equal => return Ok(true),
                    Ordering::Less => high = middle,
                    Ordering::Greater => low = middle + 1,
                }
            }
            Ok(false)
        }
        // An untyped model value is in no interval: `IntervalValue.member` says false.
        Value::Interval(..) if matches!(value, Value::Model(model) if model.model_type() == 0) => {
            Ok(false)
        }
        // The sets the standard modules override and the sets of functions, records and tuples hand
        // a model value to `ModelValue.modelValueMember`, which says false, unless it is typed.
        Value::Lazy(lazy)
            if matches!(value, Value::Model(model) if model.model_type() == 0)
                && matches!(
                    ***lazy,
                    Lazy::Nat
                        | Lazy::Int
                        | Lazy::Strings
                        | Lazy::Seq(_)
                        | Lazy::FunctionSet(..)
                        | Lazy::RecordSet(..)
                        | Lazy::Product(_)
                ) =>
        {
            Ok(false)
        }
        Value::Lazy(lazy)
            if matches!(value, Value::Model(_))
                && matches!(
                    ***lazy,
                    Lazy::Nat
                        | Lazy::Int
                        | Lazy::Strings
                        | Lazy::Seq(_)
                        | Lazy::FunctionSet(..)
                        | Lazy::RecordSet(..)
                        | Lazy::Product(_)
                ) =>
        {
            fail_runtime(
                "a typed model value's membership",
                format!(
                    "Attempted to check if the typed model value {} is an element of\n{}",
                    format_pretty(value),
                    format_pretty(set)
                ),
            )
        }
        Value::Interval(low, high, _) => match value {
            Value::Int(int) => Ok(low <= int && int <= high),
            _ if low > high => Ok(false),
            _ if let Some(error) = print_failure(value) => Err(error),
            _ => fail_runtime(
                "a mistyped membership in an interval",
                format!(
                    "Attempted to check if the value:\n{}\nis in the integer interval {}",
                    format_pretty(value),
                    format_pretty(set)
                ),
            ),
        },
        Value::Lazy(lazy) => match &***lazy {
            Lazy::Nat => match value {
                Value::Int(int) => Ok(*int >= 0),
                _ => mistyped(value, "Nat"),
            },
            Lazy::Int => match value {
                Value::Int(_) => Ok(true),
                _ => mistyped(value, "Int"),
            },
            Lazy::Real => fail("a membership in Real"),
            // `AnySet.member`.
            Lazy::Any => Ok(true),
            Lazy::Strings => match value {
                Value::Str(_) => Ok(true),
                _ => mistyped(value, "STRING"),
            },
            // `SubsetValue.member`.
            Lazy::Subset(base) => {
                if !is_enumerable(value) {
                    prepare_member_error_display(value, set, closed)?;
                    return fail_runtime(
                        "a membership in SUBSET of a non-enumerable value",
                        format!(
                            "Attempted to check if the non-enumerable value\n{}\nis element of\n{}",
                            format_pretty(value),
                            format_pretty(set)
                        ),
                    );
                }
                for element in elements(value)?.iter() {
                    if !member_filtered(element, base, test_filter, closed)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Lazy::FunctionSet(domain, range) => {
                if let Value::Lambda(lambda) = value {
                    return crate::value::lambda_as_function_unsure(lambda);
                }
                let Value::Function(function) = value else {
                    prepare_member_error_display(value, set, closed)?;
                    return fail_runtime(
                        "a mistyped membership in a set of functions",
                        format!(
                            "Attempted to check if \n{}\nwhich is not a TLC function value, is in the set of functions:\n{}",
                            format_value(value),
                            format_pretty(set)
                        ),
                    );
                };
                // `SetOfFcnsValue.member`: its domain equals the function's, or the interval a
                // function is over equals its domain.
                let is_domain = match (function.class.get(), function.interval) {
                    (Class::Tuple, _) => {
                        equals(&Value::interval(1, function.range.len() as i32), domain)?
                    }
                    (_, Some((low, high))) => equals(&Value::interval(low, high), domain)?,
                    _ => equals(domain, &Value::set(function.domain.clone()))?,
                };
                if !is_domain {
                    return Ok(false);
                }
                for element in &function.range {
                    if !member_filtered(element, range, test_filter, closed)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            // `SetOfRcdsValue.member`: a value `toRcd` makes no record of fails.
            Lazy::RecordSet(fields, _) => {
                // TLC takes a function it keeps lazy as the value it builds (`toFcnRcd`).
                if let Value::Lambda(lambda) = value {
                    return crate::value::lambda_as_function_unsure(lambda);
                }
                let Value::Function(function) = value else {
                    return non_record(value, set, closed);
                };
                let is_record = match function.class.get() {
                    Class::Tuple => function.domain.is_empty(),
                    _ => function
                        .domain
                        .iter()
                        .all(|key| matches!(key, Value::Str(_))),
                };
                if !is_record {
                    return non_record(value, set, closed);
                }
                if function.domain.len() != fields.len() {
                    return Ok(false);
                }
                for (name, set) in fields {
                    match find_key(function, &Value::Str(Rc::clone(name)))? {
                        Some(position) => {
                            if !member_filtered(
                                &function.range[position],
                                set,
                                test_filter,
                                closed,
                            )? {
                                return Ok(false);
                            }
                        }
                        None => return Ok(false),
                    }
                }
                Ok(true)
            }
            // `SetOfTuplesValue.member`: a function `toTuple` makes no tuple of is in none, but a
            // value that isn't a function, or a function over a key that isn't an integer, fails.
            Lazy::Product(factors) => {
                // TLC takes a function it keeps lazy as a tuple (`toTuple`).
                if let Value::Lambda(lambda) = value {
                    return crate::value::lambda_as_tuple(lambda);
                }
                let Some(tuple) = as_tuple(value) else {
                    let Value::Function(function) = value else {
                        return non_tuple(value, set, closed);
                    };
                    if function.interval.is_none()
                        && !function
                            .domain
                            .iter()
                            .all(|key| matches!(key, Value::Int(_)))
                    {
                        return non_tuple(value, set, closed);
                    }
                    return Ok(false);
                };
                if tuple.len() != factors.len() {
                    return Ok(false);
                }
                for (element, factor) in tuple.iter().zip(factors) {
                    if !member_filtered(element, factor, test_filter, closed)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            // `Sequences.member`.
            Lazy::Seq(base) => {
                // TLC takes a function it keeps lazy as a tuple (`toTuple`).
                if let Value::Lambda(lambda) = value {
                    return crate::value::lambda_as_tuple(lambda);
                }
                let Some(tuple) = as_tuple(value) else {
                    return mistyped(value, &format_pretty(set));
                };
                for element in tuple {
                    if !member_filtered(element, base, test_filter, closed)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Lazy::Filter(base, predicate) => test_filter(value, base, predicate),
            // `UnionValue.member`: in an element of an enumerable set of sets.
            Lazy::Union(sets) => {
                if !is_enumerable(sets) {
                    return fail("a membership in the union of a set TLC doesn't enumerate");
                }
                let sets = elements(sets)?;
                for inner in sets.iter() {
                    if member_filtered(value, inner, test_filter, closed)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            Lazy::Cap(left, right) => Ok(member_filtered(value, left, test_filter, closed)?
                && member_filtered(value, right, test_filter, closed)?),
            Lazy::Cup(left, right) => Ok(member_filtered(value, left, test_filter, closed)?
                || member_filtered(value, right, test_filter, closed)?),
            Lazy::Diff(left, right) => Ok(member_filtered(value, left, test_filter, closed)?
                && !member_filtered(value, right, test_filter, closed)?),
        },
        // The `member` of each class of value that isn't a set.
        _ => {
            let kind = match set {
                Value::Bool(_) => "boolean",
                Value::Int(_) => "integer",
                Value::Str(_) => "string",
                Value::Model(_) => "model value",
                Value::Function(function) if function.class.get() == Class::Tuple => {
                    return fail_runtime(
                        "a membership in a tuple",
                        "Attempted to check set membership in a tuple value.".into(),
                    );
                }
                Value::Function(function) if function.class.get() == Class::Record => {
                    return fail_runtime(
                        "a membership in a record",
                        format!(
                            "Attempted to check if element:\n{}\nis in the record:\n{}",
                            format_pretty(value),
                            format_pretty(set)
                        ),
                    );
                }
                Value::Function(_) | Value::Lambda(_) => "function",
                _ => {
                    return fail(format!(
                        "a membership in a {}, which isn't a set",
                        set.kind_name()
                    ));
                }
            };
            fail_runtime(
                format!("a membership in a {kind}"),
                format!(
                    "Attempted to check if the value:\n{}\nis an element of the {kind} {}",
                    format_pretty(value),
                    format_pretty(set)
                ),
            )
        }
    }
}

// Java's generated functions share one domain array. Scalar keys make the mathematical
// enumerator's extra key comparisons unobservable; exceptional composite keys do not.
fn has_scalar_domain(domain: &Value) -> bool {
    match domain {
        Value::Set(values) | Value::Unsorted(values) => values.iter().all(|key| {
            matches!(
                key,
                Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::Model(_)
            )
        }),
        Value::Interval(..) => true,
        Value::Lazy(lazy) => matches!(&***lazy, Lazy::Nat | Lazy::Int | Lazy::Strings),
        _ => false,
    }
}

// UserValue.size throws for these packaged infinite sets. SubsetValue.size calls
// its base's size first, so no function or shared domain array can be constructed.
fn domain_size_fails(domain: &Value) -> bool {
    match domain {
        Value::Lazy(lazy) => match &***lazy {
            Lazy::Nat | Lazy::Int | Lazy::Strings => true,
            Lazy::Subset(base) => domain_size_fails(base),
            _ => false,
        },
        _ => false,
    }
}

// A diagnostic observes only these captured values, never a predicate or body.
fn captured_display_tree(value: &Value) -> bool {
    match value {
        Value::Set(values) | Value::Unsorted(values) => {
            values.java_class == Some(SetClass::Enumeration)
                && values.iter().all(captured_display_tree)
        }
        Value::Interval(..) => crate::value::has_java_set_representation(value),
        Value::Lazy(lazy) => {
            if !crate::value::has_java_set_representation(value) {
                return false;
            }
            match &***lazy {
                Lazy::Nat | Lazy::Int | Lazy::Real | Lazy::Strings => true,
                // Function-set expansion can compare a shared domain array containing Any.
                // The mathematical enumerator does not retain that physical array identity.
                Lazy::Any => false,
                Lazy::Seq(base) | Lazy::Subset(base) | Lazy::Union(base) => {
                    captured_display_tree(base)
                }
                Lazy::FunctionSet(domain, range) => {
                    (has_scalar_domain(domain) || domain_size_fails(domain))
                        && captured_display_tree(domain)
                        && captured_display_tree(range)
                }
                Lazy::Cup(left, right) | Lazy::Cap(left, right) | Lazy::Diff(left, right) => {
                    captured_display_tree(left) && captured_display_tree(right)
                }
                Lazy::RecordSet(fields, _) => {
                    fields.iter().all(|(_, set)| captured_display_tree(set))
                }
                Lazy::Product(factors) => factors.iter().all(captured_display_tree),
                Lazy::Filter(..) => false,
            }
        }
        Value::Function(function) => {
            (matches!(
                function.java_class.get(),
                Some(Class::Tuple | Class::Record)
            ) || function.java_class.get() == Some(Class::Plain) && function.is_eager_record.get())
                && (function
                    .domain
                    .iter()
                    .all(|key| matches!(key, Value::Int(_)))
                    || function
                        .domain
                        .iter()
                        .all(|key| matches!(key, Value::Str(_))))
                && function.range.iter().all(captured_display_tree)
        }
        Value::Lambda(_) | Value::Null => false,
        _ => true,
    }
}

// Value.toString uses swallow=true: a lazy expansion failure falls back to printing
// its operands, whose own SetEnum normalization can still fail outside that catch.
fn check_member_error_display(value: &Value) -> Evaluated<()> {
    match value {
        Value::Set(_) => elements(value)?
            .iter()
            .try_for_each(check_member_error_display),
        Value::Unsorted(_) => crate::eval::check_unchecked(value),
        Value::Function(function) => {
            // RecordValue and string-domain FcnRcdValue render fields in their snapshot's
            // retained order. Integer-domain functions normalize a private snapshot first.
            let sorted = function.java_class.get() == Some(Class::Tuple)
                || function
                    .domain
                    .iter()
                    .all(|key| matches!(key, Value::Int(_)));
            for at in print_order(function, sorted) {
                check_member_error_display(&function.domain[at])?;
                check_member_error_display(&function.range[at])?;
            }
            Ok(())
        }
        Value::Lazy(_) | Value::Lambda(_) => crate::eval::check_to_string(value, true),
        _ => Ok(()),
    }
}

/// Whether TLC fails printing the value in a membership's message.
pub(crate) fn fails_member_display(value: &Value) -> bool {
    check_member_error_display(value).is_err()
}

fn prepare_member_error_display(value: &Value, set: &Value, closed: bool) -> Evaluated<()> {
    let checked = [value, set]
        .into_iter()
        .try_for_each(check_member_error_display);
    if closed && captured_display_tree(value) && captured_display_tree(set) {
        return checked;
    }
    // Where the evaluator doesn't hold the classes TLC prints, a message whose text may fail to
    // print is one it can't word.
    if checked.is_err() {
        return fail("a membership's message whose values TLC may fail to print");
    }
    Ok(())
}

fn non_record(value: &Value, set: &Value, closed: bool) -> Evaluated<bool> {
    if matches!(value, Value::Model(_)) {
        return fail("a model value's membership in a set of records");
    }
    prepare_member_error_display(value, set, closed)?;
    fail_runtime(
        "a mistyped membership in a set of records",
        format!(
            "Attempted to check if non-record\n{}\nis in the set of records:\n{}",
            format_value(value),
            format_pretty(set)
        ),
    )
}

fn non_tuple(value: &Value, set: &Value, closed: bool) -> Evaluated<bool> {
    if matches!(value, Value::Model(_)) {
        return fail("a model value's membership in a set of tuples");
    }
    prepare_member_error_display(value, set, closed)?;
    fail_runtime(
        "a mistyped membership in a set of tuples",
        format!(
            "Attempted to check if non-tuple\n{}\nis in the set of tuples:\n{}",
            format_pretty(value),
            format_pretty(set)
        ),
    )
}

/// The elements of a function whose domain is 1..n, in order.
pub fn as_tuple(value: &Value) -> Option<&[Value]> {
    let Value::Function(function) = value else {
        return None;
    };
    let is_tuple = function
        .domain
        .iter()
        .enumerate()
        .all(|(index, key)| matches!(key, Value::Int(int) if *int == index as i32 + 1));
    is_tuple.then_some(&function.range[..])
}

// TLC's reducible sets, a set enumeration or an interval, which combine with another set element by
// element.
pub(crate) fn is_reducible(value: &Value) -> bool {
    matches!(
        value,
        Value::Set(_) | Value::Unsorted(_) | Value::Interval(..)
    )
}

fn is_empty_reducible(value: &Value) -> bool {
    match value {
        Value::Set(elements) => elements.is_empty(),
        Value::Interval(low, high, _) => low > high,
        _ => false,
    }
}

/// `\cup`. TLC keeps the other operand as it is when one is an empty set enumeration or interval:
/// the right one after an empty left one, and a lazy left one before an empty right one, as
/// `combineReducible` does; otherwise it enumerates the union.
pub fn union(left: &Value, right: &Value) -> Evaluated<Value> {
    let result = union_contents(left, right)?;
    Ok(
        if !crate::value::set_dispatch_is_known(left) || !crate::value::set_dispatch_is_known(right)
        {
            result.without_set_provenance()
        } else {
            result
        },
    )
}

// `IntervalValue`'s `cup`, `cap` and `diff` compute the receiver's size before anything else,
// which fails for an interval of more than 2^31 - 1 elements.
fn size_receiver(receiver: &Value) -> Evaluated<()> {
    if let Value::Interval(low, high, _) = receiver {
        crate::value::interval_size(*low, *high)?;
    }
    Ok(())
}

fn union_contents(left: &Value, right: &Value) -> Evaluated<Value> {
    // `Tool`'s OPCODE_cup: the left operand's `cup` where it is reducible, else the right's.
    if is_reducible(left) {
        size_receiver(left)?;
    } else if is_reducible(right) {
        size_receiver(right)?;
    }
    if is_empty_reducible(left) {
        return Ok(right.clone());
    }
    if is_empty_reducible(right) && !is_reducible(left) {
        return Ok(left.clone());
    }
    // `cup` of a set enumeration or an interval enumerates another set enumeration, which
    // normalizes it.
    if let (true, Value::Unsorted(values)) = (is_reducible(left), right) {
        return Err(unsorted_failure(values));
    }
    // `Tool`'s OPCODE_cup: a reducible operand's `cup`, the other's lazy union otherwise.
    match (is_reducible(left), is_reducible(right)) {
        // `cup` of a set enumeration or an interval: its elements as it holds them, then each of
        // the other's that its own `member` finds it lacks, a set TLC holds unnormalized.
        (true, true) => {
            // `IntervalValue.cup` collects every element of the interval first
            // (`ValueVec.addElement`), which fails past its bound.
            if let Value::Interval(low, high, _) = left
                && crate::value::interval_size(*low, *high)? > tla_values::SET_BOUND
            {
                crate::value::check_walk(*low, *high)?;
                let mut all = Vec::with_capacity(tla_values::SET_BOUND);
                for key in *low..=*high {
                    crate::value::push_set_element(&mut all, Value::Int(key))?;
                }
            }
            let written = unnormalized(left);
            let mut all = match (&written, left) {
                (Some(written), _) => written.clone(),
                (None, Value::Unsorted(values)) => values.to_vec(),
                _ => elements(left)?.to_vec(),
            };
            // Each element goes into a ValueVec, which fails once it holds `TLCGlobals.setBound`
            // elements and is given another.
            if all.len() > tla_values::SET_BOUND {
                return Err(crate::value::set_bound_exceeded());
            }
            for element in elements(right)?.iter() {
                let is_held = match left {
                    Value::Unsorted(values) => {
                        let mut is_held = false;
                        for value in values.iter() {
                            if equals(value, element).map_err(|mut error| {
                                error.is_set_reduction = crate::value::set_dispatch_is_known(left)
                                    && crate::value::set_dispatch_is_known(right);
                                error
                            })? {
                                is_held = true;
                                break;
                            }
                        }
                        is_held
                    }
                    _ => is_member(element, left)?,
                };
                // Each element the receiver lacks is collected, up to TLC's bound.
                if !is_held {
                    crate::value::push_set_element(&mut all, element.clone())?;
                }
            }
            match set_of(all.clone()) {
                Ok(set) => {
                    mark_unnormalized(&set, all);
                    Ok(set)
                }
                Err(error)
                    if error
                        .message
                        .as_ref()
                        .is_some_and(|message| !message.is_eval_exception) =>
                {
                    Ok(Value::unsorted(all))
                }
                Err(error) => Err(error),
            }
        }
        // A set enumeration TLC fails to normalize is Reducible all the same, so it comes first.
        (false, false)
            if matches!(right, Value::Unsorted(_)) && !matches!(left, Value::Unsorted(_)) =>
        {
            Ok(lazy(Lazy::Cup(right.clone(), left.clone())))
        }
        (true, false) | (false, false) => Ok(lazy(Lazy::Cup(left.clone(), right.clone()))),
        (false, true) => Ok(lazy(Lazy::Cup(right.clone(), left.clone()))),
    }
}

fn lazy(lazy: Lazy) -> Value {
    Value::lazy(lazy)
}

/// `\cap` (`Tool`'s OPCODE_cap): a reducible operand's elements in the other, the left's first,
/// and a lazy intersection where neither is reducible. `test_filter` tests an element of a lazy
/// filter nested in the other.
pub fn intersection(left: &Value, right: &Value, test_filter: &mut Filter<'_>) -> Evaluated<Value> {
    let result = intersection_contents(left, right, test_filter)?;
    Ok(
        if !crate::value::set_dispatch_is_known(left) || !crate::value::set_dispatch_is_known(right)
        {
            result.without_set_provenance()
        } else {
            result
        },
    )
}

fn intersection_contents(
    left: &Value,
    right: &Value,
    test_filter: &mut Filter<'_>,
) -> Evaluated<Value> {
    let (enumerated, tested) = match (is_reducible(left), is_reducible(right)) {
        (true, _) => (left, right),
        (false, true) => (right, left),
        (false, false) => return Ok(lazy(Lazy::Cap(left.clone(), right.clone()))),
    };
    size_receiver(enumerated)?;
    if let Some(kept) = walked_integers(enumerated, tested, true)? {
        return Ok(kept);
    }
    filter(
        enumerated,
        crate::value::set_dispatch_is_known(left) && crate::value::set_dispatch_is_known(right),
        |element| is_member_filtered(element, tested, test_filter),
    )
}

// `IntervalValue.cap` and `diff` of an interval too long for the evaluator to walk, against an
// interval or a set enumeration of integers alone: each `member` test compares integers and
// can't fail, so what they keep is the integers of the interval in (or, for `diff`, out of) the
// other set, in order, each added to a ValueVec, which fails past `TLCGlobals.setBound`.
// `None` for any other operands, which the walk follows.
fn walked_integers(left: &Value, tested: &Value, is_kept_in: bool) -> Evaluated<Option<Value>> {
    let Value::Interval(low, high, _) = *left else {
        return Ok(None);
    };
    if i64::from(high) - i64::from(low) < crate::value::MAXIMUM_WALK as i64 {
        return Ok(None);
    }
    crate::value::check_walk(low, high)?;
    let mut points: Vec<i32> = match tested {
        Value::Interval(..) => Vec::new(),
        Value::Set(_) | Value::Unsorted(_) => {
            let Some(items) = tested.set_items() else {
                return Ok(None);
            };
            let mut points = Vec::with_capacity(items.len());
            for item in items {
                let Value::Int(point) = item else {
                    return Ok(None);
                };
                points.push(*point);
            }
            points
        }
        _ => return Ok(None),
    };
    points.sort_unstable();
    points.dedup();
    // The stretches of the interval kept, in order.
    let stretches: Vec<(i64, i64)> = match (tested, is_kept_in) {
        (Value::Interval(other_low, other_high, _), true) => {
            vec![(
                i64::from(low.max(*other_low)),
                i64::from(high.min(*other_high)),
            )]
        }
        (Value::Interval(other_low, other_high, _), false) if other_low <= other_high => vec![
            (
                i64::from(low),
                i64::from(high).min(i64::from(*other_low) - 1),
            ),
            (
                i64::from(low).max(i64::from(*other_high) + 1),
                i64::from(high),
            ),
        ],
        (Value::Interval(..), false) => vec![(i64::from(low), i64::from(high))],
        (_, true) => points
            .iter()
            .filter(|&&point| low <= point && point <= high)
            .map(|&point| (i64::from(point), i64::from(point)))
            .collect(),
        (_, false) => {
            let mut stretches = Vec::new();
            let mut start = i64::from(low);
            for &point in points
                .iter()
                .filter(|&&point| low <= point && point <= high)
            {
                stretches.push((start, i64::from(point) - 1));
                start = i64::from(point) + 1;
            }
            stretches.push((start, i64::from(high)));
            stretches
        }
    };
    let mut kept = Vec::new();
    for (start, end) in stretches {
        for point in start..=end {
            crate::value::push_set_element(&mut kept, Value::Int(point as i32))?;
        }
    }
    Ok(Some(Value::set(kept)))
}

/// `\` (`Tool`'s OPCODE_setdiff): a reducible left operand's elements not in the right, and a
/// lazy difference otherwise. `test_filter` tests an element of a lazy filter nested in the right.
pub fn difference(left: &Value, right: &Value, test_filter: &mut Filter<'_>) -> Evaluated<Value> {
    let result = difference_contents(left, right, test_filter)?;
    Ok(
        if !crate::value::set_dispatch_is_known(left) || !crate::value::set_dispatch_is_known(right)
        {
            result.without_set_provenance()
        } else {
            result
        },
    )
}

fn difference_contents(
    left: &Value,
    right: &Value,
    test_filter: &mut Filter<'_>,
) -> Evaluated<Value> {
    if !is_reducible(left) {
        return Ok(lazy(Lazy::Diff(left.clone(), right.clone())));
    }
    size_receiver(left)?;
    if let Some(kept) = walked_integers(left, right, false)? {
        return Ok(kept);
    }
    filter(
        left,
        crate::value::set_dispatch_is_known(left) && crate::value::set_dispatch_is_known(right),
        |element| Ok(!is_member_filtered(element, right, test_filter)?),
    )
}

// The elements of a set that `keep` keeps. TLC's `cap` and `diff` of a set enumeration test its
// elements as it holds them and keep its normalization, so a set TLC holds unnormalized gives one it
// holds unnormalized.
fn filter(
    left: &Value,
    is_physical_reduction: bool,
    mut keep: impl FnMut(&Value) -> Evaluated<bool>,
) -> Evaluated<Value> {
    let written = match left {
        Value::Unsorted(values) => Some(values.to_vec()),
        _ => unnormalized(left),
    };
    // `IntervalValue.cap` and `diff` walk the interval (`IntValue.gen`) without building it,
    // collecting what they keep (`ValueVec.addElement`), up to its bound, as far as the
    // evaluator walks one.
    let held: Box<dyn Iterator<Item = Value> + '_> = match (&written, left) {
        (Some(written), _) => Box::new(written.iter().cloned()),
        (None, Value::Unsorted(values)) => Box::new(values.iter().cloned()),
        (None, Value::Interval(low, high, _)) => {
            crate::value::check_walk(*low, *high)?;
            Box::new(
                (*low..=*high)
                    .map(Value::Int)
                    .take(crate::value::MAXIMUM_WALK + 1),
            )
        }
        (None, _) => Box::new(elements(left)?.to_vec().into_iter()),
    };
    let mut kept = Vec::new();
    for (index, element) in held.enumerate() {
        if index >= crate::value::MAXIMUM_WALK {
            return fail("an interval too large to build");
        }
        if keep(&element).map_err(|mut error| {
            error.is_set_reduction = is_physical_reduction;
            error
        })? {
            // `cap` and `diff` add each element they keep to a ValueVec.
            crate::value::push_set_element(&mut kept, element)?;
        }
    }
    if written.is_none() {
        return Ok(Value::set(kept));
    }
    match crate::value::held_set_of(kept) {
        Ok(set) => Ok(set),
        Err((error, kept)) if error.message.is_some() => Ok(Value::unsorted(kept)),
        Err((error, _)) => Err(error),
    }
}

/// Whether a set of functions, records or tuples is empty by an empty argument, which TLC decides
/// without enumerating the others (`isEmpty` of `SetOfFcnsValue`, `SetOfRcdsValue` and
/// `SetOfTuplesValue`): `[S -> T]` where S isn't empty and T is, and a set of records or tuples one
/// of whose sets is.
pub(crate) fn is_empty_by_argument(set: &Value) -> bool {
    let is_empty = |value: &Value| match value {
        Value::Set(elements) => elements.is_empty(),
        Value::Interval(low, high, _) => low > high,
        Value::Lazy(_) => is_empty_by_argument(value),
        _ => false,
    };
    let is_nonempty = |value: &Value| match value {
        Value::Set(elements) => !elements.is_empty(),
        // `IntervalValue.size`, which fails past 2^31 - 1 elements.
        Value::Interval(low, high, _) => {
            low <= high && crate::value::interval_size(*low, *high).is_ok()
        }
        // A set of functions, records or tuples is nonempty unless its parts empty it
        // (`SetOfFcnsValue.isEmpty`), and SUBSET S and Seq(S) always are.
        Value::Lazy(lazy) => match ***lazy {
            Lazy::Nat | Lazy::Int | Lazy::Real | Lazy::Strings | Lazy::Subset(_) | Lazy::Seq(_) => {
                true
            }
            Lazy::Any => false,
            Lazy::FunctionSet(..) | Lazy::RecordSet(..) | Lazy::Product(_) => {
                !is_empty_by_argument(value)
            }
            // TLC can't tell without enumerating it.
            Lazy::Cap(..) | Lazy::Cup(..) | Lazy::Diff(..) | Lazy::Union(_) | Lazy::Filter(..) => {
                false
            }
        },
        _ => false,
    };
    let Value::Lazy(lazy) = set else {
        return false;
    };
    // `Value.isEmpty` asks each part in turn up to an empty one, and fails on one that isn't a
    // set: an empty part decides only past parts certainly nonempty.
    let is_any_empty = |parts: &mut dyn Iterator<Item = &Value>| {
        for part in parts {
            if is_empty(part) {
                return true;
            }
            if !is_nonempty(part) {
                return false;
            }
        }
        false
    };
    match &***lazy {
        Lazy::FunctionSet(domain, range) => is_nonempty(domain) && is_empty(range),
        Lazy::RecordSet(fields, _) => is_any_empty(&mut fields.iter().map(|(_, set)| set)),
        Lazy::Product(factors) => is_any_empty(&mut factors.iter()),
        _ => false,
    }
}

/// The number of elements of a set TLC can count (`size` of its values).
pub fn cardinality(set: &Value) -> Evaluated<usize> {
    match set {
        Value::Interval(low, high, _) => crate::value::interval_size(*low, *high),
        Value::Lazy(lazy) => match &***lazy {
            Lazy::FunctionSet(domain, range) => function_set_size(set, domain, range),
            // `UserValue.size`.
            lazy if lazy.is_overridden() => fail_runtime(
                "sized a set TLC doesn't enumerate",
                format!(
                    "Attempted to compute the number of elements in the overridden value {}.",
                    format_pretty(set)
                ),
            ),
            // `SubsetValue.size`: 2^|S|, past an int an overflow.
            Lazy::Subset(base) => {
                let size = cardinality(base)?;
                if size >= 31 {
                    return Err(crate::value::EvalError {
                        runtime_exception: crate::value::RuntimeException::Runtime,
                        is_set_normalization: false,
                        is_set_reduction: false,
                        is_followed_comparison: false,
                        is_named_normalization: false,
                        reason: "a power set too large to count".into(),
                        message: Some(crate::value::TlcMessage {
                            text: format!(
                                "Overflow when computing the number of elements in:\n{}",
                                format_pretty(set)
                            ),
                            code: Some(OVERFLOW),
                            is_eval_exception: false,
                            inner: None,
                        }),
                    });
                }
                Ok(1 << size)
            }
            Lazy::Filter(_, predicate) => {
                if let Some(elements) = predicate.converted() {
                    return Ok(elements.len());
                }
                // `SetPredValue.size` converts the filter (`convertAndCache`).
                let elements = crate::value::converted(set)?;
                predicate.cache_conversion(Rc::clone(&elements));
                Ok(elements.len())
            }
            // `SetOfRcdsValue.size` and `SetOfTuplesValue.size`: the product of the parts' sizes.
            Lazy::RecordSet(fields, _) => {
                parts_size(set, fields.iter().map(|(_, part)| part), true)
            }
            Lazy::Product(factors) => parts_size(set, factors.iter(), false),
            // `SetCupValue.size` and its siblings convert the set (`convertAndCache`), whose
            // set enumeration fails past `TLCGlobals.setBound`.
            _ => {
                check_enumerated_bound(set)?;
                Ok(crate::value::converted(set)?.len())
            }
        },
        _ => Ok(elements(set)?.len()),
    }
}

/// `EC.TLC_MODULE_OVERFLOW`.
const OVERFLOW: u32 = 2178;

fn parts_size<'v>(
    set: &Value,
    parts: impl Iterator<Item = &'v Value>,
    is_record: bool,
) -> Evaluated<usize> {
    if crate::eval::is_empty(set)? {
        return Ok(0);
    }
    let mut size: i64 = 1;
    for part in parts {
        size = size.saturating_mul(cardinality(part)? as i64);
        if size > i64::from(i32::MAX) {
            let (text, code) = if is_record {
                (
                    format!(
                        "Overflow when computing the number of elements in:\n{}",
                        format_pretty(set)
                    ),
                    Some(OVERFLOW),
                )
            } else {
                (
                    format!(
                        "Overflow when computing the number of elements in {}",
                        format_pretty(set)
                    ),
                    None,
                )
            };
            return Err(crate::value::EvalError {
                runtime_exception: crate::value::RuntimeException::Runtime,
                is_set_normalization: false,
                is_set_reduction: false,
                is_followed_comparison: false,
                is_named_normalization: false,
                reason: "a set too large to count".into(),
                message: Some(crate::value::TlcMessage {
                    text,
                    code,
                    is_eval_exception: false,
                    inner: None,
                }),
            });
        }
    }
    Ok(size as usize)
}

// Whether a set is empty, as TLC's `isEmpty` finds without enumerating it: an enumeration or an
// interval by itself, a set of functions, records or tuples by its parts.
fn is_empty(set: &Value) -> bool {
    match set {
        Value::Set(elements) => elements.is_empty(),
        Value::Interval(low, high, _) => low > high,
        _ => is_empty_by_argument(set),
    }
}

// `SetOfFcnsValue.size`: one function over an empty domain, none into an empty range, one into a
// range of one element whatever the domain, and otherwise the range's size to the power of the
// domain's, which fails where it overflows an int.
fn function_set_size(set: &Value, domain: &Value, range: &Value) -> Evaluated<usize> {
    if crate::eval::is_empty(domain)? {
        return Ok(1);
    }
    if crate::eval::is_empty(range)? {
        return Ok(0);
    }
    let range = cardinality(range)?;
    if range == 1 {
        return Ok(1);
    }
    let domain = cardinality(domain)?;
    let mut count: i64 = 1;
    for _ in 0..domain {
        count = count.saturating_mul(range as i64);
        if count > i64::from(i32::MAX) {
            return fail_runtime(
                "a function set too large to count",
                format!(
                    "Overflow when computing the number of elements in:\n{}",
                    format_pretty(set)
                ),
            );
        }
    }
    Ok(count as usize)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::Text;

    fn message(result: Evaluated<bool>) -> String {
        result
            .expect_err("a failure")
            .message
            .expect("TLC's message")
            .text
    }

    #[test]
    fn keeps_a_set_operation_lazy_as_tlc_does() {
        let nat = || Value::lazy(Lazy::Nat);
        let set = |ints: &[i32]| Value::set(ints.iter().map(|&int| Value::Int(int)).collect());
        // A reducible operand is filtered by the other, whichever side it is on.
        let unfiltered =
            &mut |_: &Value, _: &Value, _: &crate::eval::Predicate| fail("a lazy filter");
        let cap = intersection(&nat(), &set(&[-1, 1, 2]), unfiltered).expect("an intersection");
        assert!(equals(&cap, &set(&[1, 2])).expect("comparable"));
        // \cup with an enumerable operand and Nat stays lazy, which TLC tests for membership
        // but can't enumerate.
        let cup = union(&set(&[-1]), &nat()).expect("a union");
        assert!(is_member(&Value::Int(-1), &cup).expect("a member"));
        assert!(is_member(&Value::Int(7), &cup).expect("a member"));
        assert_eq!(
            message(elements(&cup).map(|_| true)),
            "Attempted to enumerate S \\cup T when S:\n{-1}\nand T:\nNat\nare not both enumerable"
        );
        let difference = difference(&nat(), &set(&[0]), unfiltered).expect("a difference");
        assert!(is_member(&Value::Int(1), &difference).expect("a member"));
        assert!(!is_member(&Value::Int(0), &difference).expect("a member"));
        assert_eq!(
            message(elements(&difference).map(|_| true)),
            "Attempted to enumerate S \\ T when S:\nNat\nis not enumerable."
        );
    }

    #[test]
    fn preserves_unknown_classes_through_set_representation_shortcuts() {
        let unknown = Value::set(Vec::new()).without_set_provenance();
        let interval = Value::interval(1, 3);
        let cup = union(&unknown, &interval).expect("a union");
        assert_eq!(crate::value::java_set_class(&cup), None);
        assert_eq!(elements(&cup).expect("elements").len(), 3);
        let mut test_filter = |_: &Value, _: &Value, _: &crate::eval::Predicate| fail("a filter");
        let cap = intersection(&unknown, &interval, &mut test_filter).expect("an intersection");
        assert_eq!(crate::value::java_set_class(&cap), None);
        let diff = difference(&interval, &unknown, &mut test_filter).expect("a difference");
        assert_eq!(crate::value::java_set_class(&diff), None);
        let lazy = Value::lazy(Lazy::Subset(Value::set(vec![Value::Int(1)])));
        let cup = union(&unknown, &lazy).expect("a union");
        assert_eq!(crate::value::java_set_class(&cup), None);
    }

    #[test]
    fn tests_a_lazy_union_and_any_as_tlc_does() {
        let union = Value::lazy(Lazy::Union(Value::set(vec![Value::lazy(Lazy::Nat)])));
        assert!(is_member(&Value::Int(1), &union).expect("a member"));
        assert!(!is_member(&Value::Int(-1), &union).expect("a member"));
        assert_eq!(
            message(elements(&union).map(|_| true)),
            "Attempted to enumerate UNION(s), but some element of s is nonenumerable."
        );
        let any = Value::lazy(Lazy::Any);
        assert!(is_member(&Value::Int(1), &any).expect("a member"));
        assert_eq!(
            message(crate::eval::is_empty(&any)),
            "Shouldn't call isEmpty() on value ANY"
        );
    }

    #[test]
    fn compares_an_overridden_set_as_tlc_does() {
        let nat = || Value::lazy(Lazy::Nat);
        let int = Value::lazy(Lazy::Int);
        assert!(equals(&nat(), &nat()).expect("comparable"));
        assert_eq!(compare(&nat(), &int).expect("comparable"), Ordering::Less);
        assert_eq!(
            message(equals(&nat(), &Value::set(vec![Value::Int(1)]))),
            "Attempted to compare overridden value Nat with non-overridden value:\n{1}"
        );
    }

    #[test]
    fn sizes_an_interval_as_tlc_does() {
        assert_eq!(
            cardinality(&Value::interval(0, i32::MAX - 1)).expect("a size"),
            i32::MAX as usize
        );
        assert_eq!(
            message(cardinality(&Value::interval(0, i32::MAX)).map(|_| true)),
            "Size of interval value exceeds the maximum representable size (32bits): 0..2147483647."
        );
    }

    #[test]
    fn counts_a_function_set_as_tlc_does() {
        let set = |domain, range| Value::lazy(Lazy::FunctionSet(domain, range));
        let count = cardinality(&set(Value::interval(1, 3), Value::interval(1, 4)));
        assert_eq!(count.expect("a count"), 64);
        let huge = cardinality(&set(Value::interval(0, 2), Value::interval(1, 2000)));
        assert_eq!(
            huge.expect_err("an overflow")
                .message
                .expect("TLC's message")
                .text,
            "Overflow when computing the number of elements in:\n[0..2 -> 1..2000]"
        );
        // An empty part decides before TLC asks anything of Nat, and a range of one element
        // makes one function whatever the domain.
        let nat = || Value::lazy(Lazy::Nat);
        let count = |domain, range| cardinality(&set(domain, range)).expect("a count");
        assert_eq!(count(nat(), Value::empty_set()), 0);
        assert_eq!(count(Value::empty_set(), nat()), 1);
        assert_eq!(count(nat(), Value::interval(1, 1)), 1);
        let large = Value::lazy(Lazy::Subset(Value::interval(1, 40)));
        assert_eq!(count(large, Value::interval(1, 1)), 1);
        assert!(cardinality(&set(nat(), Value::interval(1, 2))).is_err());
        // A set its parts empty enumerates to nothing, and an empty domain to one function.
        let emptied = set(nat(), Value::empty_set());
        assert!(elements(&emptied).expect("no elements").is_empty());
        let unit = set(emptied, Value::interval(1, 2));
        assert_eq!(elements(&unit).expect("one function").len(), 1);
    }

    #[test]
    fn reports_a_non_integer_in_an_interval_as_tlc_does() {
        let empty = Value::set(Vec::new());
        assert_eq!(
            message(is_member(&empty, &Value::interval(1, 4))),
            "Attempted to check if the value:\n{}\nis in the integer interval 1..4"
        );
        // An empty interval holds nothing, whatever is checked against it.
        assert!(!is_member(&empty, &Value::interval(4, 1)).expect("no failure"));
        let string = Value::Str(Rc::new(Text {
            units: "a".encode_utf16().collect(),
            rank: 0,
        }));
        assert_eq!(
            message(equals(&Value::Int(1), &string)),
            "Attempted to check equality of integer 1 with non-integer:\n\"a\""
        );
        assert_eq!(
            message(compare(&Value::interval(1, 2), &Value::Int(1)).map(|_| true)),
            "Attempted to compare the set {1, 2} with the value:\n1"
        );
    }
}

#[cfg(test)]
mod enumeration_tests {
    use super::*;
    use crate::value::Text;

    fn text(name: &str) -> Rc<Text> {
        Rc::new(Text {
            units: name.encode_utf16().collect(),
            rank: -1,
        })
    }

    fn message(lazy: Lazy) -> Option<String> {
        enumerate(&lazy)
            .err()
            .and_then(|error| error.message)
            .map(|message| message.text)
    }

    #[test]
    fn names_what_tlc_cant_enumerate_in_a_set_it_combines() {
        let int = Value::lazy(Lazy::Int);
        // IOUtils's Serialize: CHOOSE r \in [exitValue : Int, stdout : STRING, ...] : TRUE.
        let records = Lazy::RecordSet(
            vec![
                (text("exitValue"), int.clone()),
                (text("stdout"), Value::lazy(Lazy::Strings)),
            ],
            vec![0, 1],
        );
        assert_eq!(
            message(records).as_deref(),
            Some(
                "Attempted to enumerate a set of the form [l1 : v1, ..., ln : vn],\nbut can't enumerate the value of the `exitValue' field:\nInt"
            )
        );
        let functions = Lazy::FunctionSet(Value::lazy(Lazy::Strings), int.clone());
        assert_eq!(
            message(functions).as_deref(),
            Some(
                "Attempted to enumerate a set of the form [D -> R],but the domain D:\nSTRING\ncannot be enumerated."
            )
        );
        let product = Lazy::Product(vec![Value::interval(1, 2), int]);
        assert_eq!(
            message(product).as_deref(),
            Some(
                "Attempted to enumerate a set of the form s1 \\X s2 ... \\X sn,\nbut can't enumerate s1:\nInt"
            )
        );
    }
}
