//! Fused nodes: closures chosen by the shapes of their operands that do the work of several
//! nodes in one call (native/DESIGN.md 3.1). Each evaluates what the nodes it replaces evaluate,
//! in the same order, and stops where they stop, so it differs from them only in speed.

use std::sync::Arc;

use tla_values::store::{EMPTY_SET, KIND_INT, Outcome, is_tested_set_kind};
use tla_values::{Bail, Id, check_set_insertion};

use super::lazy_function;
use super::nodes::assign_bound;
use super::predicate::{self, Predicate, Test};
use super::{Compiled, Filter, Interval, Shape, bool_id, eval, leaf};
use crate::footprint::Footprint;
use crate::machine::{Eval, Machine};

const MAXIMUM_INTERVAL: i64 = 10_000_000;

fn expect_int(machine: &Machine<'_>, id: Id) -> Outcome<i32> {
    if machine.store.kind_of(id) == KIND_INT {
        Ok(machine.store.int_of(id))
    } else {
        Err(Bail("expected an integer"))
    }
}

/// The bounds of `a..b`, as the interval's own node checks them, or None for an empty one.
pub(crate) fn interval_bounds(
    machine: &mut Machine<'_>,
    low: &Eval,
    high: &Eval,
) -> Outcome<Option<(i32, i32)>> {
    let low = low(machine)?;
    let high = high(machine)?;
    let low = expect_int(machine, low)?;
    let high = expect_int(machine, high)?;
    checked_bounds(low, high)
}

fn checked_bounds(low: i32, high: i32) -> Outcome<Option<(i32, i32)>> {
    if high < low {
        return Ok(None);
    }
    if i64::from(high) - i64::from(low) > MAXIMUM_INTERVAL {
        return Err(Bail("an interval too large to build"));
    }
    Ok(Some((low, high)))
}

/// `interval_bounds` of an interval, read in place where the compiler holds its bounds.
fn bounds_of(machine: &mut Machine<'_>, interval: &Interval) -> Outcome<Option<(i32, i32)>> {
    match interval.known {
        Some((low, high)) => checked_bounds(low, high),
        None => interval_bounds(machine, &interval.low, &interval.high),
    }
}

/// The number of elements of `a..b` (`IntervalValue.size`), its bounds checked as the interval's
/// own node checks them, or None where it has more than 2^31 - 1, where TLC fails.
pub(crate) fn interval_size(
    machine: &mut Machine<'_>,
    low: &Eval,
    high: &Eval,
) -> Outcome<Option<i64>> {
    let low = low(machine)?;
    let high = high(machine)?;
    let low = i64::from(expect_int(machine, low)?);
    let high = i64::from(expect_int(machine, high)?);
    let size = (high - low + 1).max(0);
    Ok((size <= i64::from(i32::MAX)).then_some(size))
}

/// `a..b`, built.
pub(crate) fn interval(machine: &mut Machine<'_>, low: &Eval, high: &Eval) -> Outcome<Id> {
    let Some((low, high)) = interval_bounds(machine, low, high)? else {
        return Ok(EMPTY_SET);
    };
    let mut elements = Vec::with_capacity((i64::from(high) - i64::from(low) + 1) as usize);
    for value in low..=high {
        elements.push(machine.store.int(i64::from(value))?);
    }
    Ok(machine.store.set_of_sorted(&elements))
}

/// ForallInterval and ExistsInterval: `\A x \in a..b : P`, a name over an interval at each level,
/// counted through without building the interval, its body's predicate walked in the loop.
pub(crate) fn quantify_intervals(
    levels: Vec<(u32, Interval, bool)>,
    body: Predicate,
    is_forall: bool,
) -> Eval {
    let levels = Arc::new(levels);
    let body = body.build();
    eval(move |machine| quantify_levels(machine, &levels, &body, is_forall).map(bool_id))
}

// Each level's bounds once, in the order written (`Tool.contexts`), a level that shares the set of
// the one before as `a, b \in 1..n` does taking its bounds, and then the bindings with the first
// name varying fastest (`ContextEnumerator`), until one decides the quantifier.
fn quantify_levels(
    machine: &mut Machine<'_>,
    levels: &[(u32, Interval, bool)],
    body: &Test,
    is_forall: bool,
) -> Outcome<bool> {
    let mut inline = [Counter::default(); INLINE_LEVELS];
    let mut spilled = Vec::new();
    let counters = if levels.len() <= INLINE_LEVELS {
        &mut inline[..levels.len()]
    } else {
        spilled.resize(levels.len(), Counter::default());
        &mut spilled[..]
    };
    let mut is_empty = false;
    let mut last = None;
    for ((_, interval, is_shared), counter) in levels.iter().zip(counters.iter_mut()) {
        let level = match last {
            Some(level) if *is_shared => level,
            _ => bounds_of(machine, interval)?,
        };
        last = Some(level);
        match level {
            Some((low, high)) => {
                *counter = Counter {
                    low,
                    high,
                    value: low,
                }
            }
            None => is_empty = true,
        }
    }
    if is_empty {
        return Ok(is_forall);
    }
    loop {
        for ((slot, ..), counter) in levels.iter().zip(counters.iter()) {
            machine.locals[*slot as usize] = machine.store.int(i64::from(counter.value))?;
        }
        if body(machine)? != is_forall {
            return Ok(!is_forall);
        }
        let mut level = 0;
        loop {
            let Some(counter) = counters.get_mut(level) else {
                return Ok(is_forall);
            };
            if counter.value < counter.high {
                counter.value += 1;
                break;
            }
            counter.value = counter.low;
            level += 1;
        }
    }
}

const INLINE_LEVELS: usize = 4;

/// A level of a quantifier over intervals: its bounds and the value it is at.
#[derive(Clone, Copy, Default)]
struct Counter {
    low: i32,
    high: i32,
    value: i32,
}

/// `f[e]`, and ApplyVar: `f[i]` with `f` a variable and `i` a bound name, read straight from the
/// registers, or `f[c]` with `c` a constant.
pub(crate) fn apply(function: &Compiled, argument: &Compiled, footprint: Footprint) -> Compiled {
    if let (Shape::Current(variable), Some((slot, is_int))) =
        (function.shape, argument.shape.slot())
    {
        return Compiled {
            shape: Shape::ApplyVar {
                variable,
                slot,
                is_int,
            },
            ..leaf(
                eval(move |machine| {
                    let function = machine.read_current(variable)?;
                    let key = machine.locals[slot as usize];
                    machine.store.apply(function, key)
                }),
                footprint,
            )
        };
    }
    if let (Shape::ApplyVar { variable, slot, .. }, Some((second, _))) =
        (function.shape, argument.shape.slot())
    {
        return Compiled {
            shape: Shape::ApplyVar2 {
                variable,
                slot,
                second,
            },
            ..leaf(
                eval(move |machine| predicate::apply_var2(machine, variable, slot, second)),
                footprint,
            )
        };
    }
    if let (Shape::Current(variable), Shape::Constant(key)) = (function.shape, argument.shape) {
        return leaf(
            eval(move |machine| {
                let function = machine.read_current(variable)?;
                machine.store.apply(function, key)
            }),
            footprint,
        );
    }
    if let (Some((slot, _)), Shape::Constant(key)) = (function.shape.slot(), argument.shape) {
        return leaf(
            eval(move |machine| {
                let function = machine.locals[slot as usize];
                lazy_function::apply(machine, function, key)
            }),
            footprint,
        );
    }
    if let Some((slot, _)) = function.shape.slot() {
        let argument = argument.eval.clone();
        return leaf(
            eval(move |machine| {
                let function = machine.locals[slot as usize];
                let key = argument(machine)?;
                lazy_function::apply(machine, function, key)
            }),
            footprint,
        );
    }
    let (function, argument) = (function.eval.clone(), argument.eval.clone());
    leaf(
        eval(move |machine| {
            let function = function(machine)?;
            let key = argument(machine)?;
            lazy_function::apply(machine, function, key)
        }),
        footprint,
    )
}

/// ExceptVarAt: `[x EXCEPT ![k] = v]` of a variable x.
pub(crate) fn except_var_at(
    variable: u32,
    key: Eval,
    value: Eval,
    warning: Option<tla_ir::NodeId>,
) -> Eval {
    eval(move |machine| {
        let function = machine.read_current(variable)?;
        let key = key(machine)?;
        if super::nodes::select_except(machine, function, key)?.is_none() {
            super::nodes::except_warning(machine, warning)?;
            return Ok(function);
        }
        let value = value(machine)?;
        lazy_function::except(machine, function, key, value)
    })
}

/// MemberConst: `i \in S` of a bound name and a set the engine builds, such as a constant one,
/// the element read from its slot and the set tested in place.
pub(crate) fn member_const(element: &Compiled, set: &Compiled, is_in: bool) -> Option<Eval> {
    let (slot, _) = element.shape.slot()?;
    if set.member.is_some() || set.infinite.is_some() {
        return None;
    }
    let set = set.eval.clone();
    Some(eval(move |machine| {
        let element = machine.locals[slot as usize];
        let set = set(machine)?;
        if !is_tested_set_kind(machine.store.kind_of(set)) {
            return Err(Bail("membership in a non-set"));
        }
        Ok(bool_id(machine.store.is_member(element, set)? == is_in))
    }))
}

/// CardinalityFilter: `Cardinality({x \in S : P})`, counted directly for a materialized input.
pub(crate) fn cardinality_filter(filter: Arc<Filter>) -> Eval {
    eval(move |machine| {
        let (input, elements) = filter.elements(machine)?;
        let mut kept = input.is_none().then(Vec::new);
        let mut count = 0usize;
        for element in elements {
            assign_bound(machine, &filter.slots, filter.tuple, element)?;
            if (filter.predicate)(machine)? {
                check_set_insertion(count)?;
                count += 1;
                if let Some(kept) = &mut kept {
                    kept.push(element);
                }
            }
        }
        let size = match kept {
            Some(kept) => {
                let set = machine.store.set_of(&kept)?;
                machine.store.size_of(set) as i64
            }
            None => count as i64,
        };
        machine.store.int(size)
    })
}
