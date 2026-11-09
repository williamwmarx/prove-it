//! Fused nodes: closures chosen by the shapes of their operands that do the work of several
//! nodes in one call (native/DESIGN.md 3.1). Each evaluates what the nodes it replaces evaluate,
//! in the same order, and stops where they stop, so it differs from them only in speed.

use std::sync::Arc;

use tla_values::store::{EMPTY_SET, KIND_INT, Outcome, is_tested_set_kind};
use tla_values::{Bail, Id};

use super::lazy_function;
use super::nodes::{assign_bound, evaluate_set};
use super::predicate::{self, Predicate, Test};
use super::{Compiled, Filter, Shape, bool_id, eval, leaf};
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
    if high < low {
        return Ok(None);
    }
    if i64::from(high) - i64::from(low) > MAXIMUM_INTERVAL {
        return Err(Bail("an interval too large to build"));
    }
    Ok(Some((low, high)))
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
    levels: Vec<(u32, (Eval, Eval))>,
    body: Predicate,
    is_forall: bool,
) -> Eval {
    let levels = Arc::new(levels);
    let body = body.build();
    eval(move |machine| quantify_level(machine, &levels, 0, &body, is_forall).map(bool_id))
}

fn quantify_level(
    machine: &mut Machine<'_>,
    levels: &[(u32, (Eval, Eval))],
    level: usize,
    body: &Test,
    is_forall: bool,
) -> Outcome<bool> {
    let (slot, (low, high)) = &levels[level];
    let Some((low, high)) = interval_bounds(machine, low, high)? else {
        return Ok(is_forall);
    };
    let is_last = level + 1 == levels.len();
    for value in low..=high {
        machine.locals[*slot as usize] = machine.store.int(i64::from(value))?;
        let holds = if is_last {
            body(machine)?
        } else {
            quantify_level(machine, levels, level + 1, body, is_forall)?
        };
        if holds != is_forall {
            return Ok(!is_forall);
        }
    }
    Ok(is_forall)
}

/// `f[e]`, and ApplyVar: `f[i]` with `f` a variable and `i` a bound name, read straight from the
/// registers.
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
pub(crate) fn except_var_at(variable: u32, key: Eval, value: Eval) -> Eval {
    eval(move |machine| {
        let function = machine.read_current(variable)?;
        let key = key(machine)?;
        let value = value(machine)?;
        machine.store.except(function, key, value)
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

/// CardinalityFilter: `Cardinality({x \in S : P})`, counted without building the filtered set.
pub(crate) fn cardinality_filter(filter: Arc<Filter>) -> Eval {
    eval(move |machine| {
        let id = evaluate_set(machine, &filter.set, "filtered a non-set")?;
        let mut count = 0i64;
        for index in 0..machine.store.size_of(id) {
            let element = machine.store.element_at(id, index);
            assign_bound(machine, &filter.slots, filter.tuple, element)?;
            if (filter.predicate)(machine)? {
                count += 1;
            }
        }
        machine.store.int(count)
    })
}
