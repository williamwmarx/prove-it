//! Fused nodes: closures chosen by the shapes of their operands that do the work of several
//! nodes in one call (native/DESIGN.md 3.1). Each evaluates what the nodes it replaces evaluate,
//! in the same order, and stops where they stop, so it differs from them only in speed.

use std::sync::Arc;

use tla_values::store::{EMPTY_SET, FALSE, KIND_INT, KIND_SET, Outcome, TRUE};
use tla_values::{Bail, Id};

use super::nodes::{assign_bound, evaluate_set};
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
/// counted through without building the interval.
pub(crate) fn quantify_intervals(
    levels: Vec<(u32, (Eval, Eval))>,
    body: Eval,
    is_checked: bool,
    is_forall: bool,
) -> Eval {
    let stop = bool_id(!is_forall);
    let levels = Arc::new(levels);
    eval(move |machine| quantify_level(machine, &levels, 0, &body, is_checked, stop))
}

fn quantify_level(
    machine: &mut Machine<'_>,
    levels: &[(u32, (Eval, Eval))],
    level: usize,
    body: &Eval,
    is_checked: bool,
    stop: Id,
) -> Outcome<Id> {
    let (slot, (low, high)) = &levels[level];
    let Some((low, high)) = interval_bounds(machine, low, high)? else {
        return Ok(1 - stop);
    };
    let is_last = level + 1 == levels.len();
    for value in low..=high {
        machine.locals[*slot as usize] = machine.store.int(i64::from(value))?;
        let result = if is_last {
            let value = body(machine)?;
            if is_checked && value != TRUE && value != FALSE {
                return Err(Bail("expected a boolean"));
            }
            value
        } else {
            quantify_level(machine, levels, level + 1, body, is_checked, stop)?
        };
        if result == stop {
            return Ok(stop);
        }
    }
    Ok(1 - stop)
}

/// `f[e]`, and ApplyVar: `f[i]` with `f` a variable and `i` a bound name, read straight from the
/// registers.
pub(crate) fn apply(function: &Compiled, argument: &Compiled, footprint: Footprint) -> Compiled {
    if let (Shape::Current(variable), Shape::Slot(slot)) = (function.shape, argument.shape) {
        return Compiled {
            shape: Shape::ApplyVar { variable, slot },
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
    let (function, argument) = (function.eval.clone(), argument.eval.clone());
    leaf(
        eval(move |machine| {
            let function = function(machine)?;
            let key = argument(machine)?;
            machine.store.apply(function, key)
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

fn equals_id(machine: &mut Machine<'_>, left: Id, right: Id) -> Outcome<bool> {
    if left == right {
        return Ok(true);
    }
    machine.store.equals(left, right)
}

/// `a = b` and `a # b`, and VarEqConst (`x = c`), the same of `f[i]` (`pc[i] = "cs"`) and of two
/// bound names (`i # j`).
pub(crate) fn equality(left: &Compiled, right: &Compiled, is_equal: bool) -> Eval {
    match (left.shape, right.shape) {
        (Shape::Current(variable), Shape::Constant(constant)) => eval(move |machine| {
            let value = machine.read_current(variable)?;
            Ok(bool_id(equals_id(machine, value, constant)? == is_equal))
        }),
        (Shape::Constant(constant), Shape::Current(variable)) => eval(move |machine| {
            let value = machine.read_current(variable)?;
            Ok(bool_id(equals_id(machine, constant, value)? == is_equal))
        }),
        (Shape::ApplyVar { variable, slot }, Shape::Constant(constant)) => eval(move |machine| {
            let function = machine.read_current(variable)?;
            let key = machine.locals[slot as usize];
            let value = machine.store.apply(function, key)?;
            Ok(bool_id(equals_id(machine, value, constant)? == is_equal))
        }),
        (Shape::Slot(left), Shape::Slot(right)) => eval(move |machine| {
            let (left, right) = (
                machine.locals[left as usize],
                machine.locals[right as usize],
            );
            Ok(bool_id(equals_id(machine, left, right)? == is_equal))
        }),
        _ => {
            let (left, right) = (left.eval.clone(), right.eval.clone());
            eval(move |machine| {
                let left = left(machine)?;
                let right = right(machine)?;
                Ok(bool_id(equals_id(machine, left, right)? == is_equal))
            })
        }
    }
}

/// MemberConst: `i \in S` of a bound name and a constant set the engine builds.
pub(crate) fn member_const(
    element: &Compiled,
    set: &Compiled,
    machine_kind: u8,
    is_in: bool,
) -> Option<Eval> {
    let (Shape::Slot(slot), Shape::Constant(constant)) = (element.shape, set.shape) else {
        return None;
    };
    if machine_kind != KIND_SET || set.member.is_some() || set.infinite.is_some() {
        return None;
    }
    Some(eval(move |machine| {
        let element = machine.locals[slot as usize];
        Ok(bool_id(
            machine.store.is_member(element, constant)? == is_in,
        ))
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
            if (filter.predicate)(machine)? == TRUE {
                count += 1;
            }
        }
        machine.store.int(count)
    })
}
