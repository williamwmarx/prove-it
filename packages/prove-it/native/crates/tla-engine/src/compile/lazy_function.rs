//! The functions TLC keeps lazy (`FcnLambdaValue`): a function construction over a domain TLC
//! can't enumerate, such as `[i \in Nat |-> e]`, which TLC builds only as its body, its domain and
//! the EXCEPTs applied to it since. The store holds one as an id of its own kind, which numbers it
//! among those the machine keeps; applying it checks the key against the EXCEPTs, latest first,
//! then against the domain, and evaluates the body with the key bound. The store can't compare,
//! fingerprint or print one, as TLC can't without enumerating its domain, so the engine stops
//! there.

use std::sync::Arc;

use tla_values::store::{KIND_LAZY_FUNCTION, KIND_TUPLE, Outcome};
use tla_values::{Bail, Id};

use super::lazy::Lazy;
use super::nodes::assign_converted;
use crate::machine::{Eval, Machine};

/// What a construction TLC keeps lazy compiles to: each bound's slots, and whether it is a tuple
/// pattern, the body, and what the body reads besides them, which the function captures.
pub(crate) struct LambdaDefinition {
    pub(crate) levels: Vec<(Vec<u32>, bool)>,
    pub(crate) body: Eval,
    pub(crate) captured: Vec<u32>,
    pub(crate) vars: Vec<u32>,
    pub(crate) primes: Vec<u32>,
}

/// A function TLC keeps lazy, as the machine keeps it.
pub(crate) struct Lambda {
    definition: Arc<LambdaDefinition>,
    /// Each bound's set, as TLC evaluated it when it built the function.
    domains: Arc<Vec<Lazy>>,
    /// The values of what the body reads besides its bounds: the captured slots', then the
    /// variables' and the primed variables'.
    captured: Arc<Vec<Id>>,
    state: Arc<Vec<Id>>,
    /// `[f EXCEPT ![k] = v]`'s keys and values, oldest first.
    excepts: Vec<(Id, Id)>,
}

const OTHER_STATE: Bail = Bail("unsupported: a function TLC keeps lazy applied in another state");
/// DOMAIN of a function TLC keeps lazy, which TLC can't build: the engine stops.
pub(crate) const DOMAIN: Bail = Bail("unsupported: DOMAIN of a function TLC keeps lazy");

/// Whether a set TLC evaluated is one it can't enumerate (it isn't `Reducible`), which keeps a
/// function over it lazy.
pub(crate) fn is_lazy_domain(domain: &Lazy) -> bool {
    domain.is_infinite()
}

/// The function, built by the machine.
pub(crate) fn build(
    machine: &mut Machine<'_>,
    definition: &Arc<LambdaDefinition>,
    domains: Vec<Lazy>,
) -> Outcome<Id> {
    let captured = definition
        .captured
        .iter()
        .map(|&slot| machine.locals[slot as usize])
        .collect();
    let state = definition
        .vars
        .iter()
        .map(|&variable| machine.cur[variable as usize])
        .chain(
            definition
                .primes
                .iter()
                .map(|&variable| machine.next[variable as usize]),
        )
        .collect();
    let function = Lambda {
        definition: Arc::clone(definition),
        domains: Arc::new(domains),
        captured: Arc::new(captured),
        state: Arc::new(state),
        excepts: Vec::new(),
    };
    Ok(add(machine, function))
}

fn add(machine: &mut Machine<'_>, function: Lambda) -> Id {
    let index = machine.lazy_functions.len() as u32;
    machine.lazy_functions.push(function);
    machine.store.lazy_function(index)
}

/// `f[k]`, of any function.
#[inline(always)]
pub(crate) fn apply(machine: &mut Machine<'_>, function: Id, key: Id) -> Outcome<Id> {
    if machine.store.kind_of(function) == KIND_LAZY_FUNCTION {
        return apply_lazy(machine, function, key);
    }
    machine.store.apply(function, key)
}

/// `[f EXCEPT ![k] = v]`, of any function.
pub(crate) fn except(machine: &mut Machine<'_>, function: Id, key: Id, value: Id) -> Outcome<Id> {
    if machine.store.kind_of(function) != KIND_LAZY_FUNCTION {
        return machine.store.except(function, key, value);
    }
    // TLC reads the function at the key first (`FcnLambdaValue.select`): outside its domain the
    // EXCEPT changes nothing, but TLC warns that it was applied to non-existing fields (`Tool`'s
    // OPCODE_exc), which the engine leaves to the reference interpreter as the store does for
    // any other function. Inside it the function's value there is evaluated, and may fail.
    if !is_in_domain(machine, function, key)? {
        return Err(Bail("EXCEPT outside the domain"));
    }
    apply_lazy(machine, function, key)?;
    let lazy = &machine.lazy_functions[machine.store.lazy_index_of(function) as usize];
    let mut excepts = lazy.excepts.clone();
    excepts.push((key, value));
    let function = Lambda {
        definition: Arc::clone(&lazy.definition),
        domains: Arc::clone(&lazy.domains),
        captured: Arc::clone(&lazy.captured),
        state: Arc::clone(&lazy.state),
        excepts,
    };
    Ok(add(machine, function))
}

/// Whether a value is in DOMAIN f of a function TLC keeps lazy: its bound's set, or the tuples
/// of its bounds' sets (`FcnLambdaValue.getDomain`).
pub(crate) fn is_in_domain(machine: &mut Machine<'_>, function: Id, element: Id) -> Outcome<bool> {
    let index = machine.store.lazy_index_of(function) as usize;
    in_built_context(machine, index, |machine, _, domains| {
        if let [domain] = domains {
            return domain.contains(machine, element);
        }
        // TLC fails asking a set of tuples for a value that isn't a tuple.
        if machine.store.kind_of(element) != KIND_TUPLE {
            return Err(DOMAIN);
        }
        if machine.store.size_of(element) as usize != domains.len() {
            return Ok(false);
        }
        for (position, domain) in domains.iter().enumerate() {
            let component = machine.store.get_range_value(element, position as u32);
            if !domain.contains(machine, component)? {
                return Ok(false);
            }
        }
        Ok(true)
    })
}

/// Whether a value is a function TLC keeps lazy.
pub(crate) fn is_lazy(machine: &Machine<'_>, value: Id) -> bool {
    machine.store.kind_of(value) == KIND_LAZY_FUNCTION
}

// `FcnLambdaValue.apply`: an EXCEPT's value where one names the key, the latest first, and
// otherwise the body's, with the key bound, where the key is in the domain.
#[inline(never)]
fn apply_lazy(machine: &mut Machine<'_>, function: Id, key: Id) -> Outcome<Id> {
    let index = machine.store.lazy_index_of(function) as usize;
    for at in (0..machine.lazy_functions[index].excepts.len()).rev() {
        let (except_key, value) = machine.lazy_functions[index].excepts[at];
        if machine.store.equals(except_key, key)? {
            return Ok(value);
        }
    }
    in_built_context(machine, index, |machine, definition, domains| {
        // One bound takes the key; several take a tuple of as many elements, one for each.
        let elements: Vec<Id> = match &definition.levels[..] {
            [_] => vec![key],
            levels => {
                let store = &machine.store;
                if store.kind_of(key) != KIND_TUPLE || store.size_of(key) as usize != levels.len() {
                    return Err(Bail("applied a function outside its domain"));
                }
                (0..levels.len() as u32)
                    .map(|position| store.get_range_value(key, position))
                    .collect()
            }
        };
        for (domain, &element) in domains.iter().zip(&elements) {
            if !domain.contains(machine, element)? {
                return Err(Bail("applied a function outside its domain"));
            }
        }
        for ((slots, tuple), &element) in definition.levels.iter().zip(&elements) {
            assign_converted(machine, slots, *tuple, element)?;
        }
        (definition.body)(machine)
    })
}

// Runs `run` in the context TLC built the function in, which its domains and body read: its state,
// and the captured slots' values. The slots it sets, its bounds' among them, are restored after.
fn in_built_context<T>(
    machine: &mut Machine<'_>,
    index: usize,
    run: impl FnOnce(&mut Machine<'_>, &LambdaDefinition, &[Lazy]) -> Outcome<T>,
) -> Outcome<T> {
    let lazy = &machine.lazy_functions[index];
    let (definition, domains, captured, state) = (
        Arc::clone(&lazy.definition),
        Arc::clone(&lazy.domains),
        Arc::clone(&lazy.captured),
        Arc::clone(&lazy.state),
    );
    let is_same_state = definition
        .vars
        .iter()
        .map(|&variable| machine.cur[variable as usize])
        .chain(
            definition
                .primes
                .iter()
                .map(|&variable| machine.next[variable as usize]),
        )
        .eq(state.iter().copied());
    if !is_same_state {
        return Err(OTHER_STATE);
    }
    let slots: Vec<u32> = definition
        .captured
        .iter()
        .copied()
        .chain(
            definition
                .levels
                .iter()
                .flat_map(|(slots, _)| slots.iter().copied()),
        )
        .collect();
    let saved: Vec<Id> = slots
        .iter()
        .map(|&slot| machine.locals[slot as usize])
        .collect();
    for (&slot, &value) in definition.captured.iter().zip(captured.iter()) {
        machine.locals[slot as usize] = value;
    }
    let result = run(machine, &definition, &domains);
    for (&slot, &value) in slots.iter().zip(&saved) {
        machine.locals[slot as usize] = value;
    }
    result
}
