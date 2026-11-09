//! Fused predicates: `=`, `#`, `~`, `/\`, `\/` and `=>` over operands the compiler can read
//! without calling them (a bound name, a constant, a variable, `f[i]`) are kept as a tree, so a
//! parent can take its operands' trees in, and the whole tree is built into closures chosen by
//! its shape, each doing the work of several nodes: `i # j => P` of two names bound over
//! intervals compares their ids, `~(A /\ B)` is one closure, and `f[i] = c` applies and compares
//! in place. A quantifier calls its body's closure in its own loop. Each closure evaluates what
//! the nodes it replaces evaluate, in the same order and with the same short circuits, and checks
//! a boolean where `compileBoolean` does.

use tla_values::store::{FALSE, KIND_INT, KIND_SET, KIND_STRING, KIND_TUPLE, Outcome, TRUE};
use tla_values::{Bail, Id};

use super::{Compiled, Shape, bool_id, eval};
use crate::machine::{Eval, Machine};

/// A compiled boolean, as a closure that gives a `bool`. Each has one owner, so a call needn't
/// find its data in a shared allocation.
pub(crate) type Test = Box<dyn Fn(&mut Machine<'_>) -> Outcome<bool> + Send + Sync>;

fn test(run: impl Fn(&mut Machine<'_>) -> Outcome<bool> + Send + Sync + 'static) -> Test {
    Box::new(run)
}

/// An operand read in place.
#[derive(Clone)]
pub(crate) enum Leaf {
    Slot(u32),
    /// A bound name whose values are integers.
    IntSlot(u32),
    Constant(Id),
    Current(u32),
    ApplyVar {
        variable: u32,
        slot: u32,
        is_int: bool,
    },
    ApplyVar2 {
        variable: u32,
        slot: u32,
        second: u32,
    },
    Eval(Eval),
}

#[derive(Clone)]
pub(crate) enum Predicate {
    Equal {
        left: Leaf,
        right: Leaf,
        is_equal: bool,
    },
    /// `e \in S` and `e \notin S` of a set the engine builds.
    Member {
        element: Leaf,
        set: Leaf,
        is_in: bool,
    },
    Not(Box<Predicate>),
    And(Vec<Predicate>),
    Or(Vec<Predicate>),
    Implies(Box<Predicate>, Box<Predicate>),
    /// Any other boolean, checked to be one unless it always is.
    Eval {
        eval: Eval,
        is_checked: bool,
    },
}

/// `f[k]`, with a tuple and an integer read in place, as the store's `apply` reads them.
#[inline(always)]
pub(crate) fn apply(machine: &mut Machine<'_>, function: Id, key: Id) -> Outcome<Id> {
    let store = &machine.store;
    if store.kind_of(function) == KIND_TUPLE && store.kind_of(key) == KIND_INT {
        return apply_tuple(machine, function, key);
    }
    machine.store.apply(function, key)
}

/// `f[i][j]` of a variable and two bound names.
#[inline(always)]
pub(crate) fn apply_var2(
    machine: &mut Machine<'_>,
    variable: u32,
    slot: u32,
    second: u32,
) -> Outcome<Id> {
    let function = machine.read_current(variable)?;
    let inner = apply(machine, function, machine.locals[slot as usize])?;
    apply(machine, inner, machine.locals[second as usize])
}

// A tuple applied to an integer.
#[inline(always)]
fn apply_tuple(machine: &Machine<'_>, tuple: Id, key: Id) -> Outcome<Id> {
    let position = i64::from(machine.store.int_of(key)) - 1;
    usize::try_from(position)
        .ok()
        .and_then(|position| machine.store.tuple_elements(tuple).get(position).copied())
        .ok_or(Bail("applied a function outside its domain"))
}

/// TLC's equality, with two scalars of one kind told apart by their ids, as the store tells
/// them apart.
#[inline(always)]
pub(crate) fn equals(machine: &mut Machine<'_>, left: Id, right: Id) -> Outcome<bool> {
    if left == right {
        return Ok(true);
    }
    let kind = machine.store.kind_of(left);
    if kind <= KIND_STRING && kind == machine.store.kind_of(right) {
        return Ok(false);
    }
    machine.store.equals(left, right)
}

impl Leaf {
    pub(crate) fn of(compiled: &Compiled) -> Leaf {
        match compiled.shape {
            Shape::Slot(slot) => Leaf::Slot(slot),
            Shape::IntSlot(slot) => Leaf::IntSlot(slot),
            Shape::Constant(id) => Leaf::Constant(id),
            Shape::Current(variable) => Leaf::Current(variable),
            Shape::ApplyVar {
                variable,
                slot,
                is_int,
            } => Leaf::ApplyVar {
                variable,
                slot,
                is_int,
            },
            Shape::ApplyVar2 {
                variable,
                slot,
                second,
            } => Leaf::ApplyVar2 {
                variable,
                slot,
                second,
            },
            Shape::Other => Leaf::Eval(compiled.eval.clone()),
        }
    }

    #[inline(always)]
    fn read(&self, machine: &mut Machine<'_>) -> Outcome<Id> {
        match self {
            Leaf::Slot(slot) | Leaf::IntSlot(slot) => Ok(machine.locals[*slot as usize]),
            Leaf::Constant(id) => Ok(*id),
            Leaf::Current(variable) => machine.read_current(*variable),
            Leaf::ApplyVar { variable, slot, .. } => {
                let function = machine.read_current(*variable)?;
                let key = machine.locals[*slot as usize];
                apply(machine, function, key)
            }
            Leaf::ApplyVar2 {
                variable,
                slot,
                second,
            } => apply_var2(machine, *variable, *slot, *second),
            Leaf::Eval(eval) => eval(machine),
        }
    }
}

impl Predicate {
    /// The predicate of a compiled boolean: its own tree, or a call of it.
    pub(crate) fn of(compiled: &Compiled) -> Predicate {
        match &compiled.predicate {
            Some(predicate) => (**predicate).clone(),
            None => Predicate::Eval {
                eval: compiled.eval.clone(),
                is_checked: !compiled.is_boolean,
            },
        }
    }

    /// The closures that evaluate the tree.
    pub(crate) fn build(&self) -> Test {
        match self {
            Predicate::Equal {
                left,
                right,
                is_equal,
            } => build_equal(left, right, *is_equal),
            Predicate::Member {
                element,
                set,
                is_in,
            } => {
                let (element, set, is_in) = (element.clone(), set.clone(), *is_in);
                test(move |machine| {
                    let element = element.read(machine)?;
                    let set = set.read(machine)?;
                    if machine.store.kind_of(set) != KIND_SET {
                        return Err(Bail("membership in a non-set"));
                    }
                    Ok(machine.store.is_member(element, set)? == is_in)
                })
            }
            // NotAnd: ~(A /\ B) in one closure.
            Predicate::Not(operand) => match &**operand {
                Predicate::And(operands) => {
                    let operands = build_all(operands);
                    test(move |machine| {
                        for operand in operands.iter() {
                            if !operand(machine)? {
                                return Ok(true);
                            }
                        }
                        Ok(false)
                    })
                }
                operand => {
                    let operand = operand.build();
                    test(move |machine| Ok(!operand(machine)?))
                }
            },
            Predicate::And(operands) => {
                let operands = build_all(operands);
                test(move |machine| {
                    for operand in operands.iter() {
                        if !operand(machine)? {
                            return Ok(false);
                        }
                    }
                    Ok(true)
                })
            }
            Predicate::Or(operands) => {
                let operands = build_all(operands);
                test(move |machine| {
                    for operand in operands.iter() {
                        if operand(machine)? {
                            return Ok(true);
                        }
                    }
                    Ok(false)
                })
            }
            Predicate::Implies(left, right) => {
                let consequent = right.build();
                // ImpliesDiffer: i # j => P of two names bound over intervals, whose ids are
                // equal only when their integers are.
                if let Predicate::Equal {
                    left: Leaf::IntSlot(first),
                    right: Leaf::IntSlot(second),
                    is_equal: false,
                } = &**left
                {
                    let (first, second) = (*first as usize, *second as usize);
                    return test(move |machine| {
                        if machine.locals[first] == machine.locals[second] {
                            return Ok(true);
                        }
                        consequent(machine)
                    });
                }
                let antecedent = left.build();
                test(move |machine| Ok(!antecedent(machine)? || consequent(machine)?))
            }
            Predicate::Eval { eval, is_checked } => {
                let eval = eval.clone();
                if *is_checked {
                    test(move |machine| match eval(machine)? {
                        TRUE => Ok(true),
                        FALSE => Ok(false),
                        _ => Err(Bail("expected a boolean")),
                    })
                } else {
                    test(move |machine| Ok(eval(machine)? == TRUE))
                }
            }
        }
    }
}

fn build_all(predicates: &[Predicate]) -> Box<[Test]> {
    predicates.iter().map(Predicate::build).collect()
}

fn build_equal(left: &Leaf, right: &Leaf, is_equal: bool) -> Test {
    match (left, right) {
        // Two names bound over intervals hold integers, equal when their ids are.
        (Leaf::IntSlot(first), Leaf::IntSlot(second)) => {
            let (first, second) = (*first as usize, *second as usize);
            test(move |machine| Ok((machine.locals[first] == machine.locals[second]) == is_equal))
        }
        // ApplyVarEqConst: f[i] = c, with i a name bound over an interval.
        (
            Leaf::ApplyVar {
                variable,
                slot,
                is_int: true,
            },
            Leaf::Constant(constant),
        ) => {
            let (variable, slot, constant) = (*variable, *slot as usize, *constant);
            test(move |machine| {
                let function = machine.read_current(variable)?;
                let key = machine.locals[slot];
                let value = if machine.store.kind_of(function) == KIND_TUPLE {
                    apply_tuple(machine, function, key)?
                } else {
                    machine.store.apply(function, key)?
                };
                Ok(equals(machine, value, constant)? == is_equal)
            })
        }
        // f[k] = c and f[k] = j, with k and j bound names.
        (
            Leaf::ApplyVar { variable, slot, .. },
            Leaf::Constant(_) | Leaf::Slot(_) | Leaf::IntSlot(_),
        ) => {
            let (variable, slot, right) = (*variable, *slot as usize, right.clone());
            test(move |machine| {
                let function = machine.read_current(variable)?;
                let key = machine.locals[slot];
                let value = apply(machine, function, key)?;
                let other = match right {
                    Leaf::Constant(constant) => constant,
                    Leaf::Slot(other) | Leaf::IntSlot(other) => machine.locals[other as usize],
                    _ => unreachable!("a constant or a bound name"),
                };
                Ok(equals(machine, value, other)? == is_equal)
            })
        }
        // VarEqConst: x = c.
        (Leaf::Current(variable), Leaf::Constant(constant)) => {
            let (variable, constant) = (*variable, *constant);
            test(move |machine| {
                let value = machine.read_current(variable)?;
                Ok(equals(machine, value, constant)? == is_equal)
            })
        }
        _ => {
            let (left, right) = (left.clone(), right.clone());
            test(move |machine| {
                let left = left.read(machine)?;
                let right = right.read(machine)?;
                Ok(equals(machine, left, right)? == is_equal)
            })
        }
    }
}

/// The closure of a compiled boolean whose value is the predicate's.
pub(crate) fn evaluate(predicate: &Predicate) -> Eval {
    let test = predicate.build();
    eval(move |machine| test(machine).map(bool_id))
}
