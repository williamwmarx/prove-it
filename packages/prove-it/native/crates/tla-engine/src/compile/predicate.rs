//! Fused predicates: `=`, `#`, `~`, `/\`, `\/` and `=>` over operands the compiler can read
//! without calling them (a bound name, a constant, a variable, `f[i]`) are kept as a tree, so a
//! parent can take its operands' trees in, and the whole tree is built into closures chosen by
//! its shape, each doing the work of several nodes: `i # j => P` of two names bound over
//! intervals compares their ids, `~(A /\ B)` is one closure, and `f[i] = c` applies and compares
//! in place. A quantifier calls its body's closure in its own loop. Each closure evaluates what
//! the nodes it replaces evaluate, in the same order and with the same short circuits, and checks
//! a boolean where `compileBoolean` does.

use std::sync::Arc;
use std::sync::atomic::{AtomicU32, Ordering};

use tla_values::store::{FALSE, KIND_STRING, Outcome, TRUE, is_tested_set_kind};
use tla_values::{Bail, Id};

use super::nodes::field_of;
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
    /// `r.f` of a bound name, with the position the field was last found at.
    Field {
        slot: u32,
        key: Id,
        hint: Arc<AtomicU32>,
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

/// `f[i][j]` of a variable and two bound names.
#[inline(always)]
pub(crate) fn apply_var2(
    machine: &mut Machine<'_>,
    variable: u32,
    slot: u32,
    second: u32,
) -> Outcome<Id> {
    let function = machine.read_current(variable)?;
    let inner = machine
        .store
        .apply(function, machine.locals[slot as usize])?;
    machine.store.apply(inner, machine.locals[second as usize])
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
            Shape::Field { slot, key } => Leaf::Field {
                slot,
                key,
                hint: Arc::new(AtomicU32::new(0)),
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
                machine.store.apply(function, key)
            }
            Leaf::ApplyVar2 {
                variable,
                slot,
                second,
            } => apply_var2(machine, *variable, *slot, *second),
            Leaf::Field { slot, key, hint } => {
                let record = machine.locals[*slot as usize];
                field_of(machine, record, *key, hint)
            }
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
                    if !is_tested_set_kind(machine.store.kind_of(set)) {
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
                let value = machine.store.apply(function, key)?;
                Ok(machine.store.equals(value, constant)? == is_equal)
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
                let value = machine.store.apply(function, key)?;
                let other = match right {
                    Leaf::Constant(constant) => constant,
                    Leaf::Slot(other) | Leaf::IntSlot(other) => machine.locals[other as usize],
                    _ => unreachable!("a constant or a bound name"),
                };
                Ok(machine.store.equals(value, other)? == is_equal)
            })
        }
        // FieldEqConst: r.f = c of a bound name r. Distinct ids of one kind of scalar are unequal
        // values, as `equals` finds them.
        (Leaf::Field { slot, key, hint }, Leaf::Constant(constant)) => {
            let (slot, key, hint, constant) = (*slot as usize, *key, hint.clone(), *constant);
            test(move |machine| {
                let record = machine.locals[slot];
                let value = field_of(machine, record, key, &hint)?;
                if is_other_scalar(machine, value, constant) {
                    return Ok(!is_equal);
                }
                Ok(machine.store.equals_asked(value, constant)? == is_equal)
            })
        }
        // VarEqConst: x = c.
        (Leaf::Current(variable), Leaf::Constant(constant)) => {
            let (variable, constant) = (*variable, *constant);
            test(move |machine| {
                let value = machine.read_current(variable)?;
                Ok(machine.store.equals(value, constant)? == is_equal)
            })
        }
        _ => {
            let (left, right) = (left.clone(), right.clone());
            test(move |machine| {
                let left = left.read(machine)?;
                let right = right.read(machine)?;
                Ok(machine.store.equals_asked(left, right)? == is_equal)
            })
        }
    }
}

// Whether two values are distinct scalars of one kind, which `equals` finds unequal without
// failing.
#[inline(always)]
fn is_other_scalar(machine: &Machine<'_>, value: Id, constant: Id) -> bool {
    let kind = machine.store.kind_of(constant);
    value != constant && kind <= KIND_STRING && machine.store.kind_of(value) == kind
}

/// A body whose first conjunct is `r.f = c` of the name a loop binds: an element whose field `f`
/// is found by its id and is another scalar of `c`'s kind makes the body FALSE, as evaluating it
/// would, without failing or evaluating more, so the loop passes it without binding the name.
pub(crate) struct Reject {
    key: Id,
    constant: Id,
    hint: AtomicU32,
}

impl Reject {
    pub(crate) fn of(predicate: &Predicate, bound: u32) -> Option<Reject> {
        let first = match predicate {
            Predicate::And(operands) => operands.first()?,
            predicate => predicate,
        };
        match first {
            Predicate::Equal {
                left: Leaf::Field { slot, key, .. },
                right: Leaf::Constant(constant),
                is_equal: true,
            } if *slot == bound => Some(Reject {
                key: *key,
                constant: *constant,
                hint: AtomicU32::new(0),
            }),
            _ => None,
        }
    }

    /// Whether the body is FALSE for the element.
    #[inline(always)]
    pub(crate) fn rejects(&self, machine: &Machine<'_>, element: Id) -> bool {
        let hinted = self.hint.load(Ordering::Relaxed);
        let mut position = hinted;
        let Some(value) = machine.store.field_by_id(element, self.key, &mut position) else {
            return false;
        };
        if position != hinted {
            self.hint.store(position, Ordering::Relaxed);
        }
        is_other_scalar(machine, value, self.constant)
    }
}

/// The closure of a compiled boolean whose value is the predicate's.
pub(crate) fn evaluate(predicate: &Predicate) -> Eval {
    let test = predicate.build();
    eval(move |machine| test(machine).map(bool_id))
}
