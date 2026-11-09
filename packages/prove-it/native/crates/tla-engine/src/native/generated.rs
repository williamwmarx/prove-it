//! Random predicates over random states, seeded so a failure names its seed: what the lowering and
//! the emitted code are each held to the closures with, as the design's differential fuzzer.

use std::sync::Arc;

use tla_values::store::{FALSE, Outcome, Store, TRUE};
use tla_values::{Bail, Id};

use crate::compile::predicate::{Leaf, Predicate, Test};
use crate::machine::{Eval, Machine, Program, UNASSIGNED};

// A deterministic generator, so that a failure names its seed.
pub(super) struct Random(pub(super) u64);

impl Random {
    pub(super) fn next(&mut self, bound: u64) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0 % bound
    }

    pub(super) fn pick<T: Copy>(&mut self, items: &[T]) -> T {
        items[self.next(items.len() as u64) as usize]
    }
}

const VARIABLES: u32 = 3;
const SLOTS: u32 = 3;

// Ints, strings, booleans, sets, tuples and functions, so that some comparisons fail as TLC's do.
fn values(store: &mut Store) -> Vec<Id> {
    let ints: Vec<Id> = (0..3).map(|value| store.int(value).unwrap()).collect();
    let strings: Vec<Id> = ["a", "b"]
        .iter()
        .map(|text| store.str(&text.encode_utf16().collect::<Vec<_>>()))
        .collect();
    let mut all = [ints.clone(), strings.clone(), vec![TRUE, FALSE]].concat();
    // The empty set's id, 2, is the first past FALSE's and TRUE's.
    all.push(store.set_of(&[]).unwrap());
    all.push(store.set_of(&ints[..2]).unwrap());
    all.push(store.set_of(&strings).unwrap());
    all.push(store.tuple_of(&strings));
    all.push(store.tuple_of(&ints[1..]));
    all.push(store.function_of(&strings, &ints[..2]).unwrap());
    all
}

fn leaf(random: &mut Random, values: &[Id]) -> Leaf {
    match random.next(6) {
        0 => Leaf::Slot(random.next(u64::from(SLOTS)) as u32),
        1 => Leaf::Constant(random.pick(values)),
        2 => Leaf::Current(random.next(u64::from(VARIABLES)) as u32),
        3 => Leaf::ApplyVar {
            variable: random.next(u64::from(VARIABLES)) as u32,
            slot: random.next(u64::from(SLOTS)) as u32,
            is_int: false,
        },
        4 => Leaf::ApplyVar2 {
            variable: random.next(u64::from(VARIABLES)) as u32,
            slot: random.next(u64::from(SLOTS)) as u32,
            second: random.next(u64::from(SLOTS)) as u32,
        },
        _ => Leaf::Eval(eval(random, values)),
    }
}

fn eval(random: &mut Random, values: &[Id]) -> Eval {
    if random.next(5) == 0 {
        return Arc::new(|_: &mut Machine<'_>| Err(Bail("a test's bail")));
    }
    let value = random.pick(values);
    Arc::new(move |_: &mut Machine<'_>| Ok(value))
}

fn predicate(random: &mut Random, values: &[Id], depth: u32) -> Predicate {
    let choice = random.next(if depth == 0 { 3 } else { 7 });
    match choice {
        0 => Predicate::Equal {
            left: leaf(random, values),
            right: leaf(random, values),
            is_equal: random.next(2) == 0,
        },
        1 => Predicate::Member {
            element: leaf(random, values),
            set: leaf(random, values),
            is_in: random.next(2) == 0,
        },
        2 => Predicate::Eval {
            eval: eval(random, values),
            is_checked: random.next(2) == 0,
        },
        3 => Predicate::Not(Box::new(predicate(random, values, depth - 1))),
        4 | 5 => {
            let operands = (0..random.next(4))
                .map(|_| predicate(random, values, depth - 1))
                .collect();
            if choice == 4 {
                Predicate::And(operands)
            } else {
                Predicate::Or(operands)
            }
        }
        _ => Predicate::Implies(
            Box::new(predicate(random, values, depth - 1)),
            Box::new(predicate(random, values, depth - 1)),
        ),
    }
}

pub(super) fn program() -> Program {
    Program {
        width: VARIABLES as usize,
        slot_count: SLOTS as usize,
        ..Program::default()
    }
}

/// Runs 2,000 predicates on 8 states each, as `build` builds them and as their closures run, and
/// asserts they agree; gives how many held, failed and bailed.
pub(super) fn compare(program: &Program, build: impl Fn(&Predicate) -> Test) -> [usize; 3] {
    let mut store = Store::new();
    store.reset(std::iter::empty::<&[u16]>());
    let values = values(&mut store);
    let mut machine = Machine::new(program, store);
    let mut random = Random(0x5eed_1234_abcd_0001);
    let mut outcomes = [0; 3];
    for _ in 0..2_000 {
        let predicate = predicate(&mut random, &values, 4);
        let closures = predicate.build();
        let built = build(&predicate);
        for _ in 0..8 {
            for variable in 0..VARIABLES as usize {
                machine.cur[variable] = if random.next(8) == 0 {
                    UNASSIGNED
                } else {
                    random.pick(&values)
                };
            }
            for slot in 0..SLOTS as usize {
                machine.locals[slot] = random.pick(&values);
            }
            let expected: Outcome<bool> = closures(&mut machine);
            assert_eq!(built(&mut machine), expected);
            outcomes[match expected {
                Ok(true) => 0,
                Ok(false) => 1,
                Err(_) => 2,
            }] += 1;
        }
    }
    outcomes
}
