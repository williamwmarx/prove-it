//! The micro-benchmark of native/DESIGN.md 3.1 and 10.4: MutualExclusion ==
//! \A i, j \in 1..N : i # j => ~(pc[i] = "cs" /\ pc[j] = "cs"), N = 12, compiled from the IR of
//! MutualExclusion.tla and evaluated on 4,096 states in which at most one process is in its
//! critical section, so every evaluation runs all N * N cases, as the prototype's states do. The
//! memo tables are off, so each evaluation is timed whole. It prints each run and the median.
//! Usage: cargo bench -p tla-engine --bench invariant [runs]

use std::time::Instant;

use tla_engine::{Compiler, Machine, Options, Root};
use tla_values::store::TRUE;
use tla_values::{Id, Store};

const N: usize = 12;
const STATES: usize = 4096;
const ROUNDS: usize = 200;

fn main() {
    let runs: usize = std::env::args()
        .skip(1)
        .find_map(|argument| argument.parse().ok())
        .unwrap_or(15);
    let ir = tla_ir::decode(include_bytes!("mutual-exclusion.ir")).expect("the bench's IR");
    let ranked: Vec<Vec<u16>> = (0..ir.ranked_count)
        .map(|text| ir.get_text_units(text))
        .collect();
    let mut store = Store::new();
    store.reset(ranked.iter().map(Vec::as_slice));
    let options = Options {
        is_memo_off: true,
        ..Options::default()
    };
    let mut compiler = Compiler::new(&ir, &mut store, options);
    let definition = ir.model.invariants[0]
        .root
        .definition
        .expect("MutualExclusion");
    let invariant = compiler
        .compile_root(Root::Definition(definition))
        .expect("MutualExclusion compiles");
    let program = compiler.finish();
    let texts: Vec<Id> = ["cs", "s0", "s1", "s2", "s3", "s4"]
        .iter()
        .map(|text| store.str(&text.encode_utf16().collect::<Vec<u16>>()))
        .collect();
    let states: Vec<Id> = (0..STATES)
        .map(|state| {
            let pc: Vec<Id> = (0..N)
                .map(|process| {
                    if state % (N + 3) == process {
                        texts[0]
                    } else {
                        texts[1 + (state * 7 + process) % 5]
                    }
                })
                .collect();
            store.tuple_of(&pc)
        })
        .collect();
    let mut machine = Machine::new(&program, store);
    let mut timings = Vec::with_capacity(runs);
    for run in 0..runs {
        let started = Instant::now();
        for _ in 0..ROUNDS {
            for &pc in &states {
                machine.set_current(&[pc], 0);
                let holds = machine.evaluate(invariant.eval()).expect("no stop");
                assert_eq!(holds, TRUE);
            }
        }
        let nanoseconds = started.elapsed().as_secs_f64() * 1e9 / (ROUNDS * STATES) as f64;
        println!("run {run:>2}: {nanoseconds:>7.1} ns per evaluation");
        timings.push(nanoseconds);
    }
    timings.sort_by(f64::total_cmp);
    println!(
        "MutualExclusion, N = {N}, fused nodes, memo off: median {:.1} ns per evaluation (min {:.1}, max {:.1})",
        timings[runs / 2],
        timings[0],
        timings[runs - 1]
    );
}
