//! The store's share of the prototype's workload (DESIGN.md 10.2), in ns per step: three runs of
//! 2M steps, each from a reset store, as `cargo bench -p tla-values` runs them.

#[path = "../tests/common/workload.rs"]
mod workload;

use std::time::Instant;

use tla_values::Store;

fn main() {
    let iterations = 2_000_000;
    let mut store = Store::new();
    for _ in 0..3 {
        let started = Instant::now();
        let result = workload::run(&mut store, iterations);
        let elapsed = started.elapsed();
        println!(
            "store operations: {iterations} steps in {:.1} ms ({:.0} ns per step), {} values, checksum {}",
            elapsed.as_secs_f64() * 1e3,
            elapsed.as_secs_f64() * 1e9 / f64::from(iterations),
            result.values,
            result.checksum
        );
    }
}
