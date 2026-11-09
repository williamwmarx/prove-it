// The prototype's store workload (native/prototypes/store-bench/workload.ts, removed after 1916b69),
// whose TypeScript run on src/engine/store.ts gives the value counts and checksums the tests expect.
// Each step does an EXCEPT on a 5-key function, a 2-field record, a withElement on a growing set, a
// 3-element setOf, and an append to or a reset of a short tuple.

use tla_values::store::{EMPTY_SET, EMPTY_TUPLE, Store};

pub struct Workload {
    pub values: usize,
    pub checksum: i32,
}

fn utf16(text: &str) -> Vec<u16> {
    text.encode_utf16().collect()
}

pub fn run(store: &mut Store, iterations: u32) -> Workload {
    let rms = ["r0", "r1", "r2", "r3", "r4"];
    let order: Vec<Vec<u16>> = [
        "rm",
        "type",
        "working",
        "prepared",
        "committed",
        "aborted",
        "Prepared",
        "Commit",
        "Abort",
    ]
    .into_iter()
    .chain(rms)
    .map(utf16)
    .collect();
    store.reset(order.iter().map(Vec::as_slice));
    let mut seed: u32 = 0x2545f491;
    let mut next = || {
        seed ^= seed << 13;
        seed ^= seed >> 17;
        seed ^= seed << 5;
        seed
    };
    let mut strings =
        |texts: &[&str]| -> Vec<u32> { texts.iter().map(|text| store.str(&utf16(text))).collect() };
    let rms = strings(&rms);
    let states = strings(&["working", "prepared", "committed", "aborted"]);
    let types = strings(&["Prepared", "Commit", "Abort"]);
    let keys = strings(&["rm", "type"]);
    let shape = store.create_record_shape(&keys);
    let mut rm_state = store.function_of_sorted(&rms, &[states[0]; 5]);
    let mut msgs = EMPTY_SET;
    let mut log = EMPTY_TUPLE;
    let mut checksum: i32 = 0;
    let int = |store: &mut Store, value: u32| store.int(i64::from(value)).unwrap();
    for _ in 0..iterations {
        let random = next();
        let rm = (random % 5) as usize;
        rm_state = store
            .except(rm_state, rms[rm], states[((random >> 3) & 3) as usize])
            .unwrap();
        let record = store.record_of(&shape, &[rms[rm], types[((random >> 5) % 3) as usize]]);
        msgs = store.with_element(msgs, record).unwrap();
        if (random >> 8) & 3 == 0 {
            msgs = EMPTY_SET;
        }
        let elements = [
            int(store, (random >> 12) % 4),
            int(store, (random >> 16) % 4),
            int(store, (random >> 20) % 4),
        ];
        let small = store.set_of(&elements).unwrap();
        log = if (random >> 24) & 3 == 0 || store.size_of(log) >= 3 {
            EMPTY_TUPLE
        } else {
            let bit = int(store, (random >> 27) & 1);
            store.append_tuple(log, bit)
        };
        checksum = checksum
            .wrapping_mul(31)
            .wrapping_add(rm_state as i32)
            .wrapping_add(msgs as i32)
            .wrapping_add(small as i32)
            .wrapping_add(log as i32);
    }
    Workload {
        values: store.value_count(),
        checksum,
    }
}
