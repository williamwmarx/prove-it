mod store;
mod eval;
mod fp;
use store::*;
use std::time::Instant;

const STATE_WIDTH: usize = 4;

// An open-addressed set of 64-bit fingerprints: an empty slot holds 0, so the fingerprint 0 is kept
// in a flag of its own, as FpShard.has_zero is in DESIGN.md.
struct FingerprintSet { slots: Vec<u64>, mask: usize, count: usize, has_zero: bool }
impl FingerprintSet {
    fn new() -> Self { FingerprintSet { slots: vec![0; 1 << 10], mask: (1 << 10) - 1, count: 0, has_zero: false } }
    fn insert(&mut self, fp: u64) -> bool {
        if fp == 0 { let is_new = !self.has_zero; self.has_zero = true; return is_new; }
        let key = fp;
        let mut slot = (key ^ (key >> 29)) as usize & self.mask;
        loop {
            let stored = self.slots[slot];
            if stored == 0 { break; }
            if stored == key { return false; }
            slot = (slot + 1) & self.mask;
        }
        self.slots[slot] = key;
        self.count += 1;
        if self.count * 2 > self.slots.len() {
            let doubled = vec![0; self.slots.len() * 2]; let old = std::mem::replace(&mut self.slots, doubled);
            self.mask = self.slots.len() - 1;
            for key in old { if key != 0 { let mut s = (key ^ (key >> 29)) as usize & self.mask; while self.slots[s] != 0 { s = (s + 1) & self.mask; } self.slots[s] = key; } }
        }
        true
    }
}

// The state table of search.ts: [hash, index] pairs, linear probing, states stored side by side.
struct StateTable { states: Vec<i32>, table: Vec<i32>, mask: usize, count: usize }
impl StateTable {
    fn new() -> Self { StateTable { states: Vec::with_capacity(STATE_WIDTH * 1024), table: vec![-1; 2 << 10], mask: (1 << 10) - 1, count: 0 } }
    #[inline(always)]
    fn hash(state: &[i32]) -> i32 {
        let mut hash = 0x811c9dc5u32 as i32;
        for &id in state { hash = (hash ^ id).wrapping_mul(0x01000193); }
        hash ^= ((hash as u32) >> 13) as i32;
        hash = hash.wrapping_mul(0x5bd1e995);
        hash ^ (((hash as u32) >> 15) as i32)
    }
    fn grow(&mut self) {
        let mut next = vec![-1; self.table.len() * 2];
        let mask = self.table.len() - 1;
        for slot in 0..=self.mask {
            let stored = self.table[2 * slot + 1];
            if stored == -1 { continue; }
            let mut to = self.table[2 * slot] as usize & mask;
            while next[2 * to + 1] != -1 { to = (to + 1) & mask; }
            next[2 * to] = self.table[2 * slot];
            next[2 * to + 1] = stored;
        }
        self.table = next;
        self.mask = mask;
    }
    // Returns 1 when the state is new.
    fn probe(&mut self, state: &[i32; STATE_WIDTH]) -> u32 {
        let hash = Self::hash(state);
        let mut slot = hash as usize & self.mask;
        loop {
            let stored = self.table[2 * slot + 1];
            if stored == -1 {
                self.states.extend_from_slice(state);
                self.table[2 * slot] = hash;
                self.table[2 * slot + 1] = self.count as i32;
                self.count += 1;
                if self.count * 2 > self.mask + 1 { self.grow(); }
                return 1;
            }
            if self.table[2 * slot] == hash {
                let offset = stored as usize * STATE_WIDTH;
                if self.states[offset..offset + STATE_WIDTH] == state[..] { return 0; }
            }
            slot = (slot + 1) & self.mask;
        }
    }
}

fn workload(iterations: u32, is_probing: bool, is_fingerprinted: bool) -> Result<(f64, usize, usize, i32), Bail> {
    let texts = ["rm", "type", "working", "prepared", "committed", "aborted", "Prepared", "Commit", "Abort", "r0", "r1", "r2", "r3", "r4"];
    let mut store = Store::new(&texts);
    let mut seed: u32 = 0x2545f491;
    let mut next = || { seed ^= seed << 13; seed ^= seed >> 17; seed ^= seed << 5; seed };
    let rms: Vec<Id> = ["r0", "r1", "r2", "r3", "r4"].iter().map(|t| store.str(t)).collect();
    let states: Vec<Id> = ["working", "prepared", "committed", "aborted"].iter().map(|t| store.str(t)).collect();
    let types: Vec<Id> = ["Prepared", "Commit", "Abort"].iter().map(|t| store.str(t)).collect();
    let keys = [store.str("rm"), store.str("type")];
    let shape = store.record_shape(&keys);
    let mut rm_state = store.function_of_sorted(&rms, &vec![states[0]; rms.len()]);
    let mut msgs = EMPTY_SET;
    let mut log = EMPTY_TUPLE;
    let mut checksum: i32 = 0;
    let mut table = StateTable::new();
    let fp64 = fp::Fp64::new();
    let mut shifts = Shifts::new();
    let mut values = ValueFingerprints::new();
    let mut seen = FingerprintSet::new();
    let started = Instant::now();
    for _ in 0..iterations {
        let random = next();
        let rm = (random % 5) as usize;
        rm_state = store.except(rm_state, rms[rm], states[((random >> 3) & 3) as usize])?;
        let record = store.record_of(&shape, &[rms[rm], types[((random >> 5) % 3) as usize]]);
        msgs = store.with_element(msgs, record)?;
        if (random >> 8) & 3 == 0 { msgs = EMPTY_SET; }
        let elements = [store.int(((random >> 12) % 4) as i32), store.int(((random >> 16) % 4) as i32), store.int(((random >> 20) % 4) as i32)];
        let small = store.set_of(&elements)?;
        log = if (random >> 24) & 3 == 0 || store.size(log) >= 3 { EMPTY_TUPLE } else { let bit = store.int(((random >> 27) & 1) as i32); store.append_tuple(log, bit) };
        let state = [rm_state, small, log, if msgs == EMPTY_SET { 1 } else { 0 }];
        if is_probing && !is_fingerprinted { table.probe(&state); }
        if is_probing && is_fingerprinted {
            // TLC's FPSet: the state is its 64-bit fingerprint, a probe one random read.
            let mut f = 0x911498ae0e66bad6u64;
            for &id in &state { let (vf, vl) = values.get(&fp64, &mut shifts, &store, id); f = shifts.shift(&fp64, f, vl) ^ vf; }
            if seen.insert(f) { table.states.extend_from_slice(&state); table.count += 1; }
        }
        checksum = checksum.wrapping_mul(31).wrapping_add(rm_state).wrapping_add(msgs).wrapping_add(small).wrapping_add(log);
    }
    Ok((started.elapsed().as_secs_f64() * 1e3, store.count(), table.count, checksum))
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let which = args.get(1).map(|s| s.as_str()).unwrap_or("store");
    match which {
        "store" => {
            let iterations: u32 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(2_000_000);
            for _ in 0..3 {
                let is_probing = args.get(3).map(|s| s != "noprobe").unwrap_or(true);
                let is_fingerprinted = args.get(3).map(|s| s == "fp").unwrap_or(false);
                let (ms, values, states, checksum) = workload(iterations, is_probing, is_fingerprinted).unwrap();
                println!("rust store: {iterations} iterations in {ms:.1} ms ({:.0} ns/iteration), {values} values, {states} states, checksum {checksum}", ms * 1e6 / iterations as f64);
            }
        }
        "eval" => eval::bench(),
        "fp" => fp::bench(),
        _ => {}
    }
}
