//! TLC's 64-bit fingerprints (FP64 with `-fp 0`) of values and states, as
//! `src/tlc/fingerprint.ts` and `src/engine/fingerprint.ts` compute them.
//!
//! TLC fingerprints a state by extending FP64 over the bytes of its values. Extending is linear
//! over GF(2), so extending a fingerprint by the bytes of a value v is `shift(fp, |v|) ^ F(v)`,
//! where F(v) extends zero by v and `shift` extends by |v| zero bytes. F and |v| are computed once
//! per id, and a state's fingerprint takes one shift and one xor per variable, or, from its
//! parent's, one per variable that changed.

use std::collections::HashMap;

use crate::store::{Id, KIND_BOOL, KIND_INT, KIND_MODEL, KIND_SET, KIND_STRING, Store, TRUE};

/// FP64.Polys[0], which `-fp 0` selects. A fingerprint starts as the polynomial.
pub const INITIAL: u64 = 0x911498ae0e66bad6;

const BOOL_VALUE: u8 = 0;
const INT_VALUE: u8 = 1;
const STRING_VALUE: u8 = 3;
const SET_ENUM_VALUE: u8 = 5;
const FCN_RCD_VALUE: u8 = 9;
const MODEL_VALUE: u8 = 21;

// FP64's ByteModTable: entry b is the fingerprint from zero of byte b, the sum of x^(71 - k) mod
// the polynomial for each bit k of b, with x^0 in a fingerprint's top bit.
const BYTE_MOD: [u64; 256] = {
    let mut table = [0u64; 256];
    let mut power: u64 = 1 << 63;
    let mut exponent = 1;
    while exponent < 72 {
        let is_reduced = power & 1 != 0;
        power = (power >> 1) ^ if is_reduced { INITIAL } else { 0 };
        if exponent >= 64 {
            let bit = 1usize << (71 - exponent);
            let mut byte = 0;
            while byte < 256 {
                if byte & bit != 0 {
                    table[byte] ^= power;
                }
                byte += 1;
            }
        }
        exponent += 1;
    }
    table
};

#[inline(always)]
pub fn extend_byte(fingerprint: u64, byte: u8) -> u64 {
    (fingerprint >> 8) ^ BYTE_MOD[((u64::from(byte) ^ fingerprint) & 0xff) as usize]
}

/// Extends by the four bytes of a word, lowest first.
#[inline(always)]
pub fn extend_int(fingerprint: u64, word: i32) -> u64 {
    (word as u32)
        .to_le_bytes()
        .into_iter()
        .fold(fingerprint, extend_byte)
}

// A table that shifts a fingerprint by a fixed number of zero bytes: entry [k][b] holds the shift
// of the fingerprint whose byte k is b and whose other bytes are zero.
struct ShiftTable([[u64; 256]; 8]);

impl ShiftTable {
    // Shifting is linear, so the table needs only the shifts of the 64 single bits: every other
    // entry is the xor of the entry without its lowest bit and the entry of that bit.
    fn build(shift: impl Fn(u64) -> u64) -> Box<ShiftTable> {
        let mut table = Box::new(ShiftTable([[0; 256]; 8]));
        for (position, row) in table.0.iter_mut().enumerate() {
            for bit in 0..8 {
                row[1 << bit] = shift(1 << (8 * position + bit));
            }
            for byte in 3..256usize {
                let lowest = byte.isolate_lowest_one();
                if lowest != byte {
                    row[byte] = row[lowest] ^ row[byte ^ lowest];
                }
            }
        }
        table
    }

    #[inline(always)]
    fn shift(&self, fingerprint: u64) -> u64 {
        self.0
            .iter()
            .enumerate()
            .fold(0, |shifted, (position, row)| {
                shifted ^ row[((fingerprint >> (8 * position)) & 0xff) as usize]
            })
    }
}

// Tables for the lengths of values and of the tails of states, as far as the cap allows.
const MAXIMUM_LENGTH_TABLES: usize = 1024;
// A value's length table, before it is looked up.
const UNKNOWN_TABLE: i32 = 0;
// A length past the cap, shifted by powers of two.
const NO_TABLE: i32 = -1;

#[derive(Clone, Copy, Default)]
struct ValueFingerprint {
    fingerprint: u64,
    length: u64,
    // The number of the value's length table, from 1, or UNKNOWN_TABLE or NO_TABLE.
    table: i32,
    is_computed: bool,
}

/// F(v) and |v| of the store's values, computed as they are first asked for, and the tables that
/// shift by their lengths.
#[derive(Default)]
pub struct Fingerprints {
    generation: Option<u32>,
    values: Vec<ValueFingerprint>,
    // Shifts by 2^j zero bytes.
    powers: Vec<Box<ShiftTable>>,
    lengths: Vec<Box<ShiftTable>>,
    length_numbers: HashMap<u64, i32>,
}

impl Fingerprints {
    pub fn new() -> Fingerprints {
        Fingerprints::default()
    }

    /// Forgets every value's fingerprint, as `resetFingerprints` does. The fingerprints also
    /// forget them when the store they were computed from is reset.
    pub fn reset(&mut self) {
        self.values.clear();
    }

    fn get_power(&mut self, exponent: usize) -> &ShiftTable {
        while self.powers.len() <= exponent {
            let table = match self.powers.last() {
                None => ShiftTable::build(|fingerprint| extend_byte(fingerprint, 0)),
                Some(half) => ShiftTable::build(|fingerprint| half.shift(half.shift(fingerprint))),
            };
            self.powers.push(table);
        }
        &self.powers[exponent]
    }

    fn shift_by_powers(&mut self, mut fingerprint: u64, mut length: u64) -> u64 {
        let mut exponent = 0;
        while length > 0 {
            if length % 2 == 1 {
                fingerprint = self.get_power(exponent).shift(fingerprint);
            }
            exponent += 1;
            length /= 2;
        }
        fingerprint
    }

    // The number of the table that shifts by a length, or NO_TABLE past the cap.
    fn get_length_table(&mut self, length: u64) -> i32 {
        if let Some(&number) = self.length_numbers.get(&length) {
            return number;
        }
        if self.lengths.len() >= MAXIMUM_LENGTH_TABLES {
            return NO_TABLE;
        }
        // The powers it is built from, made before the closure borrows them.
        let exponents = u64::BITS - length.leading_zeros();
        if exponents > 0 {
            self.get_power(exponents as usize - 1);
        }
        let powers = &self.powers;
        let table = ShiftTable::build(|mut fingerprint| {
            for (exponent, power) in powers.iter().enumerate() {
                if length >> exponent & 1 == 1 {
                    fingerprint = power.shift(fingerprint);
                }
            }
            fingerprint
        });
        self.lengths.push(table);
        let number = self.lengths.len() as i32;
        self.length_numbers.insert(length, number);
        number
    }

    fn shift_by_table(&mut self, number: i32, fingerprint: u64, length: u64) -> u64 {
        if number > 0 {
            self.lengths[number as usize - 1].shift(fingerprint)
        } else {
            self.shift_by_powers(fingerprint, length)
        }
    }

    /// Extends a fingerprint by `length` zero bytes.
    pub fn shift(&mut self, fingerprint: u64, length: u64) -> u64 {
        let number = self.get_length_table(length);
        self.shift_by_table(number, fingerprint, length)
    }

    fn check_generation(&mut self, store: &Store) {
        if self.generation != Some(store.generation()) {
            self.generation = Some(store.generation());
            self.values.clear();
        }
    }

    fn get_entry(&mut self, id: Id) -> &mut ValueFingerprint {
        let index = id as usize;
        if index >= self.values.len() {
            self.values
                .resize((2 * (index + 1)).max(1024), ValueFingerprint::default());
        }
        &mut self.values[index]
    }

    // Extends a fingerprint by a value whose F and length are known, with its table found once.
    fn extend_known(&mut self, fingerprint: u64, id: Id) -> u64 {
        let entry = *self.get_entry(id);
        let number = if entry.table == UNKNOWN_TABLE {
            let number = self.get_length_table(entry.length);
            self.get_entry(id).table = number;
            number
        } else {
            entry.table
        };
        self.shift_by_table(number, fingerprint, entry.length) ^ entry.fingerprint
    }

    // The ids a value's fingerprint reads: a set's elements, a function's keys and values. A
    // tuple's keys are integers that are fingerprinted without interning them.
    fn for_each_part(store: &Store, id: Id, mut visit: impl FnMut(Option<Id>, u32)) {
        let kind = store.kind_of(id);
        if kind < KIND_SET {
            return;
        }
        for index in 0..store.size_of(id) {
            if kind == KIND_SET {
                visit(Some(store.element_at(id, index)), index);
            } else {
                visit(store.peek_key(id, index), index);
                visit(Some(store.get_range_value(id, index)), index);
            }
        }
    }

    /// F(v) and |v| of a value.
    pub fn get_value(&mut self, store: &Store, id: Id) -> (u64, u64) {
        self.check_generation(store);
        self.compute(store, id);
        let entry = self.values[id as usize];
        (entry.fingerprint, entry.length)
    }

    // Computes a value's F and length, its parts' first, without recursing: a value is computed
    // when it comes off the stack the second time, after the parts pushed above it.
    fn compute(&mut self, store: &Store, id: Id) {
        let mut pending = vec![(id, false)];
        while let Some((top, is_expanded)) = pending.pop() {
            if self.get_entry(top).is_computed {
                continue;
            }
            if is_expanded {
                let computed = self.compute_one(store, top);
                *self.get_entry(top) = computed;
                continue;
            }
            pending.push((top, true));
            Fingerprints::for_each_part(store, top, |part, _| {
                if let Some(part) = part {
                    pending.push((part, false));
                }
            });
        }
    }

    fn compute_one(&mut self, store: &Store, id: Id) -> ValueFingerprint {
        let (fingerprint, length) = match store.kind_of(id) {
            KIND_BOOL => (
                extend_byte(
                    extend_byte(0, BOOL_VALUE),
                    if id == TRUE { b't' } else { b'f' },
                ),
                2,
            ),
            KIND_INT => (get_int(store.int_of(id)), 5),
            KIND_STRING => {
                let text = store.text_of(id);
                let start = extend_int(extend_byte(0, STRING_VALUE), text.len() as i32);
                let fingerprint = text.iter().fold(start, |fingerprint, &unit| {
                    extend_byte(fingerprint, unit as u8)
                });
                (fingerprint, 5 + text.len() as u64)
            }
            KIND_MODEL => (
                extend_int(extend_byte(0, MODEL_VALUE), store.text_rank_of(id) + 1),
                5,
            ),
            kind => {
                let tag = if kind == KIND_SET {
                    SET_ENUM_VALUE
                } else {
                    FCN_RCD_VALUE
                };
                let mut fingerprint = extend_int(extend_byte(0, tag), store.size_of(id) as i32);
                let mut length = 5;
                let mut parts = Vec::new();
                Fingerprints::for_each_part(store, id, |part, index| parts.push((part, index)));
                for (part, index) in parts {
                    match part {
                        Some(part) => {
                            fingerprint = self.extend_known(fingerprint, part);
                            length += self.values[part as usize].length;
                        }
                        None => {
                            fingerprint = self.shift(fingerprint, 5) ^ get_int(index as i32 + 1);
                            length += 5;
                        }
                    }
                }
                (fingerprint, length)
            }
        };
        ValueFingerprint {
            fingerprint,
            length,
            table: UNKNOWN_TABLE,
            is_computed: true,
        }
    }

    /// TLC's fingerprint of one state, its values read in `order`.
    pub fn get_state(&mut self, store: &Store, state: &[Id], order: &[usize]) -> u64 {
        self.check_generation(store);
        order.iter().fold(INITIAL, |fingerprint, &index| {
            self.compute(store, state[index]);
            self.extend_known(fingerprint, state[index])
        })
    }

    /// The TLC fingerprints of states stored one after another, each `width` ids, read in
    /// `order`, as `getStateFingerprints` computes them.
    ///
    /// A state's fingerprint is `shift(INITIAL, L)` xor the xor over its values v_j of
    /// `shift(F(v_j), S_j)`, where L is the length of all its values and S_j that of the values
    /// after v_j. Where a state differs from its parent only in values of the same lengths, L and
    /// every S_j are the parent's, so its fingerprint is the parent's xor
    /// `shift(F(v_j) ^ F(v'_j), S_j)` for each value that changed. An initial state, which has no
    /// parent, follows from the state before it in the same way.
    pub fn get_states(
        &mut self,
        store: &Store,
        states: &[Id],
        width: usize,
        order: &[usize],
        parents: Option<&[i32]>,
    ) -> Vec<u64> {
        self.check_generation(store);
        let count = states.len().checked_div(width).unwrap_or(0);
        let mut fingerprints = Vec::with_capacity(count);
        // The tail length each position last had and its table, since it seldom changes.
        let mut tails = vec![(u64::MAX, NO_TABLE); order.len()];
        for state in 0..count {
            let row = &states[state * width..(state + 1) * width];
            let parent = parents.map_or(-1, |parents| parents[state]);
            let earlier = if parent == -1 {
                state as i64 - 1
            } else {
                i64::from(parent)
            };
            let from_earlier = if earlier >= 0 && (earlier as usize) < state {
                let earlier = earlier as usize;
                let earlier_row = &states[earlier * width..(earlier + 1) * width];
                self.get_from_earlier(
                    store,
                    row,
                    earlier_row,
                    fingerprints[earlier],
                    order,
                    &mut tails,
                )
            } else {
                None
            };
            let fingerprint = from_earlier.unwrap_or_else(|| self.get_state(store, row, order));
            fingerprints.push(fingerprint);
        }
        fingerprints
    }

    // A state's fingerprint from that of an earlier one, if the values that differ keep their
    // lengths. Values are computed as they first appear.
    fn get_from_earlier(
        &mut self,
        store: &Store,
        row: &[Id],
        earlier_row: &[Id],
        earlier_fingerprint: u64,
        order: &[usize],
        tails: &mut [(u64, i32)],
    ) -> Option<u64> {
        let mut fingerprint = earlier_fingerprint;
        let mut tail = 0;
        for (position, &index) in order.iter().enumerate().rev() {
            let (id, earlier_id) = (row[index], earlier_row[index]);
            self.compute(store, id);
            if id != earlier_id {
                self.compute(store, earlier_id);
                let (value, earlier_value) =
                    (self.values[id as usize], self.values[earlier_id as usize]);
                if value.length != earlier_value.length {
                    return None;
                }
                if tails[position].0 != tail {
                    tails[position] = (tail, self.get_length_table(tail));
                }
                let changed = value.fingerprint ^ earlier_value.fingerprint;
                fingerprint ^= self.shift_by_table(tails[position].1, changed, tail);
            }
            tail += self.values[id as usize].length;
        }
        Some(fingerprint)
    }

    /// The fingerprints extended over every value of every state, which
    /// `PROVE_IT_FINGERPRINT=reference` takes.
    pub fn get_states_reference(
        &mut self,
        store: &Store,
        states: &[Id],
        width: usize,
        order: &[usize],
    ) -> Vec<u64> {
        self.check_generation(store);
        if width == 0 {
            return Vec::new();
        }
        states
            .chunks_exact(width)
            .map(|row| {
                order.iter().fold(INITIAL, |fingerprint, &index| {
                    let (value, length) = self.get_value(store, row[index]);
                    self.shift_by_powers(fingerprint, length) ^ value
                })
            })
            .collect()
    }
}

// F of an integer.
fn get_int(value: i32) -> u64 {
    extend_int(extend_byte(0, INT_VALUE), value)
}
