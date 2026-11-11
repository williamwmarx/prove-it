//! TLC's 64-bit fingerprints (FP64 with the polynomial `-fp` picks) of values and states, as
//! `src/tlc/fingerprint.ts` and `src/engine/fingerprint.ts` compute them with `-fp 0`.
//!
//! TLC fingerprints a state by extending FP64 over the bytes of its values. Extending is linear
//! over GF(2), so extending a fingerprint by the bytes of a value v is `shift(fp, |v|) ^ F(v)`,
//! where F(v) extends zero by v and `shift` extends by |v| zero bytes. F and |v| are computed once
//! per id, and a state's fingerprint takes one shift and one xor per variable, or, from its
//! parent's, one per variable that changed.

use std::collections::HashMap;
use std::sync::{Arc, OnceLock};

use crate::store::{
    Bail, EMPTY_SLOT, Id, KIND_BOOL, KIND_FUNCTION, KIND_INFINITE_SET, KIND_INT,
    KIND_LAZY_FUNCTION, KIND_MODEL, KIND_SET, KIND_STRING, KIND_TUPLE, Outcome, Store, TRUE,
};

/// Why a value has no fingerprint here: it holds, at any depth, a function TLC keeps lazy or
/// Nat, Int or STRING, which TLC fails to fingerprint with an error the engine doesn't model.
pub const UNFINGERPRINTABLE: Bail =
    Bail("unsupported: fingerprinting a function TLC keeps lazy, or Nat, Int or STRING");

const BOOL_VALUE: u8 = 0;
const INT_VALUE: u8 = 1;
const STRING_VALUE: u8 = 3;
const SET_ENUM_VALUE: u8 = 5;
const FCN_RCD_VALUE: u8 = 9;
const MODEL_VALUE: u8 = 21;

/// FP64.Polys, the irreducible polynomials `-fp` picks one of to fingerprint with.
pub const POLYNOMIALS: [u64; 131] = [
    0x911498ae0e66bad6,
    0xda8a0ba66dae0181,
    0xc02f176b8f268d9f,
    0xd617bb1220fc7812,
    0xc6fd951ad34f9f74,
    0xdd1897bd991704d4,
    0xf5394c541cbfd343,
    0xb1dded37b5c7b8f7,
    0xb713ff61039dc632,
    0xdfb340cb2fb03d43,
    0xbc3e7e4c5ecb76a3,
    0xdbb4b1349cd7058a,
    0xf53e9dcb9e915cdf,
    0xca5f58e90dd01848,
    0x80e7ff4406891aa1,
    0xab541bf881fa8571,
    0xbf274e07ac5499d5,
    0x939b1ea933040a4e,
    0xb791a595448d75b1,
    0x8bf88d6ef85563a2,
    0xecb33ec339513a53,
    0xfa2d3e722db5208a,
    0xb4e2058aac479d24,
    0xafbd6474e7213b82,
    0x98c1694d14ffaeef,
    0xe188fb5c0a125e24,
    0xfa71cc3865487d80,
    0x891135f7c1c94569,
    0xcf77cdd16d22e3e6,
    0xeb5e3a1d2e2bb4b5,
    0x92f7f5b69cd00c55,
    0xa9fbbe40ca3b9ae9,
    0x84a7b33d85295bde,
    0xebd4680dbb6fdee2,
    0xa31fc46a0583b4d0,
    0xa792c94f15de3e49,
    0xd9d60a9feff4521a,
    0x9227ba31dfdda04b,
    0xfb4c89c607ce162d,
    0xa89b3b2e01479cc0,
    0xb35a0c2a28b89f7d,
    0x91d0b700b99d9ec2,
    0xf0646bbda05020b0,
    0xcb5d5f63ce043056,
    0xd276b6a04f42a1b8,
    0xbc1a7a7dbfeb47a3,
    0xe138acff7a963036,
    0xed860223c1557ee7,
    0x9b2491e980150ab6,
    0xe7e03dd8a5b4e59e,
    0xaaa3f5eac516783c,
    0xfe78cc267a724180,
    0xc22519a21edfac64,
    0xcdb2941933fec60f,
    0xc5f485551ef38aa1,
    0xa19293d250bd3335,
    0xa4d4c215a50b7afe,
    0xc1155176406a5070,
    0xecadaa8200e123ec,
    0xbacfe629d58b2f08,
    0xded991082148cb42,
    0x9a0ccbe5deaa88db,
    0x9a83246f342061bb,
    0xb71482842297ab05,
    0xf2407eeb997592bd,
    0xb7b43d4b5c4c4bcc,
    0xb339a2568221ffe7,
    0xdb4b6b379446ef9e,
    0xe43c205bb5c0b2b6,
    0xe8e1d141f19d6db0,
    0xd19e8710a4ea1c86,
    0x9704cecfa8d6d07b,
    0xb0a35716162c3f26,
    0xa2a68c0cf56390ac,
    0xe4a74bc601c95b46,
    0xe668fff675595e56,
    0xe0ea77ebe06fabbb,
    0xa8bb94f585279523,
    0xbeb667b42b684f21,
    0xd7b65410189e28af,
    0x85722037beffc5b9,
    0xe7e7c5f773426204,
    0xa5fd0cc8e060c6f4,
    0xb8f91ee9065dcf95,
    0xb4047008040f8b50,
    0xecb9ab6291c8cfcc,
    0xe08bb9b70caad6df,
    0xd6e086a301d95d56,
    0xf6a808f5f3fb9da3,
    0xfa74b8a8ef86fbc5,
    0xa0b6b33ba9e6381c,
    0x8c78703427873dbb,
    0xc5516ea423011021,
    0xb075cce8528ae7e2,
    0x92e4a37979e2b13b,
    0xafc9ab000ed81026,
    0xf1873f2a861a518a,
    0xf885d6b35770192c,
    0xd2a82f27f71f5f7e,
    0xd5e7a4dd8beb2d9f,
    0xbab9e7e65dc23e0f,
    0xd5fc877c0bdf5b85,
    0xab428169b9f31c02,
    0xb7b1351f9266d3ea,
    0xfad564914328f635,
    0x9623ecb1000db9bd,
    0x88d371ec6644c892,
    0xd0a71270573e271c,
    0xbd200d763f9d81b4,
    0x8484fd96374bf2ea,
    0xe0d0810749432294,
    0x8ebe9dadc88658ba,
    0xf6268c58993ae542,
    0xd6cc88fed0d359c9,
    0xbcaddb8d40a16690,
    0x92817c6db421cbf6,
    0xac63721120a371b5,
    0xd6cc137fdced0820,
    0xf1c5fbaebb617bd7,
    0xac35d78c765237a5,
    0xbd0a471fa9a23116,
    0x943a7031b946a5ae,
    0xe4e83520cb1aaebb,
    0xe92a4b73246dd124,
    0xafc1e070787c4c86,
    0xdfe84d42cf06286b,
    0x8b29ec962e4b964b,
    0x807eb5de812ede0f,
    0xa3cd71299c8b3bfd,
    0x845b8031ef886f35,
    0x91f5a5fa9c5515a5,
];

/// An irreducible polynomial of FP64.Polys, with the table FP64.Init builds of it.
pub struct Polynomial {
    value: u64,
    // FP64's ByteModTable: entry b is the fingerprint from zero of byte b, the sum of x^(71 - k)
    // mod the polynomial for each bit k of b, with x^0 in a fingerprint's top bit.
    byte_mod: [u64; 256],
}

impl Polynomial {
    /// FP64.Polys[index] and its table, built the first time it is asked for.
    pub fn get(index: usize) -> &'static Polynomial {
        static BUILT: [OnceLock<Polynomial>; POLYNOMIALS.len()] =
            [const { OnceLock::new() }; POLYNOMIALS.len()];
        BUILT[index].get_or_init(|| Polynomial::build(POLYNOMIALS[index]))
    }

    fn build(value: u64) -> Polynomial {
        let mut byte_mod = [0u64; 256];
        let mut power: u64 = 1 << 63;
        for exponent in 1..72 {
            let is_reduced = power & 1 != 0;
            power = (power >> 1) ^ if is_reduced { value } else { 0 };
            if exponent >= 64 {
                let bit = 1usize << (71 - exponent);
                for (byte, entry) in byte_mod.iter_mut().enumerate() {
                    if byte & bit != 0 {
                        *entry ^= power;
                    }
                }
            }
        }
        Polynomial { value, byte_mod }
    }

    /// The polynomial, which a fingerprint starts as (`FP64.New`).
    pub fn value(&self) -> u64 {
        self.value
    }

    #[inline(always)]
    pub fn extend_byte(&self, fingerprint: u64, byte: u8) -> u64 {
        (fingerprint >> 8) ^ self.byte_mod[((u64::from(byte) ^ fingerprint) & 0xff) as usize]
    }

    /// Extends by the four bytes of a word, lowest first.
    #[inline(always)]
    pub fn extend_int(&self, fingerprint: u64, word: i32) -> u64 {
        (word as u32)
            .to_le_bytes()
            .into_iter()
            .fold(fingerprint, |fingerprint, byte| {
                self.extend_byte(fingerprint, byte)
            })
    }

    // F of an integer.
    fn get_int(&self, value: i32) -> u64 {
        self.extend_int(self.extend_byte(0, INT_VALUE), value)
    }

    /// F and length of a boolean, as of a store's.
    pub fn of_bool(&self, value: bool) -> (u64, u64) {
        let byte = if value { b't' } else { b'f' };
        (self.extend_byte(self.extend_byte(0, BOOL_VALUE), byte), 2)
    }

    /// F and length of an integer.
    pub fn of_int(&self, value: i32) -> (u64, u64) {
        (self.get_int(value), 5)
    }

    /// F and length of a string.
    pub fn of_string(&self, text: &[u16]) -> (u64, u64) {
        let start = self.extend_int(self.extend_byte(0, STRING_VALUE), text.len() as i32);
        let fingerprint = text.iter().fold(start, |fingerprint, &unit| {
            self.extend_byte(fingerprint, unit as u8)
        });
        (fingerprint, 5 + text.len() as u64)
    }

    /// F and length of a model value, by the rank of its name.
    pub fn of_model(&self, rank: i32) -> (u64, u64) {
        (
            self.extend_int(self.extend_byte(0, MODEL_VALUE), rank + 1),
            5,
        )
    }
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

/// A value's F and length, with the number of the table that shifts by its length, in a cache.
#[derive(Clone, Copy, Default)]
pub struct ValueFingerprint {
    fingerprint: u64,
    length: u64,
    // The number of the value's length table, from 1, or UNKNOWN_TABLE or NO_TABLE.
    table: i32,
    is_computed: bool,
}

/// What fingerprinting a state's successors from it needs: its fingerprint, and, by position in
/// the order its values are read, the length of the values after that value, with the table that
/// shifts by that length, and its fingerprint before that value, computed as far as a successor
/// first asks.
#[derive(Default)]
pub struct Parent {
    fingerprint: u64,
    // The position of each of the state's values in the order.
    positions: Vec<usize>,
    tails: Vec<(u64, i32)>,
    prefixes: Vec<u64>,
}

/// Where a cache keeps the entries of the store's values: a search's own in [`Dense`], and a
/// parallel level's thread's in [`Overlaid`], which reads the search's in place. A search's cache
/// reads its entries as directly as it did before threads shared them.
pub trait Entries: Default {
    fn is_computed(&self, id: Id) -> bool;
    /// A computed value's entry.
    fn entry(&self, id: Id) -> ValueFingerprint;
    fn set(&mut self, id: Id, entry: ValueFingerprint);
    /// Keeps the number of the table a computed value's length takes, where the entry is the
    /// cache's own.
    fn set_table(&mut self, id: Id, table: i32);
    fn clear(&mut self);
    /// Forgets the entries of the values from this id on.
    fn truncate(&mut self, id: Id);
}

/// The entries of a search's cache, by id.
#[derive(Default)]
pub struct Dense(Vec<ValueFingerprint>);

impl Entries for Dense {
    #[inline(always)]
    fn is_computed(&self, id: Id) -> bool {
        self.0
            .get(id as usize)
            .is_some_and(|entry| entry.is_computed)
    }

    #[inline(always)]
    fn entry(&self, id: Id) -> ValueFingerprint {
        self.0[id as usize]
    }

    fn set(&mut self, id: Id, entry: ValueFingerprint) {
        let index = id as usize;
        if index >= self.0.len() {
            self.0
                .resize((2 * (index + 1)).max(1024), ValueFingerprint::default());
        }
        self.0[index] = entry;
    }

    #[inline(always)]
    fn set_table(&mut self, id: Id, table: i32) {
        self.0[id as usize].table = table;
    }

    fn clear(&mut self) {
        self.0.clear();
    }

    fn truncate(&mut self, id: Id) {
        self.0.truncate(id as usize);
    }
}

/// The fingerprints a search computed of its store's values, which the caches of a parallel
/// level's threads read in place while the store doesn't change.
pub struct SharedFingerprints(Arc<Vec<ValueFingerprint>>);

/// The entries of a parallel level's thread's cache: those of the store's values below `bound`
/// in the search's, else in `misses` where the thread computed them, and of the thread's own
/// values from `bound` on.
#[derive(Default)]
pub struct Overlaid {
    values: Vec<ValueFingerprint>,
    bound: Id,
    base: Option<Arc<Vec<ValueFingerprint>>>,
    misses: HashMap<Id, ValueFingerprint>,
}

impl Entries for Overlaid {
    #[inline(always)]
    fn is_computed(&self, id: Id) -> bool {
        self.entry(id).is_computed
    }

    // An id below the thread's own wraps past the end of its entries.
    #[inline(always)]
    fn entry(&self, id: Id) -> ValueFingerprint {
        match self.values.get(id.wrapping_sub(self.bound) as usize) {
            Some(&entry) => entry,
            None if id < self.bound => {
                let base = self.base.as_ref().and_then(|base| base.get(id as usize));
                match base.filter(|entry| entry.is_computed) {
                    // A length table's number is the search's cache's own.
                    Some(entry) => ValueFingerprint {
                        table: UNKNOWN_TABLE,
                        ..*entry
                    },
                    None => self.misses.get(&id).copied().unwrap_or_default(),
                }
            }
            None => ValueFingerprint::default(),
        }
    }

    fn set(&mut self, id: Id, entry: ValueFingerprint) {
        let Some(own) = id.checked_sub(self.bound) else {
            self.misses.insert(id, entry);
            return;
        };
        let index = own as usize;
        if index >= self.values.len() {
            self.values
                .resize((2 * (index + 1)).max(1024), ValueFingerprint::default());
        }
        self.values[index] = entry;
    }

    fn set_table(&mut self, id: Id, table: i32) {
        if let Some(entry) = id
            .checked_sub(self.bound)
            .and_then(|own| self.values.get_mut(own as usize))
        {
            entry.table = table;
        }
    }

    fn clear(&mut self) {
        self.values.clear();
        self.misses.clear();
    }

    fn truncate(&mut self, id: Id) {
        self.values.truncate(id.saturating_sub(self.bound) as usize);
    }
}

/// F(v) and |v| of the store's values, computed as they are first asked for, and the tables that
/// shift by their lengths.
pub struct Fingerprints<E = Dense> {
    polynomial: &'static Polynomial,
    generation: Option<u32>,
    values: E,
    // Shifts by 2^j zero bytes.
    powers: Vec<Box<ShiftTable>>,
    lengths: Vec<Box<ShiftTable>>,
    // The number of each length's table, or UNKNOWN_TABLE: by length up to SHORT_LENGTHS, which a
    // state's tails are found by once per state, and in a map past it.
    short_numbers: Vec<i32>,
    length_numbers: HashMap<u64, i32>,
}

const SHORT_LENGTHS: usize = 1 << 12;

impl Fingerprints {
    /// Fingerprints with the polynomial.
    pub fn new(polynomial: &'static Polynomial) -> Fingerprints {
        Fingerprints::with_entries(polynomial)
    }

    /// Lends the fingerprints computed so far to the caches of a parallel level's threads, until
    /// [`Fingerprints::take_back`].
    pub fn share(&mut self) -> SharedFingerprints {
        SharedFingerprints(Arc::new(std::mem::take(&mut self.values.0)))
    }

    /// Takes back what [`Fingerprints::share`] lent, once the threads' caches let go of it.
    pub fn take_back(&mut self, shared: SharedFingerprints) {
        self.values.0 = Arc::into_inner(shared.0).expect("the fingerprints, once threads let go");
    }

    /// Adds what a thread's cache computed: the fingerprints of the store's values it computed,
    /// and of its own values, which `imported` gives the ids of in the store, by their position
    /// among them. What a value's fingerprint is doesn't depend on which cache computed it.
    pub fn absorb(&mut self, overlay: &Fingerprints<Overlaid>, imported: &[Id]) {
        let entries = &overlay.values;
        let own = imported
            .iter()
            .copied()
            .zip(&entries.values)
            .filter(|&(id, _)| id != EMPTY_SLOT);
        let misses = entries.misses.iter().map(|(&id, entry)| (id, entry));
        for (id, entry) in own.chain(misses) {
            if !entry.is_computed || self.values.is_computed(id) {
                continue;
            }
            // A length table's number is the thread's cache's own.
            self.values.set(
                id,
                ValueFingerprint {
                    table: UNKNOWN_TABLE,
                    ..*entry
                },
            );
        }
    }
}

impl Fingerprints<Overlaid> {
    /// Makes this the cache of a thread whose overlay is laid on a store of `bound` values, whose
    /// fingerprints so far are `shared`, forgetting what it computed before.
    pub fn attach(&mut self, shared: &SharedFingerprints, bound: Id) {
        self.values.clear();
        self.values.bound = bound;
        self.values.base = Some(Arc::clone(&shared.0));
    }

    /// Lets go of what [`Fingerprints::attach`] lent, keeping what this cache computed.
    pub fn detach(&mut self) {
        self.values.base = None;
    }
}

impl<E: Entries> Fingerprints<E> {
    /// Fingerprints with the polynomial, which keep the entries of values in `E`.
    pub fn with_entries(polynomial: &'static Polynomial) -> Fingerprints<E> {
        Fingerprints {
            polynomial,
            generation: None,
            values: E::default(),
            powers: Vec::new(),
            lengths: Vec::new(),
            short_numbers: Vec::new(),
            length_numbers: HashMap::new(),
        }
    }

    pub fn polynomial(&self) -> &'static Polynomial {
        self.polynomial
    }

    /// Forgets every value's fingerprint, as `resetFingerprints` does. The fingerprints also
    /// forget them when the store they were computed from is reset.
    pub fn reset(&mut self) {
        self.values.clear();
    }

    /// Forgets the fingerprints of the values from this id on, which an overlay has let go of.
    pub fn forget_from(&mut self, id: Id) {
        self.values.truncate(id);
    }

    fn get_power(&mut self, exponent: usize) -> &ShiftTable {
        while self.powers.len() <= exponent {
            let table = match self.powers.last() {
                None => {
                    let polynomial = self.polynomial;
                    ShiftTable::build(|fingerprint| polynomial.extend_byte(fingerprint, 0))
                }
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
        self.get_table_under(length, MAXIMUM_LENGTH_TABLES)
    }

    // The number of the table that shifts by a length, made only while fewer than `cap` tables
    // exist, or NO_TABLE.
    fn get_table_under(&mut self, length: u64, cap: usize) -> i32 {
        let is_short = length < SHORT_LENGTHS as u64;
        let known = if is_short {
            self.short_numbers.get(length as usize).copied()
        } else {
            self.length_numbers.get(&length).copied()
        };
        if let Some(number) = known.filter(|&number| number != UNKNOWN_TABLE) {
            return number;
        }
        if self.lengths.len() >= cap {
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
        if is_short {
            self.short_numbers.resize(SHORT_LENGTHS, UNKNOWN_TABLE);
            self.short_numbers[length as usize] = number;
        } else {
            self.length_numbers.insert(length, number);
        }
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

    // Extends a fingerprint by a value whose F and length are known, with its table found once.
    fn extend_known(&mut self, fingerprint: u64, id: Id) -> u64 {
        let entry = self.values.entry(id);
        let number = if entry.table == UNKNOWN_TABLE {
            let number = self.get_length_table(entry.length);
            self.values.set_table(id, number);
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
    pub fn get_value(&mut self, store: &Store, id: Id) -> Outcome<(u64, u64)> {
        self.check_generation(store);
        self.compute(store, id)?;
        let entry = self.values.entry(id);
        Ok((entry.fingerprint, entry.length))
    }

    // Computes a value's F and length, its parts' first, without recursing: a value is computed
    // when it comes off the stack the second time, after the parts pushed above it.
    #[inline(always)]
    fn compute(&mut self, store: &Store, id: Id) -> Outcome<()> {
        // A value met before is known, as nearly every value of a generated state is.
        if self.values.is_computed(id) {
            return Ok(());
        }
        self.compute_new(store, id)
    }

    #[inline(never)]
    fn compute_new(&mut self, store: &Store, id: Id) -> Outcome<()> {
        let mut pending = vec![(id, false)];
        while let Some((top, is_expanded)) = pending.pop() {
            if self.values.is_computed(top) {
                continue;
            }
            if is_expanded {
                let computed = self.compute_one(store, top)?;
                self.values.set(top, computed);
                continue;
            }
            pending.push((top, true));
            Self::for_each_part(store, top, |part, _| {
                if let Some(part) = part {
                    pending.push((part, false));
                }
            });
        }
        Ok(())
    }

    fn compute_one(&mut self, store: &Store, id: Id) -> Outcome<ValueFingerprint> {
        let (fingerprint, length) = match store.kind_of(id) {
            KIND_BOOL => self.polynomial.of_bool(id == TRUE),
            KIND_INT => self.polynomial.of_int(store.int_of(id)),
            KIND_STRING => self.polynomial.of_string(store.text_of(id)),
            KIND_MODEL => self.polynomial.of_model(store.text_rank_of(id)),
            KIND_LAZY_FUNCTION | KIND_INFINITE_SET => return Err(UNFINGERPRINTABLE),
            kind @ (KIND_SET | KIND_FUNCTION | KIND_TUPLE) => {
                let tag = if kind == KIND_SET {
                    SET_ENUM_VALUE
                } else {
                    FCN_RCD_VALUE
                };
                let polynomial = self.polynomial;
                let mut fingerprint =
                    polynomial.extend_int(polynomial.extend_byte(0, tag), store.size_of(id) as i32);
                let mut length = 5;
                let mut parts = Vec::new();
                Self::for_each_part(store, id, |part, index| parts.push((part, index)));
                for (part, index) in parts {
                    match part {
                        Some(part) => {
                            fingerprint = self.extend_known(fingerprint, part);
                            length += self.values.entry(part).length;
                        }
                        None => {
                            fingerprint =
                                self.shift(fingerprint, 5) ^ polynomial.get_int(index as i32 + 1);
                            length += 5;
                        }
                    }
                }
                (fingerprint, length)
            }
            _ => return Err(UNFINGERPRINTABLE),
        };
        Ok(ValueFingerprint {
            fingerprint,
            length,
            table: UNKNOWN_TABLE,
            is_computed: true,
        })
    }

    /// F and length of a set outside a store, from those of its elements in TLC's order, or of a
    /// function, from those of each key and its value in turn.
    pub fn of_parts(&mut self, is_set: bool, parts: &[(u64, u64)]) -> (u64, u64) {
        let (tag, size) = if is_set {
            (SET_ENUM_VALUE, parts.len())
        } else {
            (FCN_RCD_VALUE, parts.len() / 2)
        };
        let polynomial = self.polynomial;
        let start = (
            polynomial.extend_int(polynomial.extend_byte(0, tag), size as i32),
            5,
        );
        parts
            .iter()
            .fold(start, |(fingerprint, length), &(part, part_length)| {
                (
                    self.shift(fingerprint, part_length) ^ part,
                    length + part_length,
                )
            })
    }

    /// TLC's fingerprint of a state outside a store, from F and length of its values in TLC's
    /// order.
    pub fn of_state(&mut self, values: &[(u64, u64)]) -> u64 {
        values
            .iter()
            .fold(self.polynomial.value, |fingerprint, &(value, length)| {
                self.shift(fingerprint, length) ^ value
            })
    }

    /// TLC's fingerprint of one state, its values read in `order`.
    pub fn get_state(&mut self, store: &Store, state: &[Id], order: &[usize]) -> Outcome<u64> {
        self.check_generation(store);
        order
            .iter()
            .try_fold(self.polynomial.value, |fingerprint, &index| {
                self.compute(store, state[index])?;
                Ok(self.extend_known(fingerprint, state[index]))
            })
    }

    /// The TLC fingerprints of states stored one after another, each `width` ids, read in
    /// `order`, as `getStateFingerprints` computes them.
    ///
    /// A state's fingerprint is `shift(P, L)` xor the xor over its values v_j of
    /// `shift(F(v_j), S_j)`, where P is the polynomial, L the length of all its values and S_j
    /// that of the values after v_j. Where a state differs from its parent only in values of the
    /// same lengths, L and every S_j are the parent's, so its fingerprint is the parent's xor
    /// `shift(F(v_j) ^ F(v'_j), S_j)` for each value that changed. An initial state, which has no
    /// parent, follows from the state before it in the same way.
    pub fn get_states(
        &mut self,
        store: &Store,
        states: &[Id],
        width: usize,
        order: &[usize],
        parents: Option<&[i32]>,
    ) -> Outcome<Vec<u64>> {
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
                )?
            } else {
                None
            };
            let fingerprint = match from_earlier {
                Some(fingerprint) => fingerprint,
                None => self.get_state(store, row, order)?,
            };
            fingerprints.push(fingerprint);
        }
        Ok(fingerprints)
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
    ) -> Outcome<Option<u64>> {
        let mut fingerprint = earlier_fingerprint;
        let mut tail = 0;
        for (position, &index) in order.iter().enumerate().rev() {
            let (id, earlier_id) = (row[index], earlier_row[index]);
            self.compute(store, id)?;
            if id != earlier_id {
                self.compute(store, earlier_id)?;
                let (value, earlier_value) = (self.values.entry(id), self.values.entry(earlier_id));
                if value.length != earlier_value.length {
                    return Ok(None);
                }
                if tails[position].0 != tail {
                    tails[position] = (tail, self.get_length_table(tail));
                }
                let changed = value.fingerprint ^ earlier_value.fingerprint;
                fingerprint ^= self.shift_by_table(tails[position].1, changed, tail);
            }
            tail += self.values.entry(id).length;
        }
        Ok(Some(fingerprint))
    }

    /// Makes `state`, its values read in `order` and its fingerprint `fingerprint`, the parent
    /// [`Fingerprints::get_child`] fingerprints successors from. `order` holds each of the
    /// state's positions once.
    pub fn set_parent(
        &mut self,
        store: &Store,
        state: &[Id],
        order: &[usize],
        fingerprint: u64,
        parent: &mut Parent,
    ) -> Outcome<()> {
        self.check_generation(store);
        parent.fingerprint = fingerprint;
        parent.positions.resize(state.len(), 0);
        parent.tails.resize(order.len(), (u64::MAX, NO_TABLE));
        parent.prefixes.clear();
        parent.prefixes.push(self.polynomial.value);
        let mut tail = 0;
        for (position, &index) in order.iter().enumerate().rev() {
            parent.positions[index] = position;
            // A tail seldom changes from one parent to the next, so its table is looked up again
            // only when it does.
            // Tails can take any length, and a model whose values grow can meet a new one at nearly
            // every state: they make tables only up to half the cap, so the values' own lengths
            // keep theirs, and a successor that needs a tail without one is fingerprinted from
            // the parent's prefix.
            if parent.tails[position].0 != tail {
                let table = self.get_table_under(tail, MAXIMUM_LENGTH_TABLES / 2);
                parent.tails[position] = (tail, table);
            }
            self.compute(store, state[index])?;
            tail += self.values.entry(state[index]).length;
        }
        Ok(())
    }

    /// The fingerprint of a successor of the parent [`Fingerprints::set_parent`] last set, from
    /// the parent's: for each value that changed, one shift by the length of the values after it
    /// where every changed value keeps its length and that length has a table (as
    /// [`Fingerprints::get_states`] computes it), and otherwise the parent's fingerprint before the first value that changed, extended by
    /// the successor's values from there.
    pub fn get_child(
        &mut self,
        store: &Store,
        parent: &mut Parent,
        parent_state: &[Id],
        state: &[Id],
        order: &[usize],
    ) -> Outcome<u64> {
        self.check_generation(store);
        let mut fingerprint = parent.fingerprint;
        let mut first = order.len();
        let mut is_in_place = true;
        for (index, (&id, &parent_id)) in state.iter().zip(parent_state).enumerate() {
            if id == parent_id {
                continue;
            }
            let position = parent.positions[index];
            first = first.min(position);
            self.compute(store, id)?;
            self.compute(store, parent_id)?;
            let (value, parent_value) = (self.values.entry(id), self.values.entry(parent_id));
            let (tail, table) = parent.tails[position];
            is_in_place &= value.length == parent_value.length && table != NO_TABLE;
            if is_in_place {
                let changed = value.fingerprint ^ parent_value.fingerprint;
                fingerprint ^= self.shift_by_table(table, changed, tail);
            }
        }
        if is_in_place {
            return Ok(fingerprint);
        }
        while parent.prefixes.len() <= first {
            let position = parent.prefixes.len() - 1;
            let prefix =
                self.extend_known(parent.prefixes[position], parent_state[order[position]]);
            parent.prefixes.push(prefix);
        }
        Ok(order[first..]
            .iter()
            .fold(parent.prefixes[first], |fingerprint, &index| {
                self.extend_known(fingerprint, state[index])
            }))
    }

    /// The fingerprints extended over every value of every state, which
    /// `PROVE_IT_FINGERPRINT=reference` takes.
    pub fn get_states_reference(
        &mut self,
        store: &Store,
        states: &[Id],
        width: usize,
        order: &[usize],
    ) -> Outcome<Vec<u64>> {
        self.check_generation(store);
        if width == 0 {
            return Ok(Vec::new());
        }
        states
            .chunks_exact(width)
            .map(|row| {
                order
                    .iter()
                    .try_fold(self.polynomial.value, |fingerprint, &index| {
                        let (value, length) = self.get_value(store, row[index])?;
                        Ok(self.shift_by_powers(fingerprint, length) ^ value)
                    })
            })
            .collect()
    }
}
