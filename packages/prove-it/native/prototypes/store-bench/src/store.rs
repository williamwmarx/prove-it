// A port of the core of src/engine/store.ts: the same layout (structure of arrays, an int32 heap of
// blocks, an open-addressed [hash, id] table), the same hash functions and the same allocation
// order, so the same operations give the same ids as the TypeScript store.
use std::collections::HashMap;

pub const KIND_BOOL: u8 = 0;
pub const KIND_INT: u8 = 1;
pub const KIND_STRING: u8 = 2;
pub const KIND_MODEL: u8 = 3;
pub const KIND_SET: u8 = 4;
pub const KIND_FUNCTION: u8 = 5;
pub const KIND_TUPLE: u8 = 6;

pub type Id = i32;
pub const FALSE: Id = 0;
pub const TRUE: Id = 1;
pub const EMPTY_SET: Id = 2;
pub const EMPTY_TUPLE: Id = 3;
const SMALL_INT_MIN: i32 = -256;
const SMALL_INT_MAX: i32 = 4096;
const INITIAL_CAPACITY: usize = 1 << 12;

#[inline(always)]
fn imul(a: i32, b: u32) -> i32 { a.wrapping_mul(b as i32) }
#[inline(always)]
fn ushr(a: i32, n: u32) -> i32 { ((a as u32) >> n) as i32 }
#[inline(always)]
fn mix(hash: i32) -> i32 {
    let first = imul(hash ^ ushr(hash, 16), 0x7feb352d);
    let second = imul(first ^ ushr(first, 15), 0x846ca68b);
    second ^ ushr(second, 16)
}

#[derive(Debug)]
pub struct Bail(pub &'static str);

pub struct RecordShape { pub keys: Vec<Id>, pub prefix: i32 }

pub struct Store {
    kinds: Vec<u8>,
    payloads: Vec<i32>,
    sizes: Vec<i32>,
    hashes: Vec<i32>,
    heap: Vec<i32>,
    table: Vec<i32>,
    mask: usize,
    pub texts: Vec<String>,
    text_ranks: Vec<i32>,
    string_ids: HashMap<String, Id>,
    ranks: HashMap<String, i32>,
    small_ints: Vec<Id>,
    scratch: Vec<i32>,
}

impl Store {
    pub fn new(order: &[&str]) -> Store {
        let mut store = Store {
            kinds: Vec::with_capacity(INITIAL_CAPACITY),
            payloads: Vec::with_capacity(INITIAL_CAPACITY),
            sizes: Vec::with_capacity(INITIAL_CAPACITY),
            hashes: Vec::with_capacity(INITIAL_CAPACITY),
            heap: Vec::with_capacity(1 << 16),
            table: vec![-1; INITIAL_CAPACITY * 4],
            mask: INITIAL_CAPACITY * 2 - 1,
            texts: vec![],
            text_ranks: vec![],
            string_ids: HashMap::new(),
            ranks: order.iter().enumerate().map(|(i, t)| (t.to_string(), i as i32)).collect(),
            small_ints: vec![],
            scratch: vec![0; 64],
        };
        store.intern_scalar(KIND_BOOL, 0);
        store.intern_scalar(KIND_BOOL, 1);
        store.intern_block_from_scratch(KIND_SET, 0, 0);
        store.intern_block_from_scratch(KIND_TUPLE, 0, 0);
        for value in SMALL_INT_MIN..=SMALL_INT_MAX {
            let id = store.intern_scalar(KIND_INT, value);
            store.small_ints.push(id);
        }
        store
    }

    pub fn count(&self) -> usize { self.kinds.len() }
    #[inline(always)] pub fn kind(&self, id: Id) -> u8 { unsafe { *self.kinds.get_unchecked(id as usize) } }
    #[inline(always)] pub fn size(&self, id: Id) -> i32 { unsafe { *self.sizes.get_unchecked(id as usize) } }
    #[inline(always)] fn payload(&self, id: Id) -> i32 { unsafe { *self.payloads.get_unchecked(id as usize) } }
    #[inline(always)] fn word(&self, at: i32) -> i32 { unsafe { *self.heap.get_unchecked(at as usize) } }

    fn grow_table(&mut self) {
        let mut next = vec![-1; self.table.len() * 2];
        let mask = next.len() / 2 - 1;
        for id in 0..self.kinds.len() {
            let hash = self.hashes[id];
            let mut slot = hash as usize & mask;
            while next[2 * slot + 1] != -1 { slot = (slot + 1) & mask; }
            next[2 * slot] = hash;
            next[2 * slot + 1] = id as i32;
        }
        self.table = next;
        self.mask = mask;
    }

    fn allocate(&mut self, kind: u8, payload: i32, size: i32, hash: i32, slot: usize) -> Id {
        let id = self.kinds.len() as Id;
        self.kinds.push(kind);
        self.payloads.push(payload);
        self.sizes.push(size);
        self.hashes.push(hash);
        self.table[2 * slot] = hash;
        self.table[2 * slot + 1] = id;
        if self.kinds.len() * 4 > self.table.len() { self.grow_table(); }
        id
    }

    fn intern_scalar(&mut self, kind: u8, payload: i32) -> Id {
        let hash = mix(imul(kind as i32 + 1, 0x9e3779b1) ^ payload);
        let mut slot = hash as usize & self.mask;
        loop {
            let id = self.table[2 * slot + 1];
            if id == -1 { return self.allocate(kind, payload, 0, hash, slot); }
            if self.table[2 * slot] == hash && self.kind(id) == kind && self.payload(id) == payload && self.size(id) == 0 { return id; }
            slot = (slot + 1) & self.mask;
        }
    }

    fn block_hash(kind: u8, words: &[i32], size: i32) -> i32 {
        let mut hash = imul(kind as i32 + 7, 0x9e3779b1) ^ size;
        for &word in words { hash = imul(hash ^ word, 0x01000193); }
        hash
    }

    // Interns scratch[0..length).
    fn intern_block_from_scratch(&mut self, kind: u8, length: usize, size: i32) -> Id {
        let hash = mix(Self::block_hash(kind, &self.scratch[..length], size));
        let mut slot = hash as usize & self.mask;
        loop {
            let id = self.table[2 * slot + 1];
            if id == -1 {
                let offset = self.heap.len() as i32;
                self.heap.extend_from_slice(&self.scratch[..length]);
                return self.allocate(kind, offset, size, hash, slot);
            }
            if self.table[2 * slot] == hash && self.kind(id) == kind && self.size(id) == size {
                let offset = self.payload(id) as usize;
                if self.heap[offset..offset + length] == self.scratch[..length] { return id; }
            }
            slot = (slot + 1) & self.mask;
        }
    }

    fn take_scratch(&mut self, length: usize) {
        if self.scratch.len() < length { self.scratch.resize(2 * length, 0); }
    }

    pub fn int(&mut self, value: i32) -> Id {
        if (SMALL_INT_MIN..=SMALL_INT_MAX).contains(&value) { return self.small_ints[(value - SMALL_INT_MIN) as usize]; }
        self.intern_scalar(KIND_INT, value)
    }

    pub fn str(&mut self, text: &str) -> Id {
        if let Some(&id) = self.string_ids.get(text) { return id; }
        let index = self.texts.len() as i32;
        self.texts.push(text.to_string());
        self.text_ranks.push(*self.ranks.get(text).unwrap_or(&-1));
        let id = self.intern_scalar(KIND_STRING, index);
        self.string_ids.insert(text.to_string(), id);
        id
    }

    // TLC's Value#compareTo, for the kinds this workload builds.
    pub fn compare(&self, left: Id, right: Id) -> Result<i32, Bail> {
        if left == right { return Ok(0); }
        let (lk, rk) = (self.kind(left), self.kind(right));
        if lk != rk {
            let is_fn = |k| k == KIND_FUNCTION || k == KIND_TUPLE;
            return if is_fn(lk) && is_fn(rk) { self.compare_functions(left, right) } else { Err(Bail("values TLC can't compare")) };
        }
        match lk {
            KIND_INT => Ok(if self.payload(left) < self.payload(right) { -1 } else { 1 }),
            KIND_BOOL => Ok(if left < right { -1 } else { 1 }),
            KIND_STRING => {
                let (a, b) = (self.payload(left) as usize, self.payload(right) as usize);
                let (ra, rb) = (self.text_ranks[a], self.text_ranks[b]);
                Ok(if ra != -1 && rb != -1 { ra - rb } else if ra != -1 { -1 } else if rb != -1 { 1 } else if self.texts[a] < self.texts[b] { -1 } else { 1 })
            }
            KIND_SET => {
                let size = self.size(left);
                if size != self.size(right) { return Ok(size - self.size(right)); }
                let (lo, ro) = (self.payload(left), self.payload(right));
                for index in 0..size {
                    let comparison = self.compare(self.word(lo + index), self.word(ro + index))?;
                    if comparison != 0 { return Ok(comparison); }
                }
                Ok(0)
            }
            _ => self.compare_functions(left, right),
        }
    }

    pub fn key(&self, function: Id, index: i32) -> Id {
        if self.kind(function) == KIND_TUPLE { self.small_ints[(index + 1 - SMALL_INT_MIN) as usize] } else { self.word(self.payload(function) + index) }
    }
    pub fn range_value(&self, function: Id, index: i32) -> Id {
        if self.kind(function) == KIND_TUPLE { self.word(self.payload(function) + index) } else { self.word(self.payload(function) + self.size(function) + index) }
    }

    fn compare_functions(&self, left: Id, right: Id) -> Result<i32, Bail> {
        let size = self.size(left);
        if size != self.size(right) { return Ok(size - self.size(right)); }
        for index in 0..size {
            let comparison = self.compare(self.key(left, index), self.key(right, index))?;
            if comparison != 0 { return Ok(comparison); }
        }
        for index in 0..size {
            let comparison = self.compare(self.range_value(left, index), self.range_value(right, index))?;
            if comparison != 0 { return Ok(comparison); }
        }
        Ok(0)
    }

    pub fn set_of(&mut self, elements: &[Id]) -> Result<Id, Bail> {
        let length = elements.len();
        if length == 0 { return Ok(EMPTY_SET); }
        self.take_scratch(length);
        self.scratch[..length].copy_from_slice(elements);
        let mut is_sorted = true;
        for index in 1..length {
            if self.compare(elements[index - 1], elements[index])? >= 0 { is_sorted = false; break; }
        }
        if is_sorted { return Ok(self.intern_block_from_scratch(KIND_SET, length, length as i32)); }
        // Insertion sort, as store.ts sorts a short block.
        for index in 1..length {
            let word = self.scratch[index];
            let mut position = index;
            while position > 0 && self.compare(self.scratch[position - 1], word)? > 0 {
                self.scratch[position] = self.scratch[position - 1];
                position -= 1;
            }
            self.scratch[position] = word;
        }
        let mut unique = 1;
        for index in 1..length {
            if self.scratch[index] != self.scratch[unique - 1] { self.scratch[unique] = self.scratch[index]; unique += 1; }
        }
        Ok(self.intern_block_from_scratch(KIND_SET, unique, unique as i32))
    }

    pub fn with_element(&mut self, set: Id, element: Id) -> Result<Id, Bail> {
        let size = self.size(set) as usize;
        let offset = self.payload(set) as usize;
        self.take_scratch(size + 1);
        let mut length = 0;
        let mut is_inserted = false;
        for index in 0..size {
            let current = self.heap[offset + index];
            if current == element { return Ok(set); }
            if !is_inserted && self.compare(element, current)? < 0 { self.scratch[length] = element; length += 1; is_inserted = true; }
            self.scratch[length] = current;
            length += 1;
        }
        if !is_inserted { self.scratch[length] = element; length += 1; }
        Ok(self.intern_block_from_scratch(KIND_SET, length, length as i32))
    }

    pub fn function_of_sorted(&mut self, domain: &[Id], range: &[Id]) -> Id {
        let size = domain.len();
        self.take_scratch(2 * size);
        self.scratch[..size].copy_from_slice(domain);
        self.scratch[size..2 * size].copy_from_slice(range);
        self.intern_block_from_scratch(KIND_FUNCTION, 2 * size, size as i32)
    }

    pub fn record_shape(&self, keys: &[Id]) -> RecordShape {
        let mut hash = imul(KIND_FUNCTION as i32 + 7, 0x9e3779b1) ^ keys.len() as i32;
        for &key in keys { hash = imul(hash ^ key, 0x01000193); }
        RecordShape { keys: keys.to_vec(), prefix: hash }
    }

    // Looked up in place against the shape's keys and the values, copied only when new.
    pub fn record_of(&mut self, shape: &RecordShape, values: &[Id]) -> Id {
        let size = shape.keys.len();
        let mut unmixed = shape.prefix;
        for &value in values { unmixed = imul(unmixed ^ value, 0x01000193); }
        let hash = mix(unmixed);
        let mut slot = hash as usize & self.mask;
        loop {
            let id = self.table[2 * slot + 1];
            if id == -1 {
                let offset = self.heap.len() as i32;
                self.heap.extend_from_slice(&shape.keys);
                self.heap.extend_from_slice(values);
                return self.allocate(KIND_FUNCTION, offset, size as i32, hash, slot);
            }
            if self.table[2 * slot] == hash && self.kind(id) == KIND_FUNCTION && self.size(id) == size as i32 {
                let other = self.payload(id) as usize;
                if self.heap[other + size..other + 2 * size] == *values && self.heap[other..other + size] == *shape.keys { return id; }
            }
            slot = (slot + 1) & self.mask;
        }
    }

    fn find_key(&self, function: Id, key: Id) -> i32 {
        let size = self.size(function);
        let offset = self.payload(function);
        for index in 0..size { if self.word(offset + index) == key { return index; } }
        -1
    }

    // [fn EXCEPT ![key] = value], hashed and looked up in place as internPatched does.
    pub fn except(&mut self, function: Id, key: Id, value: Id) -> Result<Id, Bail> {
        let kind = self.kind(function);
        let position = self.find_key(function, key);
        if position == -1 { return Err(Bail("EXCEPT outside the domain")); }
        let size = self.size(function);
        let offset = self.payload(function) as usize;
        let index = (if kind == KIND_TUPLE { position } else { size + position }) as usize;
        if self.heap[offset + index] == value { return Ok(function); }
        let length = if kind == KIND_TUPLE { size as usize } else { 2 * size as usize };
        let mut unmixed = imul(kind as i32 + 7, 0x9e3779b1) ^ size;
        for at in 0..length {
            let word = if at == index { value } else { self.heap[offset + at] };
            unmixed = imul(unmixed ^ word, 0x01000193);
        }
        let hash = mix(unmixed);
        let mut slot = hash as usize & self.mask;
        loop {
            let id = self.table[2 * slot + 1];
            if id == -1 {
                let start = self.heap.len();
                self.heap.extend_from_within(offset..offset + length);
                self.heap[start + index] = value;
                return Ok(self.allocate(kind, start as i32, size, hash, slot));
            }
            if self.table[2 * slot] == hash && self.kind(id) == kind && self.size(id) == size {
                let other = self.payload(id) as usize;
                let heap = &self.heap;
                if heap[other + index] == value && heap[other..other + index] == heap[offset..offset + index]
                    && heap[other + index + 1..other + length] == heap[offset + index + 1..offset + length] { return Ok(id); }
            }
            slot = (slot + 1) & self.mask;
        }
    }

    pub fn append_tuple(&mut self, tuple: Id, element: Id) -> Id {
        let size = self.size(tuple) as usize;
        let offset = self.payload(tuple) as usize;
        self.take_scratch(size + 1);
        for index in 0..size { self.scratch[index] = self.heap[offset + index]; }
        self.scratch[size] = element;
        self.intern_block_from_scratch(KIND_TUPLE, size + 1, size as i32 + 1)
    }
}

// TLC's fingerprint of each interned value, as F(v) (FP64 extended from zero by v's bytes) and |v|,
// computed once per id, so a state's fingerprint is a shift and an xor per variable.
pub struct ValueFingerprints { pub f: Vec<u64>, pub len: Vec<u32>, done: Vec<bool> }

impl ValueFingerprints {
    pub fn new() -> Self { ValueFingerprints { f: vec![], len: vec![], done: vec![] } }
    pub fn get(&mut self, fp: &crate::fp::Fp64, shifts: &mut Shifts, store: &Store, id: Id) -> (u64, u32) {
        let index = id as usize;
        if index >= self.done.len() { let n = (index + 1).max(self.done.len() * 2); self.f.resize(n, 0); self.len.resize(n, 0); self.done.resize(n, false); }
        if self.done[index] { return (self.f[index], self.len[index]); }
        let kind = store.kind(id);
        let (mut f, mut len) = (0u64, 0u32);
        match kind {
            KIND_BOOL => { f = fp.byte(fp.byte(0, 0), if id == TRUE { 116 } else { 102 }); len = 2; }
            KIND_INT => { f = fp.int(fp.byte(0, 1), store.payload(id)); len = 5; }
            KIND_STRING => {
                let text = &store.texts[store.payload(id) as usize];
                f = fp.int(fp.byte(0, 3), text.len() as i32);
                for byte in text.bytes() { f = fp.byte(f, byte); }
                len = 5 + text.len() as u32;
            }
            KIND_SET => {
                f = fp.int(fp.byte(0, 5), store.size(id)); len = 5;
                for index in 0..store.size(id) {
                    let element = store.word(store.payload(id) + index);
                    let (ef, el) = self.get(fp, shifts, store, element);
                    f = shifts.shift(fp, f, el) ^ ef; len += el;
                }
            }
            _ => {
                f = fp.int(fp.byte(0, 9), store.size(id)); len = 5;
                for index in 0..store.size(id) {
                    for part in [store.key(id, index), store.range_value(id, index)] {
                        let (ef, el) = self.get(fp, shifts, store, part);
                        f = shifts.shift(fp, f, el) ^ ef; len += el;
                    }
                }
            }
        }
        self.f[index] = f; self.len[index] = len; self.done[index] = true;
        (f, len)
    }
}

// Shifting a fingerprint by n zero bytes is linear over GF(2), so a table per n holds the shift of
// each byte at each of the eight positions.
pub struct Shifts { tables: std::collections::HashMap<u32, Box<[[u64; 256]; 8]>> }
impl Shifts {
    pub fn new() -> Self { Shifts { tables: Default::default() } }
    #[inline(always)]
    pub fn shift(&mut self, fp: &crate::fp::Fp64, value: u64, n: u32) -> u64 {
        let table = self.tables.entry(n).or_insert_with(|| {
            let mut table = Box::new([[0u64; 256]; 8]);
            for position in 0..8 {
                for bit in 0..8 {
                    let mut x: u64 = 1 << (8 * position + bit);
                    for _ in 0..n { x = fp.byte(x, 0); }
                    for byte in 0..256usize { if byte & (1 << bit) != 0 { table[position][byte] ^= x; } }
                }
            }
            table
        });
        let mut result = 0;
        for position in 0..8 { result ^= table[position][((value >> (8 * position)) & 0xff) as usize]; }
        result
    }
}
