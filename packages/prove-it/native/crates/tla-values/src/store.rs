//! A hash-consed store of TLA+ values, ported from `src/engine/store.ts` without its shared mode.
//! Every finite value is interned once and named by its id, so equal values have equal ids.
//! Composite values keep their elements in TLC's order.
//!
//! The store hashes and allocates exactly as the TypeScript store does, so the same operations in
//! the same order give the same ids, and it stops (a [`Bail`]) for the same reasons in the same
//! places. Texts are UTF-16, as JavaScript's strings are, since TLC's order compares unranked
//! strings by their code units and its fingerprints read them.

use std::collections::HashMap;
use std::mem::take;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

mod shapes;

/// The name of an interned value.
pub type Id = u32;

pub const KIND_BOOL: u8 = 0;
pub const KIND_INT: u8 = 1;
pub const KIND_STRING: u8 = 2;
pub const KIND_MODEL: u8 = 3;
pub const KIND_SET: u8 = 4;
/// A function whose domain isn't 1..n, records included. Its block holds the domain in TLC's
/// order, then the range.
pub const KIND_FUNCTION: u8 = 5;
/// A function with domain 1..n, the empty function included. Its block holds the range.
pub const KIND_TUPLE: u8 = 6;
/// A function TLC keeps lazy (`FcnLambdaValue`), over a domain it can't enumerate: its payload
/// numbers it among those the machine that built it keeps, which apply it. The store can't
/// compare, fingerprint or print one, as TLC can't without enumerating its domain.
pub const KIND_LAZY_FUNCTION: u8 = 7;

/// Nat, Int or STRING held as a value, as an element of a set is (TLC's `UserValue`): its payload
/// is [`NAT`], [`INT`] or [`STRINGS`]. The store tests membership in one and compares two as TLC
/// does. It can't fingerprint or print one, as TLC can't.
pub const KIND_INFINITE_SET: u8 = 8;
pub const NAT: i32 = 0;
pub const INT: i32 = 1;
pub const STRINGS: i32 = 2;

/// Why the store stops at a function TLC keeps lazy, an engine limit.
pub const LAZY_FUNCTION: Bail = Bail("unsupported: comparing a function TLC keeps lazy");

pub const FALSE: Id = 0;
pub const TRUE: Id = 1;
pub const EMPTY_SET: Id = 2;
pub const EMPTY_TUPLE: Id = 3;

/// Where the store meets something TLC reports as an error, or the engine doesn't handle, with
/// the TypeScript store's reason, word for word.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Bail(pub &'static str);

pub type Outcome<T> = Result<T, Bail>;

const SMALL_INT_MIN: i32 = -256;
pub(crate) const SMALL_INT_MAX: i32 = 4096;
const INITIAL_CAPACITY: usize = 1 << 12;
// Each store's number, which an overlay keeps of the store it copied.
static STORES: AtomicU64 = AtomicU64::new(0);
pub(crate) const EMPTY_SLOT: Id = Id::MAX;
// A short sort runs by insertion, in place; longer ones are merged from such runs.
const INSERTION_LENGTH: usize = 16;
// Blocks this small are searched in order. A larger one is in TLC's order and searched by halving.
const LINEAR_SIZE: usize = 16;
// A set this small whose elements compare without failing is scanned for an id.
const SCANNED_SIZE: usize = 256;

// A function whose keys are all strings, which TLC compares only with another record.
const IS_RECORD: u8 = 1;
// A block whose first words are a run of consecutive integers, such as 0..n, by its first and
// last: a set's elements, a function's domain or a tuple's elements.
const IS_INT_RUN: u8 = 2;
// Whether a set, tuple or function holds, at any depth, a function TLC keeps lazy, which TLC
// builds to compare: the store's equal ids say nothing of it.
const HOLDS_LAZY: u8 = 4;

/// What the store keeps of each id: one 16-byte read finds its kind, size and payload.
#[derive(Clone, Copy)]
#[repr(C)]
struct Meta {
    kind: u8,
    flags: u8,
    size: u32,
    // An integer's value, a text's index, or the offset of a composite value's block in the heap.
    payload: i32,
    hash: u32,
}

struct Text {
    units: Box<[u16]>,
    // TLC's rank of the text when it was interned, or -1.
    rank: i32,
    // For a model value named like A_x, its type's character, or 0.
    model_type: u16,
}

/// The fixed fields of a record constructor: its keys, sorted, and the hash of the block up to
/// them, so building a record hashes only its values.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecordShape {
    pub keys: Vec<Id>,
    prefix: u32,
}

/// TLC's order of strings and model value names, which it ranks by when it first interns them:
/// `setStringOrder`, `rankString` and `getStringRank` in `src/values.ts`.
#[derive(Default)]
struct StringOrder {
    ranks: HashMap<Box<[u16]>, i32>,
}

impl StringOrder {
    fn rank(&mut self, text: &[u16]) -> i32 {
        let size = self.ranks.len() as i32;
        *self.ranks.entry(text.into()).or_insert(size)
    }
}

#[inline(always)]
fn imul(left: u32, right: u32) -> u32 {
    left.wrapping_mul(right)
}

#[inline(always)]
fn mix(hash: u32) -> u32 {
    let first = imul(hash ^ (hash >> 16), 0x7feb352d);
    let second = imul(first ^ (first >> 15), 0x846ca68b);
    second ^ (second >> 16)
}

#[inline(always)]
fn seed(kind: u8, size: u32) -> u32 {
    imul(kind as u32 + 7, 0x9e3779b1) ^ size
}

#[inline(always)]
fn fold(hash: u32, word: u32) -> u32 {
    imul(hash ^ word, 0x01000193)
}

fn get_model_type(units: &[u16]) -> u16 {
    if units.len() > 2 && units[1] == u16::from(b'_') {
        units[0]
    } else {
        0
    }
}

/// A store, or an overlay on a store that another holds: a worker of a parallel search interns
/// in an overlay of its own while the store under it doesn't change, and finds a value the store
/// under it holds by that value's id there, so each value still has one id. An overlay keeps a copy
/// of the base's values, blocks and texts, extended by what the base added each time it is laid on
/// again, and numbers its own after them: it reads an id, a block's offset or a text's index as a
/// store of its own does, and looks a value up in the base's tables and then in its own.
pub struct Store {
    base: Option<Arc<Store>>,
    // Where the overlay's own values, blocks and texts start, past its copy of the base's: the
    // base's counts when it was last laid on, and 0 for a store of its own.
    id_base: u32,
    heap_base: usize,
    text_base: usize,
    serial: u64,
    // The number and generation of the store whose values the overlay copied.
    copied: Option<(u64, u32)>,
    meta: Vec<Meta>,
    heap: Vec<u32>,
    // The intern table: a hash and an id per slot, an id of EMPTY_SLOT marking an empty one.
    table: Vec<[u32; 2]>,
    mask: usize,
    texts: Vec<Text>,
    string_ids: HashMap<Box<[u16]>, Id>,
    model_ids: HashMap<Box<[u16]>, Id>,
    order: StringOrder,
    // The first rank of the strings ranked since `freeze_string_order`, which aren't ordered.
    unordered_rank: i32,
    small_ints: Vec<Id>,
    generation: u32,
    scratch: Vec<u32>,
    sort_scratch: Vec<u32>,
    pair_scratch: Vec<u32>,
    // The words an EXCEPT changes in a block: their indexes, ascending, and their new values.
    patch_indexes: Vec<u32>,
    patch_values: Vec<u32>,
    shapes: shapes::Shapes,
}

impl Default for Store {
    fn default() -> Self {
        Self::new()
    }
}

impl Store {
    /// A store reset with no strings ranked.
    pub fn new() -> Store {
        let mut store = Store::empty();
        store.reset(std::iter::empty::<&[u16]>());
        store
    }

    fn empty() -> Store {
        Store {
            base: None,
            id_base: 0,
            heap_base: 0,
            text_base: 0,
            serial: STORES.fetch_add(1, Ordering::Relaxed),
            copied: None,
            meta: Vec::with_capacity(INITIAL_CAPACITY),
            heap: Vec::with_capacity(1 << 16),
            table: vec![[0, EMPTY_SLOT]; INITIAL_CAPACITY * 2],
            mask: INITIAL_CAPACITY * 2 - 1,
            texts: Vec::new(),
            string_ids: HashMap::new(),
            model_ids: HashMap::new(),
            order: StringOrder::default(),
            unordered_rank: i32::MAX,
            small_ints: Vec::with_capacity((SMALL_INT_MAX - SMALL_INT_MIN + 1) as usize),
            generation: 0,
            scratch: vec![0; 64],
            sort_scratch: vec![0; 64],
            pair_scratch: vec![0; 64],
            patch_indexes: vec![0; 16],
            patch_values: vec![0; 16],
            shapes: shapes::Shapes::default(),
        }
    }

    /// An overlay on a store, which interns what the store doesn't hold while the store doesn't
    /// change: each thread of a parallel search evaluates in one of its own.
    pub fn overlay(base: Arc<Store>) -> Store {
        let mut store = Store::empty();
        store.attach(base);
        store
    }

    /// Lays an overlay on a store again, forgetting the values it held: its ids name the store's
    /// values from now on. A store only adds values until it is reset, so an overlay laid again on
    /// the store it was last laid on copies only what the store added since.
    pub fn attach(&mut self, base: Arc<Store>) {
        assert!(base.base.is_none(), "an overlay laid on an overlay");
        let (values, words, texts) = if self.copied == Some((base.serial, base.generation)) {
            (self.id_base as usize, self.heap_base, self.text_base)
        } else {
            (0, 0, 0)
        };
        self.meta.truncate(values);
        self.shapes.forget_from(values as Id);
        self.meta.extend_from_slice(&base.meta[values..]);
        self.heap.truncate(words);
        self.heap.extend_from_slice(&base.heap[words..]);
        self.texts.truncate(texts);
        self.texts
            .extend(base.texts[texts..].iter().map(|text| Text {
                units: text.units.clone(),
                rank: text.rank,
                model_type: text.model_type,
            }));
        self.id_base = base.meta.len() as Id;
        self.heap_base = base.heap.len();
        self.text_base = base.texts.len();
        self.generation = base.generation;
        self.copied = Some((base.serial, base.generation));
        self.small_ints.clone_from(&base.small_ints);
        self.table.fill([0, EMPTY_SLOT]);
        self.string_ids.clear();
        self.model_ids.clear();
        self.base = Some(base);
    }

    /// Lets go of the store under an overlay, keeping the overlay's own values to import.
    pub fn detach(&mut self) {
        self.base = None;
    }

    /// The id here of a value of an overlay laid on this store, which the overlay may have let go
    /// of: the overlay's own values are interned here, parts first, and `imported` keeps the id
    /// each was given, by its position among them.
    pub fn import(&mut self, overlay: &Store, id: Id, imported: &mut Vec<Id>) -> Id {
        let Some(index) = id.checked_sub(overlay.id_base).map(|index| index as usize) else {
            return id;
        };
        if let Some(&known) = imported.get(index).filter(|&&known| known != EMPTY_SLOT) {
            return known;
        }
        let meta = overlay.meta[id as usize];
        let text = || &overlay.texts[meta.payload as usize].units;
        let value = match meta.kind {
            KIND_STRING => self.str(text()),
            KIND_MODEL => self.model(text()),
            KIND_SET | KIND_FUNCTION | KIND_TUPLE => {
                let length = meta.size as usize * if meta.kind == KIND_FUNCTION { 2 } else { 1 };
                let words: Vec<Id> = overlay.heap[meta.payload as usize..][..length]
                    .iter()
                    .map(|&word| self.import(overlay, word, imported))
                    .collect();
                self.intern_block(meta.kind, &words, meta.size)
            }
            KIND_BOOL | KIND_INT | KIND_LAZY_FUNCTION | KIND_INFINITE_SET => {
                self.intern_scalar(meta.kind, meta.payload)
            }
            kind => unreachable!("an overlay holds a value of no kind the store makes: {kind}"),
        };
        if imported.len() <= index {
            imported.resize(overlay.meta.len() - overlay.id_base as usize, EMPTY_SLOT);
        }
        imported[index] = value;
        value
    }

    /// Empties the store and ranks the given texts, in order, as `setStringOrder` and then
    /// `resetStore` do.
    pub fn reset<'a>(&mut self, order: impl IntoIterator<Item = &'a [u16]>) {
        assert!(self.base.is_none(), "an overlay reset");
        self.generation = self.generation.wrapping_add(1);
        // A store that was an overlay is a store of its own again.
        self.id_base = 0;
        self.heap_base = 0;
        self.text_base = 0;
        self.copied = None;
        self.order.ranks.clear();
        self.unordered_rank = i32::MAX;
        self.shapes.forget();
        for text in order {
            self.order.rank(text);
        }
        self.meta.clear();
        self.heap.clear();
        self.table.fill([0, EMPTY_SLOT]);
        self.texts.clear();
        self.string_ids.clear();
        self.model_ids.clear();
        self.small_ints.clear();
        self.intern_scalar(KIND_BOOL, 0);
        self.intern_scalar(KIND_BOOL, 1);
        self.intern_block(KIND_SET, &[], 0);
        self.intern_block(KIND_TUPLE, &[], 0);
        for value in SMALL_INT_MIN..=SMALL_INT_MAX {
            let id = self.intern_scalar(KIND_INT, value);
            self.small_ints.push(id);
        }
    }

    /// Ranks texts the store's caller ranked, as a trace's `rankStrings` records.
    pub fn rank_strings<'a>(&mut self, texts: impl IntoIterator<Item = &'a [u16]>) {
        assert!(self.base.is_none(), "an overlay ranks texts");
        for text in texts {
            self.order.rank(text);
        }
    }

    /// Makes the strings ranked from now on unordered: comparing one with another string bails.
    /// A search ranks what ToString makes as it evaluates it, which may be in another order than
    /// TLC's, so their order is TLC's only when the interpreter makes them again.
    pub fn freeze_string_order(&mut self) {
        self.unordered_rank = self.order.ranks.len() as i32;
        self.shapes.forget();
    }

    /// Whether a string has been ranked since `freeze_string_order`.
    pub fn has_unordered_strings(&self) -> bool {
        (self.order.ranks.len() as i32) > self.unordered_rank
    }

    /// TLC's rank of a text, ranking it if it has none, as `getStringRank` does.
    pub fn get_string_rank(&mut self, text: &[u16]) -> i32 {
        match &self.base {
            // TLC ranks a text when it first meets it, which threads would race to do.
            Some(base) => *base
                .order
                .ranks
                .get(text)
                .expect("a text ranked while workers run"),
            None => self.order.rank(text),
        }
    }

    /// Ranks a text as `get_string_rank` does, and gives the string the store already holds of it
    /// that rank, which it held unranked, as one `\o` made.
    pub fn rank_text(&mut self, text: &[u16]) -> i32 {
        let rank = self.get_string_rank(text);
        if let Some(string) = self.find_str(text) {
            let payload = self.meta(string).payload;
            let known = &mut self.texts[payload as usize];
            if known.rank < 0 {
                known.rank = rank;
                // The string may now be unordered, as may the values that hold it.
                self.shapes.forget();
            }
        }
        rank
    }

    /// TLC's ranked texts, in the order of their ranks, as `getStringOrder` gives them.
    pub fn get_string_order(&self) -> Vec<&[u16]> {
        let order = self.get_order();
        let mut texts = vec![&[][..]; order.ranks.len()];
        for (text, &rank) in &order.ranks {
            texts[rank as usize] = text;
        }
        texts
    }

    /// Bumped on every reset, so that caches keyed by ids can tell they are stale.
    pub fn generation(&self) -> u32 {
        self.generation
    }

    pub fn value_count(&self) -> usize {
        self.meta.len()
    }

    // The base's order: an overlay ranks no text of its own.
    fn get_order(&self) -> &StringOrder {
        self.base.as_ref().map_or(&self.order, |base| &base.order)
    }

    #[inline(always)]
    fn meta(&self, id: Id) -> &Meta {
        &self.meta[id as usize]
    }

    #[inline(always)]
    fn text(&self, index: i32) -> &Text {
        &self.texts[index as usize]
    }

    #[inline(always)]
    pub fn kind_of(&self, id: Id) -> u8 {
        self.meta(id).kind
    }

    #[inline(always)]
    pub fn size_of(&self, id: Id) -> u32 {
        self.meta(id).size
    }

    pub fn offset_of(&self, id: Id) -> u32 {
        self.meta(id).payload as u32
    }

    pub fn hash_of(&self, id: Id) -> u32 {
        self.meta(id).hash
    }

    pub fn int_of(&self, id: Id) -> i32 {
        self.meta(id).payload
    }

    /// The text of a string or a model value.
    pub fn text_of(&self, id: Id) -> &[u16] {
        &self.text(self.meta(id).payload).units
    }

    /// The string of a text, if the store holds one, without interning it.
    pub fn find_str(&self, units: &[u16]) -> Option<Id> {
        self.string_ids.get(units).copied()
    }

    /// The rank a string or a model value's text had when the store interned it, or -1.
    pub fn text_rank_of(&self, id: Id) -> i32 {
        self.text(self.meta(id).payload).rank
    }

    /// Whether a string or a model value compares with others without bailing: its text was
    /// ranked before `freeze_string_order`.
    pub fn is_text_ordered(&self, id: Id) -> bool {
        self.text_rank_of(id) < self.unordered_rank
    }

    pub fn is_model_id(&self, id: Id) -> bool {
        self.kind_of(id) == KIND_MODEL
    }

    /// A model value named like A_x is typed: TLC compares it only with model values of its type
    /// or untyped ones. Returns its type's character code, or 0 if it is untyped.
    pub fn get_model_type(&self, id: Id) -> u16 {
        self.text(self.meta(id).payload).model_type
    }

    pub fn is_record(&self, id: Id) -> bool {
        self.meta(id).flags & IS_RECORD != 0
    }

    #[inline(always)]
    fn word(&self, at: usize) -> u32 {
        self.heap[at]
    }

    // The heap's words at an offset. A scalar's payload is no offset, but its size is 0.
    #[inline]
    fn words(&self, offset: usize, length: usize) -> &[u32] {
        if length == 0 {
            &[]
        } else {
            &self.heap[offset..offset + length]
        }
    }

    #[inline]
    fn block(&self, id: Id) -> &[u32] {
        let meta = self.meta(id);
        let length = if meta.kind == KIND_FUNCTION {
            2 * meta.size
        } else {
            meta.size
        };
        self.words(meta.payload as usize, length as usize)
    }

    #[inline]
    pub fn element_at(&self, set: Id, index: u32) -> Id {
        self.word(self.meta(set).payload as usize + index as usize)
    }

    pub fn set_elements(&self, set: Id) -> &[Id] {
        self.block(set)
    }

    pub fn tuple_elements(&self, tuple: Id) -> &[Id] {
        self.block(tuple)
    }

    pub fn bool(&self, value: bool) -> Id {
        if value { TRUE } else { FALSE }
    }

    // --- interning ---

    fn grow_table(&mut self) {
        let slots = self.table.len() * 2;
        let mask = slots - 1;
        let mut next = vec![[0, EMPTY_SLOT]; slots];
        for (index, meta) in self.meta[self.id_base as usize..].iter().enumerate() {
            let mut slot = meta.hash as usize & mask;
            while next[slot][1] != EMPTY_SLOT {
                slot = (slot + 1) & mask;
            }
            next[slot] = [meta.hash, self.id_base + index as Id];
        }
        self.table = next;
        self.mask = mask;
    }

    // Adds a value whose block, if any, is already on the heap at `payload`.
    fn allocate(&mut self, kind: u8, payload: i32, size: u32, hash: u32, slot: usize) -> Id {
        let id = self.value_count() as Id;
        let flags = if matches!(kind, KIND_SET | KIND_FUNCTION | KIND_TUPLE) {
            self.get_flags(kind, payload as usize, size as usize)
        } else {
            0
        };
        self.meta.push(Meta {
            kind,
            flags,
            size,
            payload,
            hash,
        });
        self.table[slot] = [hash, id];
        // The table holds only the store's own values, an overlay's past its copy of the base's.
        if (self.meta.len() - self.id_base as usize) * 2 > self.table.len() {
            self.grow_table();
        }
        id
    }

    /// Whether a value is a function TLC keeps lazy or holds one, which equality builds.
    pub fn is_kept_lazy(&self, id: Id) -> bool {
        let meta = self.meta(id);
        meta.kind == KIND_LAZY_FUNCTION || meta.flags & HOLDS_LAZY != 0
    }

    fn get_flags(&self, kind: u8, offset: usize, size: usize) -> u8 {
        let keys = self.words(offset, size);
        let is_record =
            kind == KIND_FUNCTION && keys.iter().all(|&key| self.meta(key).kind == KIND_STRING);
        let is_run = match (keys.first(), keys.last()) {
            (Some(&first), Some(&last)) => {
                let (first, last) = (self.meta(first), self.meta(last));
                first.kind == KIND_INT
                    && last.kind == KIND_INT
                    && i64::from(last.payload) - i64::from(first.payload) == size as i64 - 1
            }
            _ => false,
        };
        let length = if kind == KIND_FUNCTION {
            2 * size
        } else {
            size
        };
        let holds_lazy = self
            .words(offset, length)
            .iter()
            .any(|&word| self.is_kept_lazy(word));
        (if is_record { IS_RECORD } else { 0 })
            | (if is_run { IS_INT_RUN } else { 0 })
            | if holds_lazy { HOLDS_LAZY } else { 0 }
    }

    // The id of the value with this hash that `is_match` accepts: an overlay looks in its base's
    // table first, then in its own, and gives the slot of its own table to put a new value in.
    #[inline(always)]
    fn find(&self, hash: u32, is_match: impl Fn(Id) -> bool) -> Result<Id, usize> {
        if let Some(base) = &self.base
            && let Ok(id) = probe(&base.table, base.mask, hash, &is_match)
        {
            return Ok(id);
        }
        probe(&self.table, self.mask, hash, &is_match)
    }

    // Interns a scalar: a boolean, an integer, a string, or a model value, by its payload.
    fn intern_scalar(&mut self, kind: u8, payload: i32) -> Id {
        let hash = mix(imul(kind as u32 + 1, 0x9e3779b1) ^ payload as u32);
        let found = self.find(hash, |id| {
            let meta = self.meta(id);
            meta.kind == kind && meta.payload == payload && meta.size == 0
        });
        match found {
            Ok(id) => id,
            Err(slot) => self.allocate(kind, payload, 0, hash, slot),
        }
    }

    // Interns a composite value whose block is `words`.
    fn intern_block(&mut self, kind: u8, words: &[u32], size: u32) -> Id {
        let unmixed = words
            .iter()
            .fold(seed(kind, size), |hash, &word| fold(hash, word));
        self.intern_hashed(kind, words, size, unmixed)
    }

    // Interns a block whose hash over its words, before mixing, is already known.
    fn intern_hashed(&mut self, kind: u8, words: &[u32], size: u32, unmixed: u32) -> Id {
        let hash = mix(unmixed);
        let found = self.find(hash, |id| {
            let meta = self.meta(id);
            meta.kind == kind
                && meta.size == size
                && is_same(self.words(meta.payload as usize, words.len()), words)
        });
        match found {
            Ok(id) => id,
            Err(slot) => {
                let offset = self.heap.len() as i32;
                self.heap.extend_from_slice(words);
                self.allocate(kind, offset, size, hash, slot)
            }
        }
    }

    // Interns `self.scratch[..length]`.
    fn intern_scratch(&mut self, kind: u8, length: usize, size: u32) -> Id {
        let scratch = take(&mut self.scratch);
        let id = self.intern_block(kind, &scratch[..length], size);
        self.scratch = scratch;
        id
    }

    fn take_scratch(&mut self, length: usize) -> Vec<u32> {
        if self.scratch.len() < length {
            self.scratch.resize(2 * length, 0);
        }
        take(&mut self.scratch)
    }

    fn take_pair_scratch(&mut self, length: usize) -> Vec<u32> {
        if self.pair_scratch.len() < length {
            self.pair_scratch.resize(2 * length, 0);
        }
        take(&mut self.pair_scratch)
    }

    // --- scalars ---

    /// An integer, which fails as TLC's arithmetic overflows outside 32 bits.
    pub fn int(&mut self, value: i64) -> Outcome<Id> {
        if (i64::from(SMALL_INT_MIN)..=i64::from(SMALL_INT_MAX)).contains(&value) {
            return Ok(self.small_int(value as i32));
        }
        let Ok(value) = i32::try_from(value) else {
            return Err(Bail("integer overflow"));
        };
        Ok(self.intern_scalar(KIND_INT, value))
    }

    #[inline(always)]
    fn small_int(&self, value: i32) -> Id {
        self.small_ints[(value - SMALL_INT_MIN) as usize]
    }

    // The integer `index + 1`, a tuple's key.
    #[inline(always)]
    fn position_key(&mut self, index: u32) -> Id {
        let value = index as i64 + 1;
        if value <= i64::from(SMALL_INT_MAX) {
            return self.small_int(value as i32);
        }
        self.intern_scalar(KIND_INT, value as i32)
    }

    fn intern_text(&mut self, units: &[u16], rank: i32) -> i32 {
        let index = self.texts.len() as i32;
        self.texts.push(Text {
            units: units.into(),
            rank,
            model_type: get_model_type(units),
        });
        index
    }

    /// A string. One the spec mentions has a rank already; one it builds keeps whatever rank it
    /// has now.
    pub fn str(&mut self, units: &[u16]) -> Id {
        let known = self
            .base
            .as_ref()
            .and_then(|base| base.string_ids.get(units));
        if let Some(&id) = known.or_else(|| self.string_ids.get(units)) {
            return id;
        }
        let rank = self.get_order().ranks.get(units).copied().unwrap_or(-1);
        let index = self.intern_text(units, rank);
        let id = self.intern_scalar(KIND_STRING, index);
        self.string_ids.insert(units.into(), id);
        id
    }

    /// A model value, ranked as TLC ranks its name.
    pub fn model(&mut self, units: &[u16]) -> Id {
        let known = self
            .base
            .as_ref()
            .and_then(|base| base.model_ids.get(units));
        if let Some(&id) = known.or_else(|| self.model_ids.get(units)) {
            return id;
        }
        assert!(self.base.is_none(), "a model value made while workers run");
        let rank = self.order.rank(units);
        let index = self.intern_text(units, rank);
        let id = self.intern_scalar(KIND_MODEL, index);
        self.model_ids.insert(units.into(), id);
        id
    }

    // --- TLC's order and equality ---

    // Fails where either text was ranked since `freeze_string_order`, in an order that may not be
    // TLC's.
    fn check_ordered(&self, left: i32, right: i32, reason: &'static str) -> Outcome<()> {
        let unordered = self.unordered_rank;
        if self.text(left).rank >= unordered || self.text(right).rank >= unordered {
            return Err(Bail(reason));
        }
        Ok(())
    }

    fn check_model_types(&self, left: Id, right: Id) -> Outcome<()> {
        let left_type = self.get_model_type(left);
        let right_type = self.get_model_type(right);
        if left_type != 0 && right_type != 0 && left_type != right_type {
            return Err(Bail("differently typed model values"));
        }
        Ok(())
    }

    /// TLC's `Value#compareTo`. Two values TLC can't compare make the store bail. It returns the
    /// numbers the TypeScript store does, not only their signs. A tuple's keys are interned as
    /// they are compared, as they are there.
    pub fn compare(&mut self, left: Id, right: Id) -> Outcome<i32> {
        if left == right && !self.is_kept_lazy(left) {
            return Ok(0);
        }
        let (left_meta, right_meta) = (*self.meta(left), *self.meta(right));
        if left_meta.kind == KIND_LAZY_FUNCTION || right_meta.kind == KIND_LAZY_FUNCTION {
            return Err(LAZY_FUNCTION);
        }
        if left_meta.kind == right_meta.kind {
            return match left_meta.kind {
                KIND_INT => Ok(if left_meta.payload < right_meta.payload {
                    -1
                } else {
                    1
                }),
                KIND_STRING => {
                    let (left, right) = (left_meta.payload, right_meta.payload);
                    self.check_ordered(left, right, "an order of strings the search ranked")?;
                    Ok(self.compare_texts(left, right))
                }
                KIND_BOOL => Ok(if left < right { -1 } else { 1 }),
                KIND_MODEL => {
                    self.check_model_types(left, right)?;
                    let (left, right) = (left_meta.payload, right_meta.payload);
                    self.check_ordered(left, right, "an order of model values the search ranked")?;
                    Ok(self.text(left).rank - self.text(right).rank)
                }
                KIND_SET => self.compare_sets(left, right),
                // Nat is less than Int, and TLC compares STRING with neither
                // (`Naturals.compareTo`, `Integers.compareTo`, `Strings.compareTo`).
                KIND_INFINITE_SET if left_meta.payload.max(right_meta.payload) == STRINGS => {
                    Err(Bail("values TLC can't compare"))
                }
                KIND_INFINITE_SET => Ok(left_meta.payload - right_meta.payload),
                KIND_FUNCTION | KIND_TUPLE => self.compare_functions(left, right),
                _ => Err(Bail("values TLC can't compare")),
            };
        }
        if left_meta.kind == KIND_MODEL {
            return if self.get_model_type(left) == 0 {
                Ok(-1)
            } else {
                Err(Bail("typed model value"))
            };
        }
        if right_meta.kind == KIND_MODEL {
            return if self.get_model_type(right) == 0 {
                Ok(1)
            } else {
                Err(Bail("typed model value"))
            };
        }
        if is_function_kind(left_meta.kind) && is_function_kind(right_meta.kind) {
            return self.compare_functions(left, right);
        }
        Err(Bail("values TLC can't compare"))
    }

    fn compare_texts(&self, left: i32, right: i32) -> i32 {
        let (left, right) = (self.text(left), self.text(right));
        match (left.rank, right.rank) {
            (-1, -1) => {
                if left.units < right.units {
                    -1
                } else {
                    1
                }
            }
            (_, -1) => -1,
            (-1, _) => 1,
            (left, right) => left - right,
        }
    }

    fn compare_sets(&mut self, left: Id, right: Id) -> Outcome<i32> {
        let size = self.size_of(left);
        let right_size = self.size_of(right);
        if size != right_size {
            return Ok(size as i32 - right_size as i32);
        }
        let (left_offset, right_offset) = (self.offset_of(left), self.offset_of(right));
        for index in 0..size {
            let comparison = self.compare(
                self.word((left_offset + index) as usize),
                self.word((right_offset + index) as usize),
            )?;
            if comparison != 0 {
                return Ok(comparison);
            }
        }
        Ok(0)
    }

    fn compare_functions(&mut self, left: Id, right: Id) -> Outcome<i32> {
        let (left_meta, right_meta) = (*self.meta(left), *self.meta(right));
        let size = left_meta.size;
        if size != right_meta.size {
            // TLC compares a record only with a record, which may fail before the sizes decide.
            if size > 0 && right_meta.size > 0 && self.is_record(left) != self.is_record(right) {
                return Err(Bail("record compared with a function"));
            }
            return Ok(size as i32 - right_meta.size as i32);
        }
        // A value compares as 0 with itself, and with no side effect, so equal ids are skipped.
        for index in 0..size {
            let left_key = self.key_of(&left_meta, index);
            let right_key = self.key_of(&right_meta, index);
            if left_key == right_key && !self.is_kept_lazy(left_key) {
                continue;
            }
            let comparison = self.compare(left_key, right_key)?;
            if comparison != 0 {
                return Ok(comparison);
            }
        }
        for index in 0..size {
            let left_value = self.range_value_of(&left_meta, index);
            let right_value = self.range_value_of(&right_meta, index);
            if left_value == right_value && !self.is_kept_lazy(left_value) {
                continue;
            }
            let comparison = self.compare(left_value, right_value)?;
            if comparison != 0 {
                return Ok(comparison);
            }
        }
        Ok(0)
    }

    // get_key and get_range_value of a function whose meta is read already.
    #[inline(always)]
    fn key_of(&mut self, meta: &Meta, index: u32) -> Id {
        if meta.kind == KIND_TUPLE {
            self.position_key(index)
        } else {
            self.word(meta.payload as usize + index as usize)
        }
    }

    #[inline(always)]
    fn range_value_of(&self, meta: &Meta, index: u32) -> Id {
        let start = if meta.kind == KIND_TUPLE {
            0
        } else {
            meta.size
        };
        self.word(meta.payload as usize + (start + index) as usize)
    }

    /// TLC's equality. Equal values have equal ids, so two distinct ids are unequal, but TLC
    /// compares composite values element by element up to the first difference, which fails where
    /// those elements are values TLC can't compare. The store bails wherever TLC would fail.
    /// Equal ids, two booleans, integers or strings, and two tuples of different lengths are told
    /// apart in place; the rest goes through `equals_other`.
    #[inline(always)]
    pub fn equals(&mut self, left: Id, right: Id) -> Outcome<bool> {
        if left == right {
            // TLC builds a function it kept lazy to compare it, with itself too.
            if self.is_kept_lazy(left) {
                return Err(LAZY_FUNCTION);
            }
            return Ok(true);
        }
        let (left_meta, right_meta) = (self.meta(left), self.meta(right));
        if left_meta.kind == right_meta.kind
            && (left_meta.kind <= KIND_STRING
                || left_meta.kind == KIND_TUPLE && left_meta.size != right_meta.size)
        {
            return Ok(false);
        }
        self.equals_other(left, right)
    }

    /// TLC's `left.equals(right)` where `left` is the value TLC asks: a function with a key that
    /// isn't a string is no record, so it compares with any function by its keys and values
    /// (`FcnRcdValue.equals`), where `equals`, which doesn't know which of the two TLC asks,
    /// stops in case the record is the one asked.
    pub fn equals_asked(&mut self, left: Id, right: Id) -> Outcome<bool> {
        let (left_meta, right_meta) = (*self.meta(left), *self.meta(right));
        let is_record_asked_by_function = is_function_kind(left_meta.kind)
            && is_function_kind(right_meta.kind)
            && left_meta.size > 0
            && right_meta.size > 0
            && !self.is_record(left)
            && self.is_record(right);
        if !is_record_asked_by_function {
            return self.equals(left, right);
        }
        if left_meta.size != right_meta.size {
            return Ok(false);
        }
        // The keys in order, up to the first pair that differs: one of the left's isn't a string.
        for index in 0..left_meta.size {
            let left_key = self.key_of(&left_meta, index);
            let right_key = self.key_of(&right_meta, index);
            if left_key != right_key && !self.equals(left_key, right_key)? {
                return Ok(false);
            }
        }
        Ok(false)
    }

    #[inline(never)]
    fn equals_other(&mut self, left: Id, right: Id) -> Outcome<bool> {
        let (left_kind, right_kind) = (self.kind_of(left), self.kind_of(right));
        if left_kind == KIND_LAZY_FUNCTION || right_kind == KIND_LAZY_FUNCTION {
            return Err(LAZY_FUNCTION);
        }
        if left_kind == right_kind {
            return match left_kind {
                KIND_MODEL => self.check_model_types(left, right).map(|()| false),
                KIND_SET => self.equals_sets(left, right),
                KIND_FUNCTION | KIND_TUPLE => self.equals_functions(left, right),
                // `UserValue.equals` compares.
                KIND_INFINITE_SET => self.compare(left, right).map(|order| order == 0),
                // Interned, so their ids differ only where they do.
                KIND_BOOL | KIND_INT | KIND_STRING => Ok(false),
                _ => Err(Bail("equality of values TLC can't compare")),
            };
        }
        if left_kind == KIND_MODEL {
            return if self.get_model_type(left) == 0 {
                Ok(false)
            } else {
                Err(Bail("typed model value"))
            };
        }
        if right_kind == KIND_MODEL {
            return if self.get_model_type(right) == 0 {
                Ok(false)
            } else {
                Err(Bail("typed model value"))
            };
        }
        if is_function_kind(left_kind) && is_function_kind(right_kind) {
            return self.equals_functions(left, right);
        }
        Err(Bail("equality of values TLC can't compare"))
    }

    // SetEnumValue.equals: sets of one size compare their elements in order up to the first that
    // differ, whose comparison decides, or fails.
    fn equals_sets(&mut self, left: Id, right: Id) -> Outcome<bool> {
        let size = self.size_of(left);
        if size != self.size_of(right) {
            return Ok(false);
        }
        let (left_offset, right_offset) = (self.offset_of(left), self.offset_of(right));
        for index in 0..size {
            let left_element = self.word((left_offset + index) as usize);
            let right_element = self.word((right_offset + index) as usize);
            if left_element != right_element || self.is_kept_lazy(left_element) {
                return self.equals(left_element, right_element);
            }
        }
        Ok(false)
    }

    // The equals of TLC's functions, records and tuples: functions of one size compare their
    // domains in order and then their ranges, up to the first elements that differ.
    fn equals_functions(&mut self, left: Id, right: Id) -> Outcome<bool> {
        let (left_meta, right_meta) = (*self.meta(left), *self.meta(right));
        let size = left_meta.size;
        if size > 0 && right_meta.size > 0 && self.is_record(left) != self.is_record(right) {
            return Err(Bail("record compared with a function"));
        }
        if size != right_meta.size {
            return Ok(false);
        }
        for index in 0..size {
            let left_key = self.key_of(&left_meta, index);
            let right_key = self.key_of(&right_meta, index);
            if left_key != right_key || self.is_kept_lazy(left_key) {
                return self.equals(left_key, right_key);
            }
        }
        for index in 0..size {
            let left_value = self.range_value_of(&left_meta, index);
            let right_value = self.range_value_of(&right_meta, index);
            if left_value != right_value || self.is_kept_lazy(left_value) {
                return self.equals(left_value, right_value);
            }
        }
        Ok(false)
    }

    // --- sets ---

    /// The set of the given elements, in any order and with duplicates.
    pub fn set_of(&mut self, elements: &[Id]) -> Outcome<Id> {
        let length = elements.len();
        if length == 0 {
            return Ok(EMPTY_SET);
        }
        if length == 1 {
            return Ok(self.intern_block(KIND_SET, elements, 1));
        }
        let mut is_sorted = true;
        for index in 1..length {
            if self.compare(elements[index - 1], elements[index])? >= 0 {
                is_sorted = false;
                break;
            }
        }
        if is_sorted {
            return Ok(self.intern_block(KIND_SET, elements, length as u32));
        }
        let mut words = self.take_scratch(length);
        words[..length].copy_from_slice(elements);
        let id = self.intern_sorted_set(&mut words, length);
        self.scratch = words;
        id
    }

    /// The set of `words`, in any order and with duplicates, as `setOfRange` takes it.
    pub fn set_of_range(&mut self, elements: &[Id]) -> Outcome<Id> {
        let length = elements.len();
        if length == 0 {
            return Ok(EMPTY_SET);
        }
        let mut words = self.take_scratch(length);
        words[..length].copy_from_slice(elements);
        let id = self.intern_sorted_set(&mut words, length);
        self.scratch = words;
        id
    }

    // Sorts the set of words[..length], duplicates and all, and interns it.
    fn intern_sorted_set(&mut self, words: &mut [u32], length: usize) -> Outcome<Id> {
        self.sort_words(words, length)?;
        let mut unique = 1;
        for index in 1..length {
            if words[index] != words[unique - 1] {
                words[unique] = words[index];
                unique += 1;
            }
        }
        Ok(self.intern_block(KIND_SET, &words[..unique], unique as u32))
    }

    // Sorts words[..length] in TLC's order: runs by insertion, then merged.
    fn sort_words(&mut self, words: &mut [u32], length: usize) -> Outcome<()> {
        for start in (0..length).step_by(INSERTION_LENGTH) {
            let end = (start + INSERTION_LENGTH).min(length);
            for index in start + 1..end {
                let word = words[index];
                let mut position = index;
                while position > start && self.compare(words[position - 1], word)? > 0 {
                    words[position] = words[position - 1];
                    position -= 1;
                }
                words[position] = word;
            }
        }
        if length <= INSERTION_LENGTH {
            return Ok(());
        }
        let mut other = take(&mut self.sort_scratch);
        if other.len() < length {
            other.resize(2 * length, 0);
        }
        let merged = self.merge_runs(words, &mut other, length);
        self.sort_scratch = other;
        merged
    }

    fn merge_runs(&mut self, words: &mut [u32], other: &mut [u32], length: usize) -> Outcome<()> {
        let mut is_in_words = true;
        let mut width = INSERTION_LENGTH;
        while width < length {
            let (source, target): (&[u32], &mut [u32]) = if is_in_words {
                (&*words, &mut *other)
            } else {
                (&*other, &mut *words)
            };
            for low in (0..length).step_by(2 * width) {
                let middle = (low + width).min(length);
                let high = (low + 2 * width).min(length);
                let (mut left, mut right, mut out) = (low, middle, low);
                while left < middle && right < high {
                    if self.compare(source[left], source[right])? <= 0 {
                        target[out] = source[left];
                        left += 1;
                    } else {
                        target[out] = source[right];
                        right += 1;
                    }
                    out += 1;
                }
                let rest = middle - left;
                target[out..out + rest].copy_from_slice(&source[left..middle]);
                out += rest;
                target[out..out + high - right].copy_from_slice(&source[right..high]);
            }
            is_in_words = !is_in_words;
            width *= 2;
        }
        if !is_in_words {
            words[..length].copy_from_slice(&other[..length]);
        }
        Ok(())
    }

    /// The set of elements already in TLC's order without duplicates.
    pub fn set_of_sorted(&mut self, elements: &[Id]) -> Id {
        self.intern_block(KIND_SET, elements, elements.len() as u32)
    }

    pub fn is_member(&mut self, element: Id, set: Id) -> Outcome<bool> {
        match self.kind_of(set) {
            KIND_INFINITE_SET => return self.is_member_of_infinite(element, set),
            KIND_SET => {}
            _ => return Err(Bail("membership in a non-set")),
        }
        // TLC compares the element with the set's, which builds a function it kept lazy.
        if self.size_of(set) > 0 && (self.is_kept_lazy(element) || self.is_kept_lazy(set)) {
            return Err(LAZY_FUNCTION);
        }
        // Where no comparison can fail, the set holds the element if it holds its id: a short set
        // is scanned, and a run of integers or a long set searched.
        if self.is_member_by_id(element, set) {
            if self.size_of(set) as usize <= SCANNED_SIZE && self.meta(set).flags & IS_INT_RUN == 0
            {
                return Ok(self.set_elements(set).contains(&element));
            }
            return Ok(self.find_in_block(set, element)? != -1);
        }
        if self.find_in_block(set, element)? != -1 {
            return Ok(true);
        }
        let size = self.size_of(set) as usize;
        let offset = self.offset_of(set) as usize;
        // A boolean, integer or string compares with one of its own kind without failing, so a
        // miss in a set of that kind alone, its first and last element, is a miss.
        let kind = self.kind_of(element);
        if size > 0
            && kind <= KIND_STRING
            && self.kind_of(self.word(offset)) == kind
            && self.kind_of(self.word(offset + size - 1)) == kind
        {
            return Ok(false);
        }
        // SetEnumValue.member binary-searches a set TLC has normalized with the element's
        // compareTo, which fails for values TLC can't compare, so a miss makes the same
        // comparisons, in the same order.
        let (mut low, mut high) = (0, size);
        while low < high {
            let middle = low + ((high - low) >> 1);
            let comparison = self.compare(element, self.word(offset + middle))?;
            if comparison == 0 {
                return Ok(true);
            }
            if comparison < 0 {
                high = middle;
            } else {
                low = middle + 1;
            }
        }
        // A set TLC hasn't normalized, a set enumeration's, it checks element by element with
        // equals, which fails on a value of another kind. A set holds one kind of value after any
        // untyped model values, which come first, so its first and its last element are the kinds
        // to check.
        if size > 0 {
            self.check_comparable(element, self.word(offset))?;
            if size > 1 {
                self.check_comparable(element, self.word(offset + size - 1))?;
            }
        }
        Ok(false)
    }

    fn check_comparable(&self, left: Id, right: Id) -> Outcome<()> {
        let (left_kind, right_kind) = (self.kind_of(left), self.kind_of(right));
        if left_kind == right_kind {
            if left_kind == KIND_MODEL {
                self.check_model_types(left, right)?;
            }
            return Ok(());
        }
        if left_kind == KIND_MODEL || right_kind == KIND_MODEL {
            let model = if left_kind == KIND_MODEL { left } else { right };
            if self.get_model_type(model) != 0 {
                return Err(Bail("typed model value"));
            }
            return Ok(());
        }
        if is_function_kind(left_kind) && is_function_kind(right_kind) {
            return Ok(());
        }
        Err(Bail("membership of a value TLC can't compare"))
    }

    // Merges two sets' blocks into the scratch, keeping the elements `keep` says, and returns the
    // scratch and its length.
    fn merge(
        &mut self,
        left: Id,
        right: Id,
        capacity: usize,
        keep: Merge,
    ) -> Outcome<(Vec<u32>, usize)> {
        let (left_size, right_size) = (self.size_of(left) as usize, self.size_of(right) as usize);
        let (left_offset, right_offset) = (
            self.offset_of(left) as usize,
            self.offset_of(right) as usize,
        );
        let mut merged = self.take_scratch(capacity);
        let mut length = 0;
        let (mut left_index, mut right_index) = (0, 0);
        while left_index < left_size && right_index < right_size {
            let left_element = self.word(left_offset + left_index);
            let right_element = self.word(right_offset + right_index);
            if left_element == right_element && !self.is_kept_lazy(left_element) {
                if keep != Merge::Difference {
                    merged[length] = left_element;
                    length += 1;
                }
                left_index += 1;
                right_index += 1;
                continue;
            }
            let comparison = match self.compare(left_element, right_element) {
                Ok(comparison) => comparison,
                Err(bail) => {
                    self.scratch = merged;
                    return Err(bail);
                }
            };
            if comparison < 0 {
                if keep != Merge::Intersection {
                    merged[length] = left_element;
                    length += 1;
                }
                left_index += 1;
            } else {
                if keep == Merge::Union {
                    merged[length] = right_element;
                    length += 1;
                }
                right_index += 1;
            }
        }
        if keep != Merge::Intersection {
            for index in left_index..left_size {
                merged[length] = self.word(left_offset + index);
                length += 1;
            }
        }
        if keep == Merge::Union {
            for index in right_index..right_size {
                merged[length] = self.word(right_offset + index);
                length += 1;
            }
        }
        Ok((merged, length))
    }

    // Interns a merge's result, unless it equals the operand of that size.
    fn finish_merge(&mut self, merged: Vec<u32>, length: usize, operands: &[Id]) -> Id {
        self.scratch = merged;
        for &operand in operands {
            if length == self.size_of(operand) as usize {
                return operand;
            }
        }
        self.intern_scratch(KIND_SET, length, length as u32)
    }

    pub fn union(&mut self, left: Id, right: Id) -> Outcome<Id> {
        let (left_size, right_size) = (self.size_of(left), self.size_of(right));
        if left_size == 0 {
            return Ok(right);
        }
        if right_size == 0 || left == right && !self.is_kept_lazy(left) {
            return Ok(left);
        }
        let capacity = (left_size + right_size) as usize;
        let (merged, length) = self.merge(left, right, capacity, Merge::Union)?;
        Ok(self.finish_merge(merged, length, &[left, right]))
    }

    pub fn intersection(&mut self, left: Id, right: Id) -> Outcome<Id> {
        let (left_size, right_size) = (self.size_of(left), self.size_of(right));
        if left_size == 0 || left == right && !self.is_kept_lazy(left) {
            return Ok(left);
        }
        if right_size == 0 {
            return Ok(right);
        }
        let (merged, length) = self.merge(left, right, left_size as usize, Merge::Intersection)?;
        Ok(self.finish_merge(merged, length, &[left]))
    }

    pub fn difference(&mut self, left: Id, right: Id) -> Outcome<Id> {
        let (left_size, right_size) = (self.size_of(left), self.size_of(right));
        if left_size == 0 || right_size == 0 {
            return Ok(left);
        }
        if left == right && !self.is_kept_lazy(left) {
            return Ok(EMPTY_SET);
        }
        let (merged, length) = self.merge(left, right, left_size as usize, Merge::Difference)?;
        Ok(self.finish_merge(merged, length, &[left]))
    }

    pub fn is_subset(&mut self, left: Id, right: Id) -> Outcome<bool> {
        if left == right {
            if self.is_kept_lazy(left) {
                return Err(LAZY_FUNCTION);
            }
            return Ok(true);
        }
        let left_size = self.size_of(left);
        let offset = self.offset_of(left) as usize;
        for index in 0..left_size as usize {
            if !self.is_member(self.word(offset + index), right)? {
                return Ok(false);
            }
        }
        // TLC still compares the elements of a larger set, which may fail.
        Ok(left_size <= self.size_of(right))
    }

    pub fn with_element(&mut self, set: Id, element: Id) -> Outcome<Id> {
        let size = self.size_of(set) as usize;
        let offset = self.offset_of(set) as usize;
        let mut merged = self.take_scratch(size + 1);
        let mut length = 0;
        let mut is_inserted = false;
        for index in 0..size {
            let current = self.word(offset + index);
            if current == element && !self.is_kept_lazy(element) {
                self.scratch = merged;
                return Ok(set);
            }
            if !is_inserted {
                let comparison = match self.compare(element, current) {
                    Ok(comparison) => comparison,
                    Err(bail) => {
                        self.scratch = merged;
                        return Err(bail);
                    }
                };
                if comparison < 0 {
                    merged[length] = element;
                    length += 1;
                    is_inserted = true;
                }
            }
            merged[length] = current;
            length += 1;
        }
        if !is_inserted {
            merged[length] = element;
            length += 1;
        }
        self.scratch = merged;
        Ok(self.intern_scratch(KIND_SET, length, length as u32))
    }

    // --- functions, records and tuples ---

    pub fn tuple_of(&mut self, elements: &[Id]) -> Id {
        if elements.is_empty() {
            return EMPTY_TUPLE;
        }
        self.intern_block(KIND_TUPLE, elements, elements.len() as u32)
    }

    pub fn create_record_shape(&self, keys: &[Id]) -> RecordShape {
        let prefix = keys
            .iter()
            .fold(seed(KIND_FUNCTION, keys.len() as u32), |hash, &key| {
                fold(hash, key)
            });
        RecordShape {
            keys: keys.to_vec(),
            prefix,
        }
    }

    /// The record of a shape with these values, which are as many as its keys. It is looked up
    /// against the shape's keys and the values where they are, and copied only when new.
    pub fn record_of(&mut self, shape: &RecordShape, values: &[Id]) -> Id {
        let size = shape.keys.len();
        let values = &values[..size];
        let unmixed = values
            .iter()
            .fold(shape.prefix, |hash, &value| fold(hash, value));
        let hash = mix(unmixed);
        let found = self.find(hash, |id| {
            let meta = self.meta(id);
            let other = meta.payload as usize;
            meta.kind == KIND_FUNCTION
                && meta.size == size as u32
                && is_same(self.words(other + size, size), values)
                && is_same(self.words(other, size), &shape.keys)
        });
        match found {
            Ok(id) => id,
            Err(slot) => {
                let start = self.heap.len() as i32;
                self.heap.extend_from_slice(&shape.keys);
                self.heap.extend_from_slice(values);
                self.allocate(KIND_FUNCTION, start, size as u32, hash, slot)
            }
        }
    }

    fn is_position_keys(&self, keys: &[Id]) -> bool {
        keys.iter().enumerate().all(|(index, &key)| {
            let meta = self.meta(key);
            meta.kind == KIND_INT && i64::from(meta.payload) == index as i64 + 1
        })
    }

    /// The function with the given domain in TLC's order and the range in the same order. A
    /// domain of 1..n makes a tuple.
    pub fn function_of_sorted(&mut self, domain: &[Id], range: &[Id]) -> Id {
        let size = domain.len();
        if size == 0 {
            return EMPTY_TUPLE;
        }
        if self.is_position_keys(domain) {
            return self.intern_block(KIND_TUPLE, &range[..size], size as u32);
        }
        let mut words = self.take_pair_scratch(2 * size);
        words[..size].copy_from_slice(domain);
        words[size..2 * size].copy_from_slice(&range[..size]);
        let id = self.intern_block(KIND_FUNCTION, &words[..2 * size], size as u32);
        self.pair_scratch = words;
        id
    }

    // The function whose sorted keys and then their values fill words[..2 * size]. A domain of
    // 1..n makes a tuple of the values.
    fn intern_pairs(&mut self, words: &[u32], size: usize) -> Id {
        if self.is_position_keys(&words[..size]) {
            return self.intern_block(KIND_TUPLE, &words[size..2 * size], size as u32);
        }
        self.intern_block(KIND_FUNCTION, &words[..2 * size], size as u32)
    }

    /// The function from the elements of a set, in its order, to `values`, one for each.
    pub fn function_over_set(&mut self, set: Id, values: &[Id]) -> Id {
        let size = self.size_of(set) as usize;
        if size == 0 {
            return EMPTY_TUPLE;
        }
        let offset = self.offset_of(set) as usize;
        if self.is_position_keys(self.words(offset, size)) {
            return self.intern_block(KIND_TUPLE, &values[..size], size as u32);
        }
        let mut words = self.take_pair_scratch(2 * size);
        words[..size].copy_from_slice(self.words(offset, size));
        words[size..2 * size].copy_from_slice(&values[..size]);
        let id = self.intern_block(KIND_FUNCTION, &words[..2 * size], size as u32);
        self.pair_scratch = words;
        id
    }

    /// The function of the given pairs, keys in any order but without duplicates.
    pub fn function_of(&mut self, keys: &[Id], values: &[Id]) -> Outcome<Id> {
        let size = keys.len();
        let mut is_sorted = true;
        for index in 1..size {
            if self.compare(keys[index - 1], keys[index])? >= 0 {
                is_sorted = false;
                break;
            }
        }
        if is_sorted {
            return Ok(self.function_of_sorted(keys, values));
        }
        if size <= INSERTION_LENGTH {
            // The pairs, sorted by key as they are inserted: the keys, then the values.
            let mut words = self.take_scratch(2 * size);
            let sorted = self.insert_pairs(&mut words, keys, values);
            let id = sorted.map(|()| self.intern_pairs(&words, size));
            self.scratch = words;
            return id;
        }
        let mut order: Vec<usize> = (0..size).collect();
        self.merge_sort(&mut order, keys)?;
        let domain: Vec<Id> = order.iter().map(|&index| keys[index]).collect();
        let range: Vec<Id> = order.iter().map(|&index| values[index]).collect();
        Ok(self.function_of_sorted(&domain, &range))
    }

    fn insert_pairs(&mut self, words: &mut [u32], keys: &[Id], values: &[Id]) -> Outcome<()> {
        let size = keys.len();
        for (index, &key) in keys.iter().enumerate() {
            let mut position = index;
            while position > 0 && self.compare(words[position - 1], key)? > 0 {
                words[position] = words[position - 1];
                words[size + position] = words[size + position - 1];
                position -= 1;
            }
            words[position] = key;
            words[size + position] = values[index];
        }
        Ok(())
    }

    // Sorts the indexes of keys by their keys, stably, as JavaScript's sort does with the store's
    // comparison.
    fn merge_sort(&mut self, order: &mut [usize], keys: &[Id]) -> Outcome<()> {
        if order.len() <= 1 {
            return Ok(());
        }
        let middle = order.len() / 2;
        self.merge_sort(&mut order[..middle], keys)?;
        self.merge_sort(&mut order[middle..], keys)?;
        let mut merged = Vec::with_capacity(order.len());
        let (mut left, mut right) = (0, middle);
        while left < middle && right < order.len() {
            if self.compare(keys[order[left]], keys[order[right]])? <= 0 {
                merged.push(order[left]);
                left += 1;
            } else {
                merged.push(order[right]);
                right += 1;
            }
        }
        merged.extend_from_slice(&order[left..middle]);
        merged.extend_from_slice(&order[right..]);
        order.copy_from_slice(&merged);
        Ok(())
    }

    /// A function's key at a position. A tuple's key is interned as it is read, as it is there.
    pub fn get_key(&mut self, function: Id, index: u32) -> Id {
        let meta = *self.meta(function);
        self.key_of(&meta, index)
    }

    /// A function's key at a position, if it is interned: always, except for the key of a tuple
    /// beyond the small integers that hasn't been read.
    pub fn peek_key(&self, function: Id, index: u32) -> Option<Id> {
        if self.kind_of(function) != KIND_TUPLE {
            return Some(self.word((self.offset_of(function) + index) as usize));
        }
        let value = index as i64 + 1;
        if value <= i64::from(SMALL_INT_MAX) {
            return Some(self.small_int(value as i32));
        }
        None
    }

    #[inline]
    pub fn get_range_value(&self, function: Id, index: u32) -> Id {
        let meta = self.meta(function);
        let start = if meta.kind == KIND_TUPLE {
            0
        } else {
            meta.size
        };
        self.word((meta.payload as u32 + start + index) as usize)
    }

    /// The position of a key in the domain of a function, or -1.
    pub fn find_key(&mut self, function: Id, key: Id) -> Outcome<i32> {
        if self.kind_of(function) == KIND_TUPLE {
            let key = *self.meta(key);
            if key.kind != KIND_INT {
                return Ok(-1);
            }
            let position = i64::from(key.payload) - 1;
            return Ok(
                if position >= 0 && position < i64::from(self.size_of(function)) {
                    position as i32
                } else {
                    -1
                },
            );
        }
        self.find_in_block(function, key)
    }

    // The position of a value in the sorted block of a set, or of a function's domain, or -1.
    fn find_in_block(&mut self, block: Id, key: Id) -> Outcome<i32> {
        let meta = *self.meta(block);
        let (offset, size) = (meta.payload as usize, meta.size as usize);
        let key_meta = *self.meta(key);
        // TLC compares a key that is or holds a function it keeps lazy, which fails, where the
        // store would find it by its id.
        if size > 0 && self.is_kept_lazy(key) {
            return Err(LAZY_FUNCTION);
        }
        // A block of consecutive integers, such as 0..n, finds its key by subtraction.
        if meta.flags & IS_INT_RUN != 0 && key_meta.kind == KIND_INT {
            let low = self.meta(self.word(offset)).payload;
            let position = i64::from(key_meta.payload) - i64::from(low);
            return Ok(if position >= 0 && position < size as i64 {
                position as i32
            } else {
                -1
            });
        }
        if size <= LINEAR_SIZE {
            let words = self.words(offset, size);
            return Ok(words
                .iter()
                .position(|&word| word == key)
                .map_or(-1, |index| index as i32));
        }
        let (mut low, mut high) = (0i64, size as i64 - 1);
        while low <= high {
            let middle = (low + high) >> 1;
            let current = self.word(offset + middle as usize);
            if current == key {
                return Ok(middle as i32);
            }
            if self.compare(current, key)? < 0 {
                low = middle + 1;
            } else {
                high = middle - 1;
            }
        }
        Ok(-1)
    }

    /// `f[k]`. A tuple or a function over a run of integers, at an integer in its domain, finds
    /// its value by subtraction in place; the rest goes through `apply_other`.
    #[inline(always)]
    pub fn apply(&mut self, function: Id, key: Id) -> Outcome<Id> {
        let (meta, key_meta) = (self.meta(function), self.meta(key));
        let run = match meta.kind {
            _ if key_meta.kind != KIND_INT => None,
            KIND_TUPLE => Some((1, 0)),
            KIND_FUNCTION if meta.flags & IS_INT_RUN != 0 => Some((
                self.meta(self.word(meta.payload as usize)).payload,
                meta.size,
            )),
            _ => None,
        };
        if let Some((low, values)) = run {
            let position = i64::from(key_meta.payload) - i64::from(low);
            if position >= 0 && position < i64::from(meta.size) {
                return Ok(self.word((meta.payload as u32 + values) as usize + position as usize));
            }
        }
        self.apply_other(function, key)
    }

    // `f[k]` of any other function, or of a key outside a run's domain.
    #[inline(never)]
    fn apply_other(&mut self, function: Id, key: Id) -> Outcome<Id> {
        let meta = *self.meta(function);
        if !is_function_kind(meta.kind) {
            return Err(Bail("applied a non-function"));
        }
        let position = self.find_key(function, key)?;
        if position == -1 {
            return Err(Bail("applied a function outside its domain"));
        }
        Ok(self.get_range_value(function, position as u32))
    }

    // Interns the function's block with the words at patch_indexes[..count] replaced. The result
    // usually exists already, so it is looked up in place, hashed as intern_block would hash the
    // changed block, and copied only when it is new.
    fn intern_patched(&mut self, function: Id, count: usize) -> Id {
        let meta = *self.meta(function);
        let offset = meta.payload as usize;
        let length = if meta.kind == KIND_TUPLE {
            meta.size
        } else {
            2 * meta.size
        } as usize;
        let mut unmixed = seed(meta.kind, meta.size);
        let mut from = 0;
        for patch in 0..count {
            let to = self.patch_indexes[patch] as usize;
            for index in from..to {
                unmixed = fold(unmixed, self.word(offset + index));
            }
            unmixed = fold(unmixed, self.patch_values[patch]);
            from = to + 1;
        }
        for index in from..length {
            unmixed = fold(unmixed, self.word(offset + index));
        }
        let hash = mix(unmixed);
        let found = self.find(hash, |id| {
            let other = self.meta(id);
            other.kind == meta.kind
                && other.size == meta.size
                && self.is_patched(other.payload as usize, offset, length, count)
        });
        match found {
            Ok(id) => id,
            Err(slot) => {
                let start = self.heap.len();
                self.heap.extend_from_within(offset..offset + length);
                for patch in 0..count {
                    self.heap[start + self.patch_indexes[patch] as usize] =
                        self.patch_values[patch];
                }
                self.allocate(meta.kind, start as i32, meta.size, hash, slot)
            }
        }
    }

    // Whether the block at other is the block at offset with the patches applied.
    fn is_patched(&self, other: usize, offset: usize, length: usize, count: usize) -> bool {
        let (other, source) = (self.words(other, length), self.words(offset, length));
        let mut from = 0;
        for patch in 0..count {
            let to = self.patch_indexes[patch] as usize;
            if other[to] != self.patch_values[patch]
                || !is_same(&other[from..to], &source[from..to])
            {
                return false;
            }
            from = to + 1;
        }
        is_same(&other[from..length], &source[from..length])
    }

    /// `[fn EXCEPT ![key] = value]`.
    pub fn except(&mut self, function: Id, key: Id, value: Id) -> Outcome<Id> {
        let kind = self.kind_of(function);
        if !is_function_kind(kind) {
            return Err(Bail("EXCEPT on a non-function"));
        }
        let position = self.find_key(function, key)?;
        // TLC leaves a function alone when EXCEPT names a key outside its domain, but a tuple
        // fails to fingerprint later, so the store leaves both to the reference interpreter.
        if position == -1 {
            return Err(Bail("EXCEPT outside the domain"));
        }
        let index = if kind == KIND_TUPLE {
            position as u32
        } else {
            self.size_of(function) + position as u32
        };
        if self.word((self.offset_of(function) + index) as usize) == value {
            return Ok(function);
        }
        self.patch_indexes[0] = index;
        self.patch_values[0] = value;
        Ok(self.intern_patched(function, 1))
    }

    /// `[fn EXCEPT ![k1] = v1, ..., ![kn] = vn]`, given the position of each key in the function,
    /// interned once. A later update of a key replaces an earlier one.
    pub fn except_at(&mut self, function: Id, positions: &[u32], values: &[Id]) -> Id {
        let offset = self.offset_of(function) as usize;
        let value_start = if self.kind_of(function) == KIND_TUPLE {
            0
        } else {
            self.size_of(function)
        };
        let count = positions.len();
        if self.patch_indexes.len() < count {
            self.patch_indexes.resize(2 * count, 0);
            self.patch_values.resize(2 * count, 0);
        }
        let mut patches = 0;
        for (update, &position) in positions.iter().enumerate() {
            let index = value_start + position;
            let mut patch = patches;
            while patch > 0 && self.patch_indexes[patch - 1] > index {
                patch -= 1;
            }
            if patch > 0 && self.patch_indexes[patch - 1] == index {
                self.patch_values[patch - 1] = values[update];
                continue;
            }
            self.patch_indexes.copy_within(patch..patches, patch + 1);
            self.patch_values.copy_within(patch..patches, patch + 1);
            self.patch_indexes[patch] = index;
            self.patch_values[patch] = values[update];
            patches += 1;
        }
        let is_changed = (0..patches).any(|patch| {
            self.word(offset + self.patch_indexes[patch] as usize) != self.patch_values[patch]
        });
        if is_changed {
            self.intern_patched(function, patches)
        } else {
            function
        }
    }

    /// `r.field` for a record, given where the field was in the last record read: records of one
    /// type keep their fields at the same position, so the hint usually saves the search.
    pub fn apply_field(&mut self, function: Id, key: Id, hint: &mut u32) -> Outcome<Id> {
        let meta = *self.meta(function);
        if meta.kind == KIND_FUNCTION {
            let (size, offset) = (meta.size, meta.payload as usize);
            if *hint < size && self.word(offset + *hint as usize) == key {
                return Ok(self.word(offset + (size + *hint) as usize));
            }
            let found = self.find_key(function, key)?;
            if found != -1 {
                *hint = found as u32;
                return Ok(self.word(offset + (size + *hint) as usize));
            }
        }
        self.apply(function, key)
    }

    /// `r.field` of a function that has the key, found by the key's id without comparing, where
    /// `hint` is the position it was last found at: None where `apply_field` would search with
    /// comparisons or fail.
    #[inline(always)]
    pub fn field_by_id(&self, function: Id, key: Id, hint: &mut u32) -> Option<Id> {
        let meta = self.meta(function);
        if meta.kind != KIND_FUNCTION {
            return None;
        }
        let (size, offset) = (meta.size, meta.payload as usize);
        if *hint >= size || self.word(offset + *hint as usize) != key {
            *hint = self
                .words(offset, size as usize)
                .iter()
                .position(|&stored| stored == key)? as u32;
        }
        Some(self.word(offset + (size + *hint) as usize))
    }

    pub fn domain_of(&mut self, function: Id) -> Id {
        let size = self.size_of(function);
        let mut keys = self.take_scratch(size as usize);
        for index in 0..size {
            keys[index as usize] = self.get_key(function, index);
        }
        let id = self.intern_block(KIND_SET, &keys[..size as usize], size);
        self.scratch = keys;
        id
    }

    /// Nat, Int or STRING as a value, by [`NAT`], [`INT`] or [`STRINGS`].
    pub fn infinite_set(&mut self, name: i32) -> Id {
        self.intern_scalar(KIND_INFINITE_SET, name)
    }

    /// Which of Nat, Int and STRING a value of that kind is: [`NAT`], [`INT`] or [`STRINGS`].
    pub fn infinite_name_of(&self, id: Id) -> i32 {
        self.meta(id).payload
    }

    // Membership in Nat, Int or STRING held as a value (`Naturals.member`, `Integers.member`,
    // `Strings.member`): an untyped model value is in none, and any other value of another kind
    // fails.
    fn is_member_of_infinite(&self, element: Id, set: Id) -> Outcome<bool> {
        let (name, kind) = (self.meta(set).payload, self.kind_of(element));
        let (holds, reason) = match name {
            NAT => (
                kind == KIND_INT && self.int_of(element) >= 0,
                "a mistyped membership in Nat",
            ),
            INT => (kind == KIND_INT, "a mistyped membership in Int"),
            _ => (kind == KIND_STRING, "a mistyped membership in STRING"),
        };
        let is_typed = if name == STRINGS {
            kind == KIND_STRING
        } else {
            kind == KIND_INT
        };
        if is_typed || kind == KIND_MODEL && self.get_model_type(element) == 0 {
            Ok(holds)
        } else {
            Err(Bail(reason))
        }
    }

    /// A function TLC keeps lazy, by its number among those a machine keeps.
    pub fn lazy_function(&mut self, index: u32) -> Id {
        self.intern_scalar(KIND_LAZY_FUNCTION, index as i32)
    }

    /// The number among those a machine keeps of a function TLC keeps lazy.
    pub fn lazy_index_of(&self, id: Id) -> u32 {
        self.meta(id).payload as u32
    }

    /// Whether a value holds a function TLC keeps lazy, or Nat, Int or STRING as a value, at any
    /// depth: what TLC can't fingerprint.
    pub fn holds_lazy_function(&self, id: Id) -> bool {
        let meta = self.meta(id);
        let length = match meta.kind {
            KIND_LAZY_FUNCTION | KIND_INFINITE_SET => return true,
            KIND_SET | KIND_TUPLE => meta.size as usize,
            KIND_FUNCTION => 2 * meta.size as usize,
            _ => return false,
        };
        (0..length).any(|index| self.holds_lazy_function(self.word(meta.payload as usize + index)))
    }

    /// The elements of a tuple from position `from` up to `to`, as Tail takes them.
    pub fn slice_tuple(&mut self, tuple: Id, from: u32, to: u32) -> Id {
        if to <= from {
            return EMPTY_TUPLE;
        }
        let offset = self.offset_of(tuple) as usize;
        let length = (to - from) as usize;
        let mut words = self.take_scratch(length);
        words[..length].copy_from_slice(self.words(offset + from as usize, length));
        self.scratch = words;
        self.intern_scratch(KIND_TUPLE, length, length as u32)
    }

    pub fn concat_tuples(&mut self, left: Id, right: Id) -> Id {
        let (left_size, right_size) = (self.size_of(left) as usize, self.size_of(right) as usize);
        if right_size == 0 {
            return left;
        }
        if left_size == 0 {
            return right;
        }
        let length = left_size + right_size;
        let (left_offset, right_offset) = (
            self.offset_of(left) as usize,
            self.offset_of(right) as usize,
        );
        let mut words = self.take_scratch(length);
        words[..left_size].copy_from_slice(self.words(left_offset, left_size));
        words[left_size..length].copy_from_slice(self.words(right_offset, right_size));
        self.scratch = words;
        self.intern_scratch(KIND_TUPLE, length, length as u32)
    }

    pub fn append_tuple(&mut self, tuple: Id, element: Id) -> Id {
        let size = self.size_of(tuple) as usize;
        let offset = self.offset_of(tuple) as usize;
        let mut words = self.take_scratch(size + 1);
        words[..size].copy_from_slice(self.words(offset, size));
        words[size] = element;
        self.scratch = words;
        self.intern_scratch(KIND_TUPLE, size + 1, size as u32 + 1)
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Merge {
    Union,
    Intersection,
    Difference,
}

// The id in a table of a value with this hash that `is_match` accepts, or the empty slot where the
// probe ended.
#[inline(always)]
fn probe(
    table: &[[u32; 2]],
    mask: usize,
    hash: u32,
    is_match: &impl Fn(Id) -> bool,
) -> Result<Id, usize> {
    let mut slot = hash as usize & mask;
    loop {
        let [stored_hash, id] = table[slot];
        if id == EMPTY_SLOT {
            return Err(slot);
        }
        if stored_hash == hash && is_match(id) {
            return Ok(id);
        }
        slot = (slot + 1) & mask;
    }
}

// Whether two blocks of one length hold the same words. Blocks are short, and a loop that stops at
// the first difference beats a call to memcmp on them.
#[inline(always)]
fn is_same(left: &[u32], right: &[u32]) -> bool {
    left.len() == right.len() && left.iter().zip(right).all(|(left, right)| left == right)
}

/// How TLC prints Nat, Int or STRING held as a value.
pub fn infinite_set_name(name: i32) -> &'static str {
    match name {
        NAT => "Nat",
        INT => "Int",
        _ => "STRING",
    }
}

/// Whether a value of this kind is a set the store tests membership in.
pub fn is_tested_set_kind(kind: u8) -> bool {
    kind == KIND_SET || kind == KIND_INFINITE_SET
}

pub fn is_function_kind(kind: u8) -> bool {
    kind == KIND_FUNCTION || kind == KIND_TUPLE
}

#[cfg(test)]
mod tests {
    use super::*;

    // An overlay's intern table holds only its own values, so a large base doesn't make it grow.
    #[test]
    fn an_overlays_table_grows_with_its_own_values() {
        let mut base = Store::new();
        let held: Vec<Id> = (10_000..60_000)
            .map(|value| base.int(value).unwrap())
            .collect();
        let mut overlay = Store::overlay(Arc::new(base));
        let own = overlay.int(70_000).unwrap();
        assert_eq!(overlay.int(10_000).unwrap(), held[0]);
        assert_eq!(overlay.int(70_000).unwrap(), own);
        assert_eq!(overlay.table.len(), INITIAL_CAPACITY * 2);
    }

    #[test]
    fn holds_nat_and_int_as_elements_as_tlc_does() {
        let mut store = Store::new();
        let (nat, int, strings) = (
            store.infinite_set(NAT),
            store.infinite_set(INT),
            store.infinite_set(STRINGS),
        );
        // Nat is less than Int, so {{Nat}, {Int}} holds {Nat} first.
        assert_eq!(store.compare(nat, int), Ok(-1));
        assert_eq!(store.equals(nat, int), Ok(false));
        let (of_nat, of_int) = (store.set_of(&[nat]).unwrap(), store.set_of(&[int]).unwrap());
        let both = store.set_of(&[of_int, of_nat]).unwrap();
        assert_eq!(store.set_elements(both), [of_nat, of_int]);
        assert!(store.compare(nat, strings).is_err());
        let (minus_one, text) = (store.int(-1).unwrap(), store.str(&[97]));
        assert_eq!(store.is_member(minus_one, nat), Ok(false));
        assert_eq!(store.is_member(minus_one, int), Ok(true));
        assert_eq!(store.is_member(text, strings), Ok(true));
        assert_eq!(
            store.is_member(text, nat),
            Err(Bail("a mistyped membership in Nat"))
        );
        assert!(store.holds_lazy_function(both));
        assert_eq!(
            crate::print::format_value(&store, both).unwrap(),
            "{{Nat}, {Int}}"
        );
    }
}
