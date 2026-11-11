//! zlib 1.3's deflate at level 6 with a raw 32K window and memory level 8, as
//! `java.util.zip.Deflater` runs it for `GZIPOutputStream`: `deflate_slow` from deflate.c and the
//! Huffman coding of trees.c, which together decide every byte of the stream. Feeding the input in
//! pieces doesn't change the stream, so this takes it whole.

const WINDOW_BITS: usize = 15;
const WINDOW_SIZE: usize = 1 << WINDOW_BITS;
const WINDOW_MASK: usize = WINDOW_SIZE - 1;
const HASH_BITS: usize = 15;
const HASH_SIZE: usize = 1 << HASH_BITS;
const HASH_MASK: usize = HASH_SIZE - 1;
const HASH_SHIFT: usize = HASH_BITS.div_ceil(MIN_MATCH);
const LITERAL_BUFFER_SIZE: usize = 1 << 14;
const SYMBOL_END: usize = (LITERAL_BUFFER_SIZE - 1) * 3;

const MIN_MATCH: usize = 3;
const MAX_MATCH: usize = 258;
const MIN_LOOKAHEAD: usize = MAX_MATCH + MIN_MATCH + 1;
const MAX_DISTANCE: usize = WINDOW_SIZE - MIN_LOOKAHEAD;
const TOO_FAR: usize = 4096;

// Level 6 of `configuration_table`.
const GOOD_MATCH: usize = 8;
const MAX_LAZY_MATCH: usize = 16;
const NICE_MATCH: usize = 128;
const MAX_CHAIN: usize = 128;

const LENGTH_CODES: usize = 29;
const LITERALS: usize = 256;
const LENGTH_SYMBOLS: usize = LITERALS + 1 + LENGTH_CODES;
const DISTANCE_CODES: usize = 30;
const BIT_LENGTH_CODES: usize = 19;
const HEAP_SIZE: usize = 2 * LENGTH_SYMBOLS + 1;
const MAX_BITS: usize = 15;
const MAX_BIT_LENGTH_BITS: usize = 7;
const END_BLOCK: usize = 256;
const REPEAT_3_6: usize = 16;
const REPEAT_ZERO_3_10: usize = 17;
const REPEAT_ZERO_11_138: usize = 18;

const EXTRA_LENGTH_BITS: [usize; LENGTH_CODES] = [
    0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0,
];
const EXTRA_DISTANCE_BITS: [usize; DISTANCE_CODES] = [
    0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13,
    13,
];
const EXTRA_BIT_LENGTH_BITS: [usize; BIT_LENGTH_CODES] =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 7];
const BIT_LENGTH_ORDER: [usize; BIT_LENGTH_CODES] = [
    16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15,
];

/// The raw deflate stream of `input`.
pub fn deflate(input: &[u8]) -> Vec<u8> {
    let mut state = State::new(input);
    state.compress();
    state.output
}

// trees.c's static tables, as `tr_static_init` computes them.
struct Tables {
    length_code: [u8; MAX_MATCH - MIN_MATCH + 1],
    distance_code: [u8; 512],
    base_length: [usize; LENGTH_CODES],
    base_distance: [usize; DISTANCE_CODES],
    static_literal_lengths: [u16; LENGTH_SYMBOLS + 2],
    static_literal_codes: [u16; LENGTH_SYMBOLS + 2],
    static_distance_codes: [u16; DISTANCE_CODES],
}

impl Tables {
    fn new() -> Tables {
        let mut tables = Tables {
            length_code: [0; MAX_MATCH - MIN_MATCH + 1],
            distance_code: [0; 512],
            base_length: [0; LENGTH_CODES],
            base_distance: [0; DISTANCE_CODES],
            static_literal_lengths: [0; LENGTH_SYMBOLS + 2],
            static_literal_codes: [0; LENGTH_SYMBOLS + 2],
            static_distance_codes: [0; DISTANCE_CODES],
        };
        let mut length = 0;
        for (code, extra) in EXTRA_LENGTH_BITS.iter().enumerate().take(LENGTH_CODES - 1) {
            tables.base_length[code] = length;
            for _ in 0..1 << extra {
                tables.length_code[length] = code as u8;
                length += 1;
            }
        }
        // Length 258 has a code of its own, which overwrites the last of the code before it.
        tables.length_code[length - 1] = (LENGTH_CODES - 1) as u8;
        let mut distance = 0;
        for (code, extra) in EXTRA_DISTANCE_BITS.iter().enumerate().take(16) {
            tables.base_distance[code] = distance;
            for _ in 0..1 << extra {
                tables.distance_code[distance] = code as u8;
                distance += 1;
            }
        }
        distance >>= 7;
        for (code, extra) in EXTRA_DISTANCE_BITS.iter().enumerate().skip(16) {
            tables.base_distance[code] = distance << 7;
            for _ in 0..1 << (extra - 7) {
                tables.distance_code[256 + distance] = code as u8;
                distance += 1;
            }
        }
        let mut bit_counts = [0u16; MAX_BITS + 1];
        for (symbol, length) in tables.static_literal_lengths.iter_mut().enumerate() {
            *length = match symbol {
                0..=143 => 8,
                144..=255 => 9,
                256..=279 => 7,
                _ => 8,
            };
            bit_counts[*length as usize] += 1;
        }
        tables.static_literal_codes = generate_codes(
            &tables.static_literal_lengths,
            LENGTH_SYMBOLS + 1,
            &bit_counts,
        )
        .try_into()
        .expect("the static literal codes");
        for (code, value) in tables.static_distance_codes.iter_mut().enumerate() {
            *value = reverse_bits(code as u32, 5) as u16;
        }
        tables
    }

    fn distance_code(&self, distance: usize) -> usize {
        usize::from(if distance < 256 {
            self.distance_code[distance]
        } else {
            self.distance_code[256 + (distance >> 7)]
        })
    }
}

fn reverse_bits(mut code: u32, length: usize) -> u32 {
    let mut reversed = 0;
    for _ in 0..length {
        reversed = (reversed << 1) | (code & 1);
        code >>= 1;
    }
    reversed
}

// `gen_codes`: the code of each symbol of a nonzero length up to `max_code`, the rest 0.
fn generate_codes(lengths: &[u16], max_code: usize, bit_counts: &[u16]) -> Vec<u16> {
    let mut next_code = [0u16; MAX_BITS + 1];
    let mut code: u32 = 0;
    for bits in 1..=MAX_BITS {
        code = (code + u32::from(bit_counts[bits - 1])) << 1;
        next_code[bits] = code as u16;
    }
    let mut codes = vec![0u16; lengths.len()];
    for symbol in 0..=max_code.min(lengths.len() - 1) {
        let length = usize::from(lengths[symbol]);
        if length == 0 {
            continue;
        }
        codes[symbol] = reverse_bits(u32::from(next_code[length]), length) as u16;
        next_code[length] = next_code[length].wrapping_add(1);
    }
    codes
}

// A dynamic tree of trees.c (`ct_data` with its `tree_desc`): zlib keeps the frequency and the code
// in one field, and the parent and the length in another, which here are apart.
struct Tree {
    frequencies: Vec<u32>,
    codes: Vec<u16>,
    parents: Vec<u16>,
    lengths: Vec<u16>,
    max_code: usize,
    elements: usize,
    max_length: usize,
    extra_bits: &'static [usize],
    extra_base: usize,
}

impl Tree {
    fn new(size: usize, elements: usize, max_length: usize, extra_bits: &'static [usize]) -> Tree {
        let extra_base = if elements == LENGTH_SYMBOLS {
            LITERALS + 1
        } else {
            0
        };
        Tree {
            frequencies: vec![0; size],
            codes: vec![0; size],
            parents: vec![0; size],
            lengths: vec![0; size],
            max_code: 0,
            elements,
            max_length,
            extra_bits,
            extra_base,
        }
    }
}

#[derive(Clone, Copy)]
enum TreeKind {
    Literal,
    Distance,
    BitLength,
}

struct State<'a> {
    input: &'a [u8],
    read: usize,
    output: Vec<u8>,
    tables: Tables,
    window: Vec<u8>,
    head: Vec<u16>,
    previous: Vec<u16>,
    insert_hash: usize,
    block_start: isize,
    match_length: usize,
    previous_match: usize,
    match_available: bool,
    string_start: usize,
    match_start: usize,
    lookahead: usize,
    previous_length: usize,
    insert: usize,
    high_water: usize,
    symbols: Vec<u8>,
    literal_tree: Tree,
    distance_tree: Tree,
    bit_length_tree: Tree,
    bit_counts: [u16; MAX_BITS + 1],
    heap: [usize; HEAP_SIZE],
    heap_length: usize,
    heap_max: usize,
    depth: [u8; HEAP_SIZE],
    optimal_length: u64,
    static_length: u64,
    bit_buffer: u16,
    bit_count: usize,
}

impl<'a> State<'a> {
    fn new(input: &'a [u8]) -> State<'a> {
        let mut state = State {
            input,
            read: 0,
            output: Vec::new(),
            tables: Tables::new(),
            window: vec![0; 2 * WINDOW_SIZE],
            head: vec![0; HASH_SIZE],
            previous: vec![0; WINDOW_SIZE],
            insert_hash: 0,
            block_start: 0,
            match_length: MIN_MATCH - 1,
            previous_match: 0,
            match_available: false,
            string_start: 0,
            match_start: 0,
            lookahead: 0,
            previous_length: MIN_MATCH - 1,
            insert: 0,
            high_water: 0,
            symbols: Vec::with_capacity(SYMBOL_END),
            literal_tree: Tree::new(HEAP_SIZE, LENGTH_SYMBOLS, MAX_BITS, &EXTRA_LENGTH_BITS),
            distance_tree: Tree::new(
                2 * DISTANCE_CODES + 1,
                DISTANCE_CODES,
                MAX_BITS,
                &EXTRA_DISTANCE_BITS,
            ),
            bit_length_tree: Tree::new(
                2 * BIT_LENGTH_CODES + 1,
                BIT_LENGTH_CODES,
                MAX_BIT_LENGTH_BITS,
                &EXTRA_BIT_LENGTH_BITS,
            ),
            bit_counts: [0; MAX_BITS + 1],
            heap: [0; HEAP_SIZE],
            heap_length: 0,
            heap_max: 0,
            depth: [0; HEAP_SIZE],
            optimal_length: 0,
            static_length: 0,
            bit_buffer: 0,
            bit_count: 0,
        };
        state.init_block();
        state
    }

    fn tree(&mut self, kind: TreeKind) -> &mut Tree {
        match kind {
            TreeKind::Literal => &mut self.literal_tree,
            TreeKind::Distance => &mut self.distance_tree,
            TreeKind::BitLength => &mut self.bit_length_tree,
        }
    }

    fn update_hash(&mut self, byte: u8) {
        self.insert_hash = ((self.insert_hash << HASH_SHIFT) ^ usize::from(byte)) & HASH_MASK;
    }

    // `INSERT_STRING`: the previous head of the string's chain.
    fn insert_string(&mut self, position: usize) -> usize {
        self.update_hash(self.window[position + MIN_MATCH - 1]);
        let head = self.head[self.insert_hash];
        self.previous[position & WINDOW_MASK] = head;
        self.head[self.insert_hash] = position as u16;
        usize::from(head)
    }

    fn slide_hash(&mut self) {
        for entry in self.head.iter_mut().chain(self.previous.iter_mut()) {
            *entry = if usize::from(*entry) >= WINDOW_SIZE {
                (usize::from(*entry) - WINDOW_SIZE) as u16
            } else {
                0
            };
        }
    }

    fn fill_window(&mut self) {
        loop {
            let mut more = 2 * WINDOW_SIZE - self.lookahead - self.string_start;
            if self.string_start >= WINDOW_SIZE + MAX_DISTANCE {
                self.window
                    .copy_within(WINDOW_SIZE..2 * WINDOW_SIZE - more, 0);
                self.match_start = self.match_start.wrapping_sub(WINDOW_SIZE);
                self.string_start -= WINDOW_SIZE;
                self.block_start -= WINDOW_SIZE as isize;
                if self.insert > self.string_start {
                    self.insert = self.string_start;
                }
                self.slide_hash();
                more += WINDOW_SIZE;
            }
            if self.read == self.input.len() {
                break;
            }
            let count = more.min(self.input.len() - self.read);
            let start = self.string_start + self.lookahead;
            self.window[start..start + count]
                .copy_from_slice(&self.input[self.read..self.read + count]);
            self.read += count;
            self.lookahead += count;
            if self.lookahead + self.insert >= MIN_MATCH {
                let mut position = self.string_start - self.insert;
                self.insert_hash = usize::from(self.window[position]);
                self.update_hash(self.window[position + 1]);
                while self.insert > 0 {
                    self.update_hash(self.window[position + MIN_MATCH - 1]);
                    self.previous[position & WINDOW_MASK] = self.head[self.insert_hash];
                    self.head[self.insert_hash] = position as u16;
                    position += 1;
                    self.insert -= 1;
                    if self.lookahead + self.insert < MIN_MATCH {
                        break;
                    }
                }
            }
            if self.lookahead >= MIN_LOOKAHEAD || self.read == self.input.len() {
                break;
            }
        }
        // zlib zeroes the window just past the data it holds, for the matches that read beyond it.
        let current = self.string_start + self.lookahead;
        if self.high_water < current {
            let end = (current + MAX_MATCH).min(2 * WINDOW_SIZE);
            self.window[current..end].fill(0);
            self.high_water = end;
        } else if self.high_water < current + MAX_MATCH {
            let end = (current + MAX_MATCH).min(2 * WINDOW_SIZE);
            self.window[self.high_water..end].fill(0);
            self.high_water = end;
        }
    }

    fn longest_match(&mut self, mut current_match: usize) -> usize {
        let mut chain_length = MAX_CHAIN;
        let scan = self.string_start;
        let mut best_length = self.previous_length;
        let mut nice_match = NICE_MATCH;
        let limit = self.string_start.saturating_sub(MAX_DISTANCE);
        let string_end = scan + MAX_MATCH;
        let mut scan_end1 = self.window[scan + best_length - 1];
        let mut scan_end = self.window[scan + best_length];
        if self.previous_length >= GOOD_MATCH {
            chain_length >>= 2;
        }
        if nice_match > self.lookahead {
            nice_match = self.lookahead;
        }
        loop {
            let candidate = current_match;
            let window = &self.window;
            if window[candidate + best_length] == scan_end
                && window[candidate + best_length - 1] == scan_end1
                && window[candidate] == window[scan]
                && window[candidate + 1] == window[scan + 1]
            {
                let mut scan_position = scan + 2;
                let mut match_position = candidate + 2;
                loop {
                    scan_position += 1;
                    match_position += 1;
                    if window[scan_position] != window[match_position]
                        || scan_position >= string_end
                    {
                        break;
                    }
                }
                let length = MAX_MATCH - (string_end - scan_position);
                if length > best_length {
                    self.match_start = candidate;
                    best_length = length;
                    if length >= nice_match {
                        break;
                    }
                    scan_end1 = window[scan + best_length - 1];
                    scan_end = window[scan + best_length];
                }
            }
            current_match = usize::from(self.previous[current_match & WINDOW_MASK]);
            if current_match <= limit {
                break;
            }
            chain_length -= 1;
            if chain_length == 0 {
                break;
            }
        }
        best_length.min(self.lookahead)
    }

    // `deflate_slow`, with the input all there and finished.
    fn compress(&mut self) {
        loop {
            if self.lookahead < MIN_LOOKAHEAD {
                self.fill_window();
                if self.lookahead == 0 {
                    break;
                }
            }
            let mut hash_head = 0;
            if self.lookahead >= MIN_MATCH {
                hash_head = self.insert_string(self.string_start);
            }
            self.previous_length = self.match_length;
            self.previous_match = self.match_start;
            self.match_length = MIN_MATCH - 1;
            if hash_head != 0
                && self.previous_length < MAX_LAZY_MATCH
                && self.string_start - hash_head <= MAX_DISTANCE
            {
                self.match_length = self.longest_match(hash_head);
                if self.match_length <= 5
                    && self.match_length == MIN_MATCH
                    && self.string_start - self.match_start > TOO_FAR
                {
                    self.match_length = MIN_MATCH - 1;
                }
            }
            if self.previous_length >= MIN_MATCH && self.match_length <= self.previous_length {
                let max_insert = self.string_start + self.lookahead - MIN_MATCH;
                let is_full = self.tally_distance(
                    self.string_start - 1 - self.previous_match,
                    self.previous_length - MIN_MATCH,
                );
                self.lookahead -= self.previous_length - 1;
                self.previous_length -= 2;
                loop {
                    self.string_start += 1;
                    if self.string_start <= max_insert {
                        self.insert_string(self.string_start);
                    }
                    self.previous_length -= 1;
                    if self.previous_length == 0 {
                        break;
                    }
                }
                self.match_available = false;
                self.match_length = MIN_MATCH - 1;
                self.string_start += 1;
                if is_full {
                    self.flush_block(false);
                }
            } else if self.match_available {
                if self.tally_literal(self.window[self.string_start - 1]) {
                    self.flush_block(false);
                }
                self.string_start += 1;
                self.lookahead -= 1;
            } else {
                self.match_available = true;
                self.string_start += 1;
                self.lookahead -= 1;
            }
        }
        if self.match_available {
            self.tally_literal(self.window[self.string_start - 1]);
            self.match_available = false;
        }
        self.flush_block(true);
    }

    fn tally_literal(&mut self, literal: u8) -> bool {
        self.symbols.extend([0, 0, literal]);
        self.literal_tree.frequencies[usize::from(literal)] += 1;
        self.symbols.len() == SYMBOL_END
    }

    fn tally_distance(&mut self, distance: usize, length: usize) -> bool {
        self.symbols
            .extend([distance as u8, (distance >> 8) as u8, length as u8]);
        let length_code = usize::from(self.tables.length_code[length]);
        self.literal_tree.frequencies[length_code + LITERALS + 1] += 1;
        let distance_code = self.tables.distance_code(distance - 1);
        self.distance_tree.frequencies[distance_code] += 1;
        self.symbols.len() == SYMBOL_END
    }

    fn init_block(&mut self) {
        self.literal_tree.frequencies[..LENGTH_SYMBOLS].fill(0);
        self.distance_tree.frequencies[..DISTANCE_CODES].fill(0);
        self.bit_length_tree.frequencies[..BIT_LENGTH_CODES].fill(0);
        self.literal_tree.frequencies[END_BLOCK] = 1;
        self.optimal_length = 0;
        self.static_length = 0;
        self.symbols.clear();
    }

    fn put_byte(&mut self, byte: u8) {
        self.output.push(byte);
    }

    fn put_short(&mut self, value: u16) {
        self.output.extend(value.to_le_bytes());
    }

    fn send_bits(&mut self, value: u32, length: usize) {
        if self.bit_count > 16 - length {
            self.bit_buffer |= (value << self.bit_count) as u16;
            self.put_short(self.bit_buffer);
            self.bit_buffer = (value >> (16 - self.bit_count)) as u16;
            self.bit_count = self.bit_count + length - 16;
        } else {
            self.bit_buffer |= (value << self.bit_count) as u16;
            self.bit_count += length;
        }
    }

    fn send_code(&mut self, symbol: usize, kind: Option<TreeKind>) {
        let (code, length) = match kind {
            None => (
                self.tables.static_literal_codes[symbol],
                self.tables.static_literal_lengths[symbol],
            ),
            Some(kind) => {
                let tree = self.tree(kind);
                (tree.codes[symbol], tree.lengths[symbol])
            }
        };
        self.send_bits(u32::from(code), usize::from(length));
    }

    fn bit_windup(&mut self) {
        if self.bit_count > 8 {
            self.put_short(self.bit_buffer);
        } else if self.bit_count > 0 {
            self.put_byte(self.bit_buffer as u8);
        }
        self.bit_buffer = 0;
        self.bit_count = 0;
    }

    // `smaller`: by frequency, then by depth.
    fn is_smaller(&self, kind: TreeKind, left: usize, right: usize) -> bool {
        let frequencies = match kind {
            TreeKind::Literal => &self.literal_tree.frequencies,
            TreeKind::Distance => &self.distance_tree.frequencies,
            TreeKind::BitLength => &self.bit_length_tree.frequencies,
        };
        frequencies[left] < frequencies[right]
            || (frequencies[left] == frequencies[right] && self.depth[left] <= self.depth[right])
    }

    fn heap_down(&mut self, kind: TreeKind, mut position: usize) {
        let value = self.heap[position];
        let mut child = position << 1;
        while child <= self.heap_length {
            if child < self.heap_length
                && self.is_smaller(kind, self.heap[child + 1], self.heap[child])
            {
                child += 1;
            }
            if self.is_smaller(kind, value, self.heap[child]) {
                break;
            }
            self.heap[position] = self.heap[child];
            position = child;
            child <<= 1;
        }
        self.heap[position] = value;
    }

    fn generate_bit_lengths(&mut self, kind: TreeKind, uses_static_lengths: bool) {
        self.bit_counts = [0; MAX_BITS + 1];
        let root = self.heap[self.heap_max];
        let tree = match kind {
            TreeKind::Literal => &mut self.literal_tree,
            TreeKind::Distance => &mut self.distance_tree,
            TreeKind::BitLength => &mut self.bit_length_tree,
        };
        tree.lengths[root] = 0;
        let mut overflow: isize = 0;
        let mut index = self.heap_max + 1;
        while index < HEAP_SIZE {
            let node = self.heap[index];
            index += 1;
            let mut bits = usize::from(tree.lengths[usize::from(tree.parents[node])]) + 1;
            if bits > tree.max_length {
                bits = tree.max_length;
                overflow += 1;
            }
            tree.lengths[node] = bits as u16;
            if node > tree.max_code {
                continue;
            }
            self.bit_counts[bits] += 1;
            let extra = if node >= tree.extra_base {
                tree.extra_bits[node - tree.extra_base]
            } else {
                0
            };
            let frequency = u64::from(tree.frequencies[node]);
            self.optimal_length = self
                .optimal_length
                .wrapping_add(frequency * (bits + extra) as u64);
            if uses_static_lengths {
                let static_length = match kind {
                    TreeKind::Literal => usize::from(self.tables.static_literal_lengths[node]),
                    _ => 5,
                };
                self.static_length = self
                    .static_length
                    .wrapping_add(frequency * (static_length + extra) as u64);
            }
        }
        if overflow == 0 {
            return;
        }
        let max_length = tree.max_length;
        loop {
            let mut bits = max_length - 1;
            while self.bit_counts[bits] == 0 {
                bits -= 1;
            }
            self.bit_counts[bits] -= 1;
            self.bit_counts[bits + 1] += 2;
            self.bit_counts[max_length] -= 1;
            overflow -= 2;
            if overflow <= 0 {
                break;
            }
        }
        let mut position = HEAP_SIZE;
        for bits in (1..=max_length).rev() {
            let mut count = self.bit_counts[bits];
            while count != 0 {
                position -= 1;
                let node = self.heap[position];
                if node > tree.max_code {
                    continue;
                }
                if usize::from(tree.lengths[node]) != bits {
                    self.optimal_length = self.optimal_length.wrapping_add(
                        (bits as u64)
                            .wrapping_sub(u64::from(tree.lengths[node]))
                            .wrapping_mul(u64::from(tree.frequencies[node])),
                    );
                    tree.lengths[node] = bits as u16;
                }
                count -= 1;
            }
        }
    }

    fn build_tree(&mut self, kind: TreeKind) {
        let uses_static_lengths = !matches!(kind, TreeKind::BitLength);
        let elements = self.tree(kind).elements;
        self.heap_length = 0;
        self.heap_max = HEAP_SIZE;
        let mut max_code: isize = -1;
        for symbol in 0..elements {
            if self.tree(kind).frequencies[symbol] != 0 {
                self.heap_length += 1;
                self.heap[self.heap_length] = symbol;
                max_code = symbol as isize;
                self.depth[symbol] = 0;
            } else {
                self.tree(kind).lengths[symbol] = 0;
            }
        }
        while self.heap_length < 2 {
            let node = if max_code < 2 {
                max_code += 1;
                max_code as usize
            } else {
                0
            };
            self.heap_length += 1;
            self.heap[self.heap_length] = node;
            self.tree(kind).frequencies[node] = 1;
            self.depth[node] = 0;
            self.optimal_length = self.optimal_length.wrapping_sub(1);
            if uses_static_lengths {
                let static_length = match kind {
                    TreeKind::Literal => u64::from(self.tables.static_literal_lengths[node]),
                    _ => 5,
                };
                self.static_length = self.static_length.wrapping_sub(static_length);
            }
        }
        self.tree(kind).max_code = max_code as usize;
        for position in (1..=self.heap_length / 2).rev() {
            self.heap_down(kind, position);
        }
        let mut node = elements;
        loop {
            let least = self.heap[1];
            self.heap[1] = self.heap[self.heap_length];
            self.heap_length -= 1;
            self.heap_down(kind, 1);
            let next = self.heap[1];
            self.heap_max -= 1;
            self.heap[self.heap_max] = least;
            self.heap_max -= 1;
            self.heap[self.heap_max] = next;
            let tree = self.tree(kind);
            tree.frequencies[node] = tree.frequencies[least] + tree.frequencies[next];
            tree.parents[least] = node as u16;
            tree.parents[next] = node as u16;
            self.depth[node] = self.depth[least].max(self.depth[next]) + 1;
            self.heap[1] = node;
            node += 1;
            self.heap_down(kind, 1);
            if self.heap_length < 2 {
                break;
            }
        }
        self.heap_max -= 1;
        self.heap[self.heap_max] = self.heap[1];
        self.generate_bit_lengths(kind, uses_static_lengths);
        let bit_counts = self.bit_counts;
        let tree = self.tree(kind);
        let codes = generate_codes(&tree.lengths, tree.max_code, &bit_counts);
        let max_code = tree.max_code;
        tree.codes[..=max_code].copy_from_slice(&codes[..=max_code]);
    }

    fn scan_tree(&mut self, kind: TreeKind) {
        let max_code = self.tree(kind).max_code;
        let tree = self.tree(kind);
        tree.lengths[max_code + 1] = 0xffff;
        let lengths: Vec<u16> = tree.lengths[..=max_code + 1].to_vec();
        let frequencies = &mut self.bit_length_tree.frequencies;
        let mut previous_length: i32 = -1;
        let mut next_length = lengths[0];
        let mut count = 0;
        let (mut max_count, mut min_count) = if next_length == 0 { (138, 3) } else { (7, 4) };
        for symbol in 0..=max_code {
            let current_length = next_length;
            next_length = lengths[symbol + 1];
            count += 1;
            if count < max_count && current_length == next_length {
                continue;
            } else if count < min_count {
                frequencies[usize::from(current_length)] += count as u32;
            } else if current_length != 0 {
                if i32::from(current_length) != previous_length {
                    frequencies[usize::from(current_length)] += 1;
                }
                frequencies[REPEAT_3_6] += 1;
            } else if count <= 10 {
                frequencies[REPEAT_ZERO_3_10] += 1;
            } else {
                frequencies[REPEAT_ZERO_11_138] += 1;
            }
            count = 0;
            previous_length = i32::from(current_length);
            (max_count, min_count) = if next_length == 0 {
                (138, 3)
            } else if current_length == next_length {
                (6, 3)
            } else {
                (7, 4)
            };
        }
    }

    fn send_tree(&mut self, kind: TreeKind, max_code: usize) {
        let lengths: Vec<u16> = self.tree(kind).lengths[..=max_code + 1].to_vec();
        let bit_lengths = Some(TreeKind::BitLength);
        let mut previous_length: i32 = -1;
        let mut next_length = lengths[0];
        let mut count = 0;
        let (mut max_count, mut min_count) = if next_length == 0 { (138, 3) } else { (7, 4) };
        for symbol in 0..=max_code {
            let current_length = next_length;
            next_length = lengths[symbol + 1];
            count += 1;
            if count < max_count && current_length == next_length {
                continue;
            } else if count < min_count {
                for _ in 0..count {
                    self.send_code(usize::from(current_length), bit_lengths);
                }
            } else if current_length != 0 {
                if i32::from(current_length) != previous_length {
                    self.send_code(usize::from(current_length), bit_lengths);
                    count -= 1;
                }
                self.send_code(REPEAT_3_6, bit_lengths);
                self.send_bits(count - 3, 2);
            } else if count <= 10 {
                self.send_code(REPEAT_ZERO_3_10, bit_lengths);
                self.send_bits(count - 3, 3);
            } else {
                self.send_code(REPEAT_ZERO_11_138, bit_lengths);
                self.send_bits(count - 11, 7);
            }
            count = 0;
            previous_length = i32::from(current_length);
            (max_count, min_count) = if next_length == 0 {
                (138, 3)
            } else if current_length == next_length {
                (6, 3)
            } else {
                (7, 4)
            };
        }
    }

    fn build_bit_length_tree(&mut self) -> usize {
        self.scan_tree(TreeKind::Literal);
        self.scan_tree(TreeKind::Distance);
        self.build_tree(TreeKind::BitLength);
        let mut max_index = BIT_LENGTH_CODES - 1;
        while max_index >= 3 && self.bit_length_tree.lengths[BIT_LENGTH_ORDER[max_index]] == 0 {
            max_index -= 1;
        }
        self.optimal_length = self
            .optimal_length
            .wrapping_add(3 * (max_index as u64 + 1) + 5 + 5 + 4);
        max_index
    }

    fn send_all_trees(
        &mut self,
        literal_codes: usize,
        distance_codes: usize,
        bit_length_codes: usize,
    ) {
        self.send_bits((literal_codes - 257) as u32, 5);
        self.send_bits((distance_codes - 1) as u32, 5);
        self.send_bits((bit_length_codes - 4) as u32, 4);
        for &symbol in &BIT_LENGTH_ORDER[..bit_length_codes] {
            let length = self.bit_length_tree.lengths[symbol];
            self.send_bits(u32::from(length), 3);
        }
        self.send_tree(TreeKind::Literal, literal_codes - 1);
        self.send_tree(TreeKind::Distance, distance_codes - 1);
    }

    fn compress_block(&mut self, is_static: bool) {
        let literal_kind = (!is_static).then_some(TreeKind::Literal);
        let symbols = std::mem::take(&mut self.symbols);
        for symbol in symbols.chunks(3) {
            let mut distance = usize::from(symbol[0]) | (usize::from(symbol[1]) << 8);
            let length = usize::from(symbol[2]);
            if distance == 0 {
                self.send_code(length, literal_kind);
                continue;
            }
            let code = usize::from(self.tables.length_code[length]);
            self.send_code(code + LITERALS + 1, literal_kind);
            let extra = EXTRA_LENGTH_BITS[code];
            if extra != 0 {
                self.send_bits((length - self.tables.base_length[code]) as u32, extra);
            }
            distance -= 1;
            let code = self.tables.distance_code(distance);
            if is_static {
                self.send_bits(u32::from(self.tables.static_distance_codes[code]), 5);
            } else {
                self.send_code(code, Some(TreeKind::Distance));
            }
            let extra = EXTRA_DISTANCE_BITS[code];
            if extra != 0 {
                self.send_bits((distance - self.tables.base_distance[code]) as u32, extra);
            }
        }
        self.symbols = symbols;
        self.send_code(END_BLOCK, literal_kind);
    }

    fn flush_block(&mut self, is_last: bool) {
        let stored_length = (self.string_start as isize - self.block_start) as usize;
        self.build_tree(TreeKind::Literal);
        self.build_tree(TreeKind::Distance);
        let max_index = self.build_bit_length_tree();
        let mut optimal_bytes = (self.optimal_length.wrapping_add(3 + 7)) >> 3;
        let static_bytes = (self.static_length.wrapping_add(3 + 7)) >> 3;
        if static_bytes <= optimal_bytes {
            optimal_bytes = static_bytes;
        }
        let last = u32::from(is_last);
        if stored_length as u64 + 4 <= optimal_bytes && self.block_start >= 0 {
            self.send_bits(last, 3);
            self.bit_windup();
            self.put_short(stored_length as u16);
            self.put_short(!(stored_length as u16));
            let start = self.block_start as usize;
            self.output
                .extend_from_slice(&self.window[start..start + stored_length]);
        } else if static_bytes == optimal_bytes {
            self.send_bits((1 << 1) + last, 3);
            self.compress_block(true);
        } else {
            self.send_bits((2 << 1) + last, 3);
            self.send_all_trees(
                self.literal_tree.max_code + 1,
                self.distance_tree.max_code + 1,
                max_index + 1,
            );
            self.compress_block(false);
        }
        self.init_block();
        if is_last {
            self.bit_windup();
        }
        self.block_start = self.string_start as isize;
    }
}

/// The CRC-32 of `bytes`, as gzip's trailer holds it.
pub fn crc32(bytes: &[u8]) -> u32 {
    !bytes.iter().fold(!0u32, |crc, &byte| {
        (0..8).fold(crc ^ u32::from(byte), |crc, _| {
            (crc >> 1) ^ (0xedb8_8320 & (crc & 1).wrapping_neg())
        })
    })
}

#[cfg(test)]
mod tests {
    use super::deflate;

    // The streams Python's zlib 1.3 writes at level 6 with a raw 32K window and memory level 8
    // (`compressobj(6, DEFLATED, -15, 8)`), byte for byte: the payloads of trace files TLC wrote,
    // whose streams are the recorded files' own, and inputs that make zlib slide its window, split
    // blocks, choose stored, fixed and dynamic blocks, and match at the longest distance.
    #[test]
    fn deflates_as_zlib_does() {
        let cases: [(&str, Vec<u8>, &[u8]); 9] = [
            (
                "empty",
                Vec::new(),
                include_bytes!("../tests/deflate/empty.deflate"),
            ),
            (
                "byte",
                b"a".to_vec(),
                include_bytes!("../tests/deflate/byte.deflate"),
            ),
            (
                "run",
                vec![b'a'; 100_000],
                include_bytes!("../tests/deflate/run.deflate"),
            ),
            (
                "noise",
                noise(70_000, 1),
                include_bytes!("../tests/deflate/noise.deflate"),
            ),
            (
                "words",
                words(300_000, 7),
                include_bytes!("../tests/deflate/words.deflate"),
            ),
            (
                "payload 002",
                include_bytes!("../tests/deflate/payload-002.bin").to_vec(),
                include_bytes!("../tests/deflate/payload-002.deflate"),
            ),
            (
                "payload 055",
                include_bytes!("../tests/deflate/payload-055.bin").to_vec(),
                include_bytes!("../tests/deflate/payload-055.deflate"),
            ),
            (
                "payload 056",
                include_bytes!("../tests/deflate/payload-056.bin").to_vec(),
                include_bytes!("../tests/deflate/payload-056.deflate"),
            ),
            (
                "payload 118",
                include_bytes!("../tests/deflate/payload-118.bin").to_vec(),
                include_bytes!("../tests/deflate/payload-118.deflate"),
            ),
        ];
        for (name, input, expected) in cases {
            assert!(deflate(&input) == expected, "{name}");
        }
    }

    fn next(state: &mut u64) -> u8 {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        (*state >> 56) as u8
    }

    fn noise(length: usize, seed: u64) -> Vec<u8> {
        let mut state = seed;
        (0..length).map(|_| next(&mut state)).collect()
    }

    fn words(length: usize, seed: u64) -> Vec<u8> {
        const VOCABULARY: [&[u8]; 8] = [
            b"state",
            b"action",
            b"TLC",
            b"counterexample",
            b"\0\0\0\x01",
            b" ",
            b"\x03\0\0\0\x07",
            b"vars",
        ];
        let mut state = seed;
        let mut out = Vec::new();
        while out.len() < length {
            out.extend(VOCABULARY[usize::from(next(&mut state)) % VOCABULARY.len()]);
        }
        out.truncate(length);
        out
    }
}
