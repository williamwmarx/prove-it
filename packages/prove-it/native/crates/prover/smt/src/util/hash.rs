//! Ported from Z3 (src/util/hash.h, src/util/hash.cpp), MIT license, through `hash.ts`. Bob
//! Jenkins' hash functions, on unsigned 32-bit integers. Z3 hashes every AST with them, and its
//! hash tables iterate in hash order, so matching the hashes matches Z3's iteration order.

const GOLDEN_RATIO: u32 = 0x9e37_79b9;

/// The a, b and c of Z3's mix, which wrap like its unsigned integers.
struct State {
    a: u32,
    b: u32,
    c: u32,
}

impl State {
    fn new(a: u32, b: u32, c: u32) -> State {
        State { a, b, c }
    }

    fn mix(&mut self) {
        let (mut a, mut b, mut c) = (self.a, self.b, self.c);
        a = a.wrapping_sub(b).wrapping_sub(c) ^ (c >> 13);
        b = b.wrapping_sub(c).wrapping_sub(a) ^ (a << 8);
        c = c.wrapping_sub(a).wrapping_sub(b) ^ (b >> 13);
        a = a.wrapping_sub(b).wrapping_sub(c) ^ (c >> 12);
        b = b.wrapping_sub(c).wrapping_sub(a) ^ (a << 16);
        c = c.wrapping_sub(a).wrapping_sub(b) ^ (b >> 5);
        a = a.wrapping_sub(b).wrapping_sub(c) ^ (c >> 3);
        b = b.wrapping_sub(c).wrapping_sub(a) ^ (a << 10);
        c = c.wrapping_sub(a).wrapping_sub(b) ^ (b >> 15);
        *self = State { a, b, c };
    }
}

/// `mkMix`: the c of mixing a, b and c.
pub fn mk_mix(a: u32, b: u32, c: u32) -> u32 {
    let mut state = State::new(a, b, c);
    state.mix();
    state.c
}

/// `hashU`.
pub fn hash_u(value: u32) -> u32 {
    let mut a = value;
    a = a.wrapping_add(0x7ed5_5d16).wrapping_add(a << 12);
    a = a ^ 0xc761_c23c ^ (a >> 19);
    a = a.wrapping_add(0x1656_67b1).wrapping_add(a << 5);
    a = a.wrapping_add(0xd3a2_646c) ^ (a << 9);
    a = a.wrapping_add(0xfd70_46c5).wrapping_add(a << 3);
    a ^ 0xb55a_4f09 ^ (a >> 16)
}

/// `combineHash`.
pub fn combine_hash(first: u32, second: u32) -> u32 {
    hash_u(
        first
            ^ second
                .wrapping_add(GOLDEN_RATIO)
                .wrapping_add(first << 6)
                .wrapping_add(first >> 2),
    )
}

/// string_hash, over bytes: `bytesHash`.
pub fn bytes_hash(data: &[u8], init_value: u32) -> u32 {
    let read_unsigned = |offset: usize| {
        u32::from_le_bytes([
            data[offset],
            data[offset + 1],
            data[offset + 2],
            data[offset + 3],
        ])
    };
    let mut state = State::new(GOLDEN_RATIO, GOLDEN_RATIO, init_value);
    let mut offset = 0;
    let mut rest = data.len();
    while rest >= 12 {
        state.a = state.a.wrapping_add(read_unsigned(offset));
        state.b = state.b.wrapping_add(read_unsigned(offset + 4));
        state.c = state.c.wrapping_add(read_unsigned(offset + 8));
        state.mix();
        offset += 12;
        rest -= 12;
    }
    // Z3's length is an unsigned int.
    state.c = state.c.wrapping_add(data.len() as u32);
    // The low byte of c is reserved for the length.
    const SHIFTS: [u32; 11] = [0, 8, 16, 24, 0, 8, 16, 24, 8, 16, 24];
    for index in (0..rest).rev() {
        let byte = u32::from(data[offset + index]) << SHIFTS[index];
        match index {
            0..4 => state.a = state.a.wrapping_add(byte),
            4..8 => state.b = state.b.wrapping_add(byte),
            _ => state.c = state.c.wrapping_add(byte),
        }
    }
    state.mix();
    state.c
}

/// `stringHash`: over the UTF-8 bytes of a text.
pub fn string_hash(text: &str, init_value: u32) -> u32 {
    bytes_hash(text.as_bytes(), init_value)
}

/// get_composite_hash over child hashes; Z3's default kind hash is 17.
pub fn get_composite_hash(child_hashes: &[u32], kind_hash: u32) -> u32 {
    let mut state = State::new(GOLDEN_RATIO, GOLDEN_RATIO, 11);
    match child_hashes.len() {
        0 => state.c,
        1 => {
            state.a = state.a.wrapping_add(kind_hash);
            state.b = child_hashes[0];
            state.mix();
            state.c
        }
        2 => {
            state.a = state.a.wrapping_add(kind_hash);
            state.b = state.b.wrapping_add(child_hashes[0]);
            state.c = state.c.wrapping_add(child_hashes[1]);
            state.mix();
            state.c
        }
        3 => {
            state.a = state.a.wrapping_add(child_hashes[0]);
            state.b = state.b.wrapping_add(child_hashes[1]);
            state.c = state.c.wrapping_add(child_hashes[2]);
            state.mix();
            state.a = state.a.wrapping_add(kind_hash);
            state.mix();
            state.c
        }
        count => {
            let mut rest = count;
            while rest >= 3 {
                state.a = state.a.wrapping_add(child_hashes[rest - 1]);
                state.b = state.b.wrapping_add(child_hashes[rest - 2]);
                state.c = state.c.wrapping_add(child_hashes[rest - 3]);
                rest -= 3;
                state.mix();
            }
            state.a = state.a.wrapping_add(kind_hash);
            if rest == 2 {
                state.b = state.b.wrapping_add(child_hashes[1]);
            }
            if rest >= 1 {
                state.c = state.c.wrapping_add(child_hashes[0]);
            }
            state.mix();
            state.c
        }
    }
}

/// ast_array_hash: the hash of an AST from the hashes of its children, `get_hash(item)` as Z3's
/// get_hash looks each up.
pub fn ast_array_hash(items: &[u32], get_hash: impl Fn(u32) -> u32, init_value: u32) -> u32 {
    match items.len() {
        0 => init_value,
        1 => combine_hash(get_hash(items[0]), init_value),
        2 => combine_hash(
            combine_hash(get_hash(items[0]), get_hash(items[1])),
            init_value,
        ),
        3 => combine_hash(
            combine_hash(get_hash(items[0]), get_hash(items[1])),
            combine_hash(get_hash(items[2]), init_value),
        ),
        count => {
            let mut state = State::new(GOLDEN_RATIO, GOLDEN_RATIO, init_value);
            let mut rest = count;
            while rest >= 3 {
                state.a = state.a.wrapping_add(get_hash(items[rest - 1]));
                state.b = state.b.wrapping_add(get_hash(items[rest - 2]));
                state.c = state.c.wrapping_add(get_hash(items[rest - 3]));
                rest -= 3;
                state.mix();
            }
            if rest == 2 {
                state.b = state.b.wrapping_add(get_hash(items[1]));
                state.c = state.c.wrapping_add(get_hash(items[0]));
            } else if rest == 1 {
                state.c = state.c.wrapping_add(get_hash(items[0]));
            }
            state.mix();
            state.c
        }
    }
}
