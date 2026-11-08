// TLC's FP64 (FP64.Polys[0]) on real 64-bit integers, against the TypeScript one, which keeps it
// as two 32-bit halves.
use std::time::Instant;

const POLY: u64 = 0x911498ae0e66bad6;

pub struct Fp64 { table: [u64; 256] }

#[derive(Clone)]
pub enum V { Bool(bool), Int(i32), Str(String), Set(Vec<V>), Fcn(Vec<(V, V)>) }

impl Fp64 {
    pub fn new() -> Fp64 {
        let mut table = [0u64; 256];
        let mut power: u64 = 1 << 63;
        for exponent in 1..72 {
            let is_reduced = power & 1 != 0;
            power = (power >> 1) ^ if is_reduced { POLY } else { 0 };
            if exponent < 64 { continue; }
            let bit = 1usize << (71 - exponent);
            for byte in 0..256 { if byte & bit != 0 { table[byte] ^= power; } }
        }
        Fp64 { table }
    }
    #[inline(always)]
    pub fn byte(&self, fp: u64, byte: u8) -> u64 { (fp >> 8) ^ self.table[((byte as u64 ^ fp) & 0xff) as usize] }
    #[inline(always)]
    pub fn int(&self, mut fp: u64, word: i32) -> u64 {
        let mut x = word as u32;
        for _ in 0..4 { fp = self.byte(fp, x as u8); x >>= 8; }
        fp
    }
    pub fn value(&self, fp: u64, value: &V) -> u64 {
        match value {
            V::Bool(b) => { let fp = self.byte(fp, 0); self.byte(fp, if *b { 116 } else { 102 }) }
            V::Int(i) => { let fp = self.byte(fp, 1); self.int(fp, *i) }
            V::Str(s) => {
                let mut fp = self.int(self.byte(fp, 3), s.encode_utf16().count() as i32);
                for unit in s.encode_utf16() { fp = self.byte(fp, unit as u8); }
                fp
            }
            V::Set(elements) => {
                let mut fp = self.int(self.byte(fp, 5), elements.len() as i32);
                for element in elements { fp = self.value(fp, element); }
                fp
            }
            V::Fcn(pairs) => {
                let mut fp = self.int(self.byte(fp, 9), pairs.len() as i32);
                for (key, value) in pairs { fp = self.value(self.value(fp, key), value); }
                fp
            }
        }
    }
    pub fn state(&self, state: &[V]) -> u64 { state.iter().fold(POLY, |fp, value| self.value(fp, value)) }
}

pub fn sample() -> Vec<V> {
    vec![
        V::Int(7), V::Int(-2147483648), V::Str("hello".into()), V::Bool(true),
        V::Set(vec![V::Int(1), V::Int(2), V::Int(3)]),
        V::Fcn(vec![(V::Str("a".into()), V::Int(1)), (V::Str("b".into()), V::Str("x".into()))]),
        V::Fcn(vec![(V::Int(1), V::Str("p".into())), (V::Int(2), V::Str("q".into()))]),
    ]
}

pub fn bench() {
    let fp = Fp64::new();
    println!("sample fingerprint {}", fp.state(&sample()) as i64);
    // A million states of five small integers, as a state of counters would be.
    let started = Instant::now();
    let mut sink = 0u64;
    for state in 0..1_000_000i32 {
        let mut f = POLY;
        for variable in 0..5 { f = fp.int(fp.byte(f, 1), state.wrapping_mul(variable + 1) & 1023); }
        sink ^= f;
    }
    let ms = started.elapsed().as_secs_f64() * 1e3;
    println!("rust fp64: 1M states of 5 ints in {ms:.1} ms ({:.1} ns/state), sink {}", ms, sink as i64);
}
