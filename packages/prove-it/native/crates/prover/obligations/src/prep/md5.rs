//! MD5 (RFC 1321), as OCaml's Digest computes it. tlapm names the operators it coalesces by
//! the digest of their printed form, so matching its SMT-LIB output needs the same digest.
//! A port of `src/prover/prep/md5.ts`.

const SHIFTS: [u32; 16] = [7, 12, 17, 22, 5, 9, 14, 20, 4, 11, 16, 23, 6, 10, 15, 21];

/// `Math.floor(Math.abs(Math.sin(index + 1)) * 2 ** 32)`, precomputed.
const CONSTANTS: [u32; 64] = [
    0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee, 0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501,
    0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be, 0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821,
    0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa, 0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8,
    0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed, 0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a,
    0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c, 0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70,
    0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05, 0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665,
    0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039, 0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1,
    0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1, 0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391,
];

/// The lowercase hex digest of the text's UTF-8 bytes, which is what `TextEncoder` encodes a
/// JavaScript string to (a Rust string has no lone surrogates for it to replace).
pub fn get_md5(text: &str) -> String {
    let message = text.as_bytes();
    let length = (message.len() + 9).div_ceil(64) * 64;
    let mut bytes = vec![0u8; length];
    bytes[..message.len()].copy_from_slice(message);
    bytes[message.len()] = 0x80;
    let bit_length = (message.len() as u64).wrapping_mul(8);
    bytes[length - 8..].copy_from_slice(&bit_length.to_le_bytes());
    let mut state: [u32; 4] = [0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476];
    for block in bytes.as_chunks::<64>().0 {
        let mut words = [0u32; 16];
        for (word, chunk) in words.iter_mut().zip(block.as_chunks::<4>().0) {
            *word = u32::from_le_bytes(*chunk);
        }
        let [mut inner_a, mut inner_b, mut inner_c, mut inner_d] = state;
        for index in 0..64 {
            let round = index / 16;
            let mixed = match round {
                0 => (inner_b & inner_c) | (!inner_b & inner_d),
                1 => (inner_d & inner_b) | (!inner_d & inner_c),
                2 => inner_b ^ inner_c ^ inner_d,
                _ => inner_c ^ (inner_b | !inner_d),
            };
            let word = match round {
                0 => index,
                1 => (5 * index + 1) % 16,
                2 => (3 * index + 5) % 16,
                _ => (7 * index) % 16,
            };
            let sum = inner_a
                .wrapping_add(mixed)
                .wrapping_add(CONSTANTS[index])
                .wrapping_add(words[word]);
            let rotated = sum.rotate_left(SHIFTS[round * 4 + index % 4]);
            (inner_a, inner_b, inner_c, inner_d) =
                (inner_d, inner_b.wrapping_add(rotated), inner_b, inner_c);
        }
        for (word, mixed) in state.iter_mut().zip([inner_a, inner_b, inner_c, inner_d]) {
            *word = word.wrapping_add(mixed);
        }
    }
    state
        .iter()
        .flat_map(|word| word.to_le_bytes())
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `Math.floor(Math.abs(Math.sin(index + 1)) * 2 ** 32)`.
    #[test]
    fn constants_match_the_sine_formula() {
        for (index, constant) in CONSTANTS.iter().enumerate() {
            let computed = ((index as f64 + 1.0).sin().abs() * 2f64.powi(32)).floor();
            assert_eq!(computed, f64::from(*constant), "constant {index}");
        }
    }

    // Digests from Bun, running the TypeScript.
    #[test]
    fn matches_the_typescript() {
        let cases = [
            ("", "d41d8cd98f00b204e9800998ecf8427e"),
            ("a", "0cc175b9c0f1b6a831c399e269772661"),
            ("abc", "900150983cd24fb0d6963f7d28e17f72"),
            ("message digest", "f96b697d7cb7938d525a2f31aaf161d0"),
            (
                "abcdefghijklmnopqrstuvwxyz",
                "c3fcd3d76192e4007dfb496cca67e13b",
            ),
            (
                "12345678901234567890123456789012345678901234567890123456789012345678901234567890",
                "57edf4a22be3c955ac49da2e2107b67a",
            ),
            ("é", "66ddcd97cfdeabb2f6fb8a999b4bc76f"),
            ("∀ x ∈ S : x ≥ 0", "16b95a0fbc6b3d95e4aa8c10faa5acbc"),
            ("😀 emoji", "937948e47e1dfa66901634dea84a7092"),
            ("\0\n\t", "bfb2e95030044c0b1ca6bbbff1307257"),
        ];
        for (text, digest) in cases {
            assert_eq!(get_md5(text), digest, "{text:?}");
        }
    }

    // Lengths around the block boundaries, where the padding spills into another block.
    #[test]
    fn pads_across_block_boundaries() {
        let cases = [
            (55, "04364420e25c512fd958a70738aa8f72"),
            (56, "668a72d5ba17f08e62dabcafad6db14b"),
            (63, "7dc2ca208106a2f703567bdff99d8981"),
            (64, "c1bb4f81d892b2d57947682aeb252456"),
            (65, "1bc932052302d074bdec39795fe00cf6"),
        ];
        for (count, digest) in cases {
            assert_eq!(get_md5(&"x".repeat(count)), digest, "{count}");
        }
    }
}
