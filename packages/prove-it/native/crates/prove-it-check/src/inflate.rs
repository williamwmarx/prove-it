//! DEFLATE (RFC 1951), which a zip archive compresses its entries with: stored blocks and blocks
//! of fixed and dynamic Huffman codes, decoded as zlib's `puff` does.

/// The longest code DEFLATE has.
const MAX_BITS: usize = 15;

/// The base length of the length symbols 257 to 285, and the extra bits that follow each.
const LENGTH_BASES: [u16; 29] = [
    3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131,
    163, 195, 227, 258,
];
const LENGTH_EXTRA: [u8; 29] = [
    0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0,
];
/// The base distance of the distance symbols 0 to 29, and the extra bits that follow each.
const DISTANCE_BASES: [u16; 30] = [
    1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537,
    2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577,
];
const DISTANCE_EXTRA: [u8; 30] = [
    0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13,
    13,
];
/// The order a dynamic block gives the lengths of the code lengths' code in.
const CODE_LENGTH_ORDER: [usize; 19] = [
    16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15,
];

/// The compressed data, read a bit at a time from the least significant bit of each byte.
struct Bits<'a> {
    data: &'a [u8],
    position: usize,
}

impl Bits<'_> {
    fn read(&mut self, count: u8) -> Result<u32, String> {
        (0..count).try_fold(0, |value, index| {
            let byte = self
                .data
                .get(self.position / 8)
                .ok_or("deflated data that ends early")?;
            let bit = u32::from(byte >> (self.position % 8) & 1);
            self.position += 1;
            Ok(value | bit << index)
        })
    }
}

/// A canonical Huffman code: how many codes each length has, and the symbols in code order.
struct Huffman {
    counts: [u16; MAX_BITS + 1],
    symbols: Vec<u16>,
}

impl Huffman {
    /// The code of the symbols' lengths, where 0 leaves a symbol out. A code with more codes of
    /// some length than it has room for is no code.
    fn new(lengths: &[u8]) -> Result<Huffman, String> {
        let mut counts = [0u16; MAX_BITS + 1];
        for &length in lengths {
            counts[usize::from(length)] += 1;
        }
        let mut left = 1i32;
        for &count in &counts[1..] {
            left = left * 2 - i32::from(count);
            if left < 0 {
                return Err("an over-subscribed Huffman code".into());
            }
        }
        let mut offsets = [0u16; MAX_BITS + 1];
        for length in 1..MAX_BITS {
            offsets[length + 1] = offsets[length] + counts[length];
        }
        let mut symbols = vec![0; lengths.len()];
        for (symbol, &length) in lengths.iter().enumerate() {
            if length != 0 {
                let offset = &mut offsets[usize::from(length)];
                symbols[usize::from(*offset)] = symbol as u16;
                *offset += 1;
            }
        }
        Ok(Huffman { counts, symbols })
    }

    fn decode(&self, bits: &mut Bits) -> Result<u16, String> {
        // The first code of each length, and the index of its symbol.
        let (mut code, mut first, mut index) = (0i32, 0i32, 0i32);
        for &count in &self.counts[1..] {
            code |= bits.read(1)? as i32;
            let count = i32::from(count);
            if code - first < count {
                return Ok(self.symbols[(index + code - first) as usize]);
            }
            index += count;
            first = (first + count) << 1;
            code <<= 1;
        }
        Err("a Huffman code that isn't in the code".into())
    }
}

/// The data the deflated `data` holds, which is `size` bytes long.
pub fn inflate(data: &[u8], size: usize) -> Result<Vec<u8>, String> {
    let mut bits = Bits { data, position: 0 };
    let mut output = Vec::with_capacity(size);
    loop {
        let is_last = bits.read(1)? == 1;
        match bits.read(2)? {
            0 => {
                bits.position = bits.position.next_multiple_of(8);
                let length = bits.read(16)?;
                if bits.read(16)? != !length & 0xffff {
                    return Err("a stored block whose length doesn't match its complement".into());
                }
                let start = bits.position / 8;
                let stored = data
                    .get(start..start + length as usize)
                    .ok_or("deflated data that ends early")?;
                output.extend_from_slice(stored);
                bits.position += 8 * stored.len();
            }
            1 => {
                let mut lengths = [8; 288];
                lengths[144..256].fill(9);
                lengths[256..280].fill(7);
                let literals = Huffman::new(&lengths)?;
                let distances = Huffman::new(&[5; 30])?;
                inflate_codes(&mut bits, &mut output, &literals, &distances, size)?;
            }
            2 => {
                let (literals, distances) = read_dynamic_codes(&mut bits)?;
                inflate_codes(&mut bits, &mut output, &literals, &distances, size)?;
            }
            _ => return Err("a deflate block of the reserved type 3".into()),
        }
        if output.len() > size {
            return Err("deflated data longer than its entry says".into());
        }
        if is_last {
            return Ok(output);
        }
    }
}

/// The literal and length code and the distance code a dynamic block starts with.
fn read_dynamic_codes(bits: &mut Bits) -> Result<(Huffman, Huffman), String> {
    let literal_count = bits.read(5)? as usize + 257;
    let distance_count = bits.read(5)? as usize + 1;
    let code_length_count = bits.read(4)? as usize + 4;
    if literal_count > 286 || distance_count > 30 {
        return Err("a dynamic block with too many codes".into());
    }
    let mut code_lengths = [0u8; 19];
    for &symbol in &CODE_LENGTH_ORDER[..code_length_count] {
        code_lengths[symbol] = bits.read(3)? as u8;
    }
    let code_lengths = Huffman::new(&code_lengths)?;
    let mut lengths = Vec::with_capacity(literal_count + distance_count);
    while lengths.len() < literal_count + distance_count {
        let (length, repeat) = match code_lengths.decode(bits)? {
            symbol @ 0..=15 => (symbol as u8, 1),
            16 => {
                let previous = *lengths
                    .last()
                    .ok_or("a repeated code length without one before it")?;
                (previous, 3 + bits.read(2)?)
            }
            17 => (0, 3 + bits.read(3)?),
            _ => (0, 11 + bits.read(7)?),
        };
        if lengths.len() + repeat as usize > literal_count + distance_count {
            return Err("code lengths that repeat past the end of the codes".into());
        }
        lengths.extend(std::iter::repeat_n(length, repeat as usize));
    }
    if lengths[256] == 0 {
        return Err("a dynamic block without a code for its end".into());
    }
    Ok((
        Huffman::new(&lengths[..literal_count])?,
        Huffman::new(&lengths[literal_count..])?,
    ))
}

/// A block's literals and the earlier data its lengths and distances copy, up to its end.
fn inflate_codes(
    bits: &mut Bits,
    output: &mut Vec<u8>,
    literals: &Huffman,
    distances: &Huffman,
    size: usize,
) -> Result<(), String> {
    loop {
        let symbol = usize::from(literals.decode(bits)?);
        if symbol == 256 {
            return Ok(());
        }
        if symbol < 256 {
            output.push(symbol as u8);
        } else {
            let index = symbol - 257;
            let (Some(base), Some(&extra)) = (LENGTH_BASES.get(index), LENGTH_EXTRA.get(index))
            else {
                return Err("a length symbol DEFLATE doesn't have".into());
            };
            let length = usize::from(*base) + bits.read(extra)? as usize;
            let index = usize::from(distances.decode(bits)?);
            let (Some(base), Some(&extra)) = (DISTANCE_BASES.get(index), DISTANCE_EXTRA.get(index))
            else {
                return Err("a distance symbol DEFLATE doesn't have".into());
            };
            let distance = usize::from(*base) + bits.read(extra)? as usize;
            if distance > output.len() {
                return Err("a distance back past the start of the data".into());
            }
            let start = output.len() - distance;
            for offset in 0..length {
                output.push(output[start + offset]);
            }
        }
        if output.len() > size {
            return Err("deflated data longer than its entry says".into());
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Raw deflate streams as zlib writes them. A jar's manifest is in a dynamic Huffman block
    // (`zip::tests`).
    #[test]
    fn inflates_stored_and_fixed_huffman_blocks() {
        assert_eq!(
            inflate(&[1, 6, 0, 249, 255, 115, 116, 111, 114, 101, 100], 6),
            Ok(b"stored".to_vec())
        );
        assert_eq!(
            inflate(&[75, 76, 74, 78, 132, 33, 0], 12),
            Ok(b"abcabcabcabc".to_vec())
        );
        assert_eq!(inflate(&[3, 0], 0), Ok(Vec::new()));
    }

    #[test]
    fn rejects_what_isnt_deflate() {
        assert_eq!(
            inflate(&[75, 76, 74, 78, 132, 33, 0], 11),
            Err("deflated data longer than its entry says".into())
        );
        assert_eq!(
            inflate(&[75, 76, 74], 12),
            Err("deflated data that ends early".into())
        );
        assert_eq!(
            inflate(&[7], 0),
            Err("a deflate block of the reserved type 3".into())
        );
        assert_eq!(
            inflate(&[1, 6, 0, 249, 254], 6),
            Err("a stored block whose length doesn't match its complement".into())
        );
    }
}
