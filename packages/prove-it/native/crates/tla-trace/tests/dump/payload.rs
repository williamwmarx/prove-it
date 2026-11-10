//! The files TLC's `_TLCTrace` writes, read back: gunzipped, and parsed with the grammar of
//! `ValueInputStream.readExternal`, to compare two dumps byte for byte but for the tokens of their
//! `UniqueString`s, the numbers TLC interns a text by in one run, which its reader skips.

use std::collections::HashMap;

/// Whether two gzipped dumps are the same but for their tokens, each file's tokens naming its
/// texts one to one; otherwise the first difference, by the lines of a listing of each.
pub fn compare_dumps(expected: &[u8], actual: &[u8]) -> Result<(), String> {
    let expected = Dump::read(&gunzip(expected)?)?;
    let actual = Dump::read(&gunzip(actual)?)?;
    if expected.bytes == actual.bytes {
        return Ok(());
    }
    let position = expected
        .lines
        .iter()
        .zip(&actual.lines)
        .position(|(expected, actual)| expected != actual)
        .unwrap_or(expected.lines.len().min(actual.lines.len()));
    let context = |lines: &[String]| {
        lines[position.saturating_sub(3).min(lines.len())..]
            .iter()
            .take(6)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n")
    };
    Err(format!(
        "the dumps differ at line {position}:\nexpected:\n{}\nactual:\n{}",
        context(&expected.lines),
        context(&actual.lines),
    ))
}

// A payload with its tokens zeroed, and a listing of it.
struct Dump {
    bytes: Vec<u8>,
    lines: Vec<String>,
}

struct Reader<'a> {
    payload: &'a [u8],
    at: usize,
    bytes: Vec<u8>,
    lines: Vec<String>,
    handles: usize,
    tokens: HashMap<i32, Vec<u8>>,
    texts: HashMap<Vec<u8>, i32>,
}

impl Dump {
    fn read(payload: &[u8]) -> Result<Dump, String> {
        let mut reader = Reader {
            payload,
            at: 0,
            bytes: Vec::new(),
            lines: Vec::new(),
            handles: 0,
            tokens: HashMap::new(),
            texts: HashMap::new(),
        };
        reader.value(0)?;
        if reader.at != payload.len() {
            return Err(format!(
                "{} bytes past the value",
                payload.len() - reader.at
            ));
        }
        Ok(Dump {
            bytes: reader.bytes,
            lines: reader.lines,
        })
    }
}

impl Reader<'_> {
    fn take(&mut self, count: usize) -> Result<&[u8], String> {
        let Some(bytes) = self.payload.get(self.at..self.at + count) else {
            return Err(format!("the payload ends at {}", self.payload.len()));
        };
        self.bytes.extend_from_slice(bytes);
        self.at += count;
        Ok(bytes)
    }

    fn byte(&mut self) -> Result<i8, String> {
        Ok(self.take(1)?[0] as i8)
    }

    fn short(&mut self) -> Result<i16, String> {
        let bytes = self.take(2)?;
        Ok(i16::from_be_bytes([bytes[0], bytes[1]]))
    }

    fn int(&mut self) -> Result<i32, String> {
        let bytes = self.take(4)?;
        Ok(i32::from_be_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]))
    }

    // `ValueInputStream.readNat`.
    fn nat(&mut self) -> Result<i32, String> {
        let high = self.short()?;
        if high >= 0 {
            return Ok(i32::from(high));
        }
        let low = self.short()?;
        Ok(-((i32::from(high) << 16) | i32::from(low as u16)))
    }

    fn handle(&mut self) -> usize {
        self.handles += 1;
        self.handles - 1
    }

    fn line(&mut self, depth: usize, text: String) {
        self.lines.push(format!("{}{text}", "  ".repeat(depth)));
    }

    // `UniqueString.readExternal`: the token, zeroed, which must name one text in the file.
    fn unique(&mut self) -> Result<String, String> {
        let at = self.at;
        let token = self.int()?;
        self.bytes[at..at + 4].fill(0);
        let slot = self.int()?;
        let length = self.int()?;
        let Ok(length) = usize::try_from(length) else {
            return Err(format!("a string of length {length}"));
        };
        let text = self.take(length)?.to_vec();
        if *self.tokens.entry(token).or_insert_with(|| text.clone()) != text
            || *self.texts.entry(text.clone()).or_insert(token) != token
        {
            return Err(format!(
                "token {token} doesn't name {:?} alone",
                String::from_utf8_lossy(&text)
            ));
        }
        Ok(format!(
            "{:?} slot {slot}",
            text.iter()
                .map(|&byte| char::from(byte))
                .collect::<String>()
        ))
    }

    fn reference(&mut self, depth: usize, what: &str) -> Result<(), String> {
        let handle = self.nat()?;
        if handle < 0 || handle as usize >= self.handles {
            return Err(format!(
                "a reference to handle {handle} of {}",
                self.handles
            ));
        }
        self.line(depth, format!("{what}@{handle}"));
        Ok(())
    }

    fn value(&mut self, depth: usize) -> Result<(), String> {
        match self.byte()? {
            // BOOLVALUE, INTVALUE.
            0 => {
                let boolean = self.byte()?;
                self.line(depth, format!("bool {boolean}"));
            }
            1 => {
                let int = self.int()?;
                self.line(depth, format!("int {int}"));
            }
            // STRINGVALUE: the handle follows the string.
            3 => {
                let text = self.unique()?;
                let handle = self.handle();
                self.line(depth, format!("string#{handle} {text}"));
            }
            // RECORDVALUE: the handle, then each field's name, a string or a reference to one.
            4 => {
                let handle = self.handle();
                let length = self.int()?;
                self.line(depth, format!("record#{handle} {length}"));
                for _ in 0..length.unsigned_abs() {
                    match self.byte()? {
                        26 => self.reference(depth + 1, "name")?,
                        _ => {
                            let name_handle = self.handle();
                            let text = self.unique()?;
                            self.line(depth + 1, format!("name#{name_handle} {text}"));
                        }
                    }
                    self.value(depth + 2)?;
                }
            }
            // SETENUMVALUE.
            5 => {
                let handle = self.handle();
                let length = self.int()?;
                self.line(depth, format!("set#{handle} {length}"));
                for _ in 0..length.unsigned_abs() {
                    self.value(depth + 1)?;
                }
            }
            // TUPLEVALUE.
            7 => {
                let handle = self.handle();
                let length = self.nat()?;
                self.line(depth, format!("tuple#{handle} {length}"));
                for _ in 0..length {
                    self.value(depth + 1)?;
                }
            }
            // FCNRCDVALUE: over an interval, its values; else its keys and values.
            9 => {
                let handle = self.handle();
                let length = self.nat()?;
                match self.byte()? {
                    0 => {
                        let (low, high) = (self.int()?, self.int()?);
                        self.line(depth, format!("function#{handle} {length} {low}..{high}"));
                        for _ in 0..length {
                            self.value(depth + 1)?;
                        }
                    }
                    info => {
                        self.line(depth, format!("function#{handle} {length} info {info}"));
                        for _ in 0..length {
                            self.value(depth + 1)?;
                            self.value(depth + 1)?;
                        }
                    }
                }
            }
            // MODELVALUE, INTERVALVALUE, DUMMYVALUE.
            21 => {
                let index = self.short()?;
                self.line(depth, format!("model value {index}"));
            }
            23 => {
                let (low, high) = (self.int()?, self.int()?);
                self.line(depth, format!("interval {low}..{high}"));
            }
            26 => self.reference(depth, "value")?,
            kind => return Err(format!("a value of kind {kind}, which TLC doesn't read")),
        }
        Ok(())
    }
}

/// The member of a gzip file: its header checked, its deflate stream inflated (RFC 1951), and
/// its length checked.
pub fn gunzip(file: &[u8]) -> Result<Vec<u8>, String> {
    if file.len() < 18 || file[..4] != [0x1f, 0x8b, 8, 0] {
        return Err("not a gzip file of no options".into());
    }
    let mut bits = Bits {
        bytes: &file[10..],
        at: 0,
        bit: 0,
    };
    let mut out = Vec::new();
    loop {
        let is_last = bits.read(1)? == 1;
        match bits.read(2)? {
            0 => {
                bits.align();
                let length = bits.read(16)? as usize;
                let complement = bits.read(16)? as usize;
                if length != !complement & 0xffff {
                    return Err("a stored block of a bad length".into());
                }
                for _ in 0..length {
                    out.push(bits.read(8)? as u8);
                }
            }
            1 => {
                let lengths: Vec<u8> = (0..288)
                    .map(|symbol| match symbol {
                        0..=143 => 8,
                        144..=255 => 9,
                        256..=279 => 7,
                        _ => 8,
                    })
                    .collect();
                inflate_block(
                    &mut bits,
                    &Huffman::new(&lengths),
                    &Huffman::new(&[5; 30]),
                    &mut out,
                )?;
            }
            2 => {
                let literals = bits.read(5)? as usize + 257;
                let distances = bits.read(5)? as usize + 1;
                let codes = bits.read(4)? as usize + 4;
                const ORDER: [usize; 19] = [
                    16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15,
                ];
                let mut code_lengths = [0u8; 19];
                for &symbol in &ORDER[..codes] {
                    code_lengths[symbol] = bits.read(3)? as u8;
                }
                let code = Huffman::new(&code_lengths);
                let mut lengths = Vec::with_capacity(literals + distances);
                while lengths.len() < literals + distances {
                    let (repeat, length) = match code.decode(&mut bits)? {
                        symbol @ 0..=15 => (1, symbol as u8),
                        16 => {
                            let Some(&previous) = lengths.last() else {
                                return Err("a repeat of no length".into());
                            };
                            (3 + bits.read(2)?, previous)
                        }
                        17 => (3 + bits.read(3)?, 0),
                        _ => (11 + bits.read(7)?, 0),
                    };
                    lengths.extend(std::iter::repeat_n(length, repeat as usize));
                }
                inflate_block(
                    &mut bits,
                    &Huffman::new(&lengths[..literals]),
                    &Huffman::new(&lengths[literals..]),
                    &mut out,
                )?;
            }
            _ => return Err("a block of a reserved type".into()),
        }
        if is_last {
            break;
        }
    }
    bits.align();
    let trailer = &bits.bytes[bits.at..];
    if trailer.len() != 8 || trailer[4..] != (out.len() as u32).to_le_bytes() {
        return Err("a gzip trailer that doesn't fit the data".into());
    }
    Ok(out)
}

struct Bits<'a> {
    bytes: &'a [u8],
    at: usize,
    bit: u32,
}

impl Bits<'_> {
    fn read(&mut self, count: u32) -> Result<u32, String> {
        let mut value = 0;
        for shift in 0..count {
            let Some(&byte) = self.bytes.get(self.at) else {
                return Err("the deflate stream ends early".into());
            };
            value |= u32::from((byte >> self.bit) & 1) << shift;
            self.bit += 1;
            if self.bit == 8 {
                self.bit = 0;
                self.at += 1;
            }
        }
        Ok(value)
    }

    fn align(&mut self) {
        if self.bit > 0 {
            self.bit = 0;
            self.at += 1;
        }
    }
}

// A canonical Huffman code: how many codes each length has, and the symbols in code order.
struct Huffman {
    counts: [u16; 16],
    symbols: Vec<u16>,
}

impl Huffman {
    fn new(lengths: &[u8]) -> Huffman {
        let mut counts = [0u16; 16];
        for &length in lengths {
            counts[length as usize] += 1;
        }
        counts[0] = 0;
        let mut symbols = Vec::new();
        for length in 1..16 {
            for (symbol, _) in lengths
                .iter()
                .enumerate()
                .filter(|&(_, &symbol_length)| symbol_length == length)
            {
                symbols.push(symbol as u16);
            }
        }
        Huffman { counts, symbols }
    }

    fn decode(&self, bits: &mut Bits<'_>) -> Result<u16, String> {
        let (mut code, mut first, mut index) = (0i32, 0i32, 0i32);
        for length in 1..16 {
            code |= bits.read(1)? as i32;
            let count = i32::from(self.counts[length]);
            if code - count < first {
                return Ok(self.symbols[(index + code - first) as usize]);
            }
            index += count;
            first = (first + count) << 1;
            code <<= 1;
        }
        Err("a code of no symbol".into())
    }
}

fn inflate_block(
    bits: &mut Bits<'_>,
    literals: &Huffman,
    distances: &Huffman,
    out: &mut Vec<u8>,
) -> Result<(), String> {
    const LENGTHS: [(u32, u32); 29] = [
        (3, 0),
        (4, 0),
        (5, 0),
        (6, 0),
        (7, 0),
        (8, 0),
        (9, 0),
        (10, 0),
        (11, 1),
        (13, 1),
        (15, 1),
        (17, 1),
        (19, 2),
        (23, 2),
        (27, 2),
        (31, 2),
        (35, 3),
        (43, 3),
        (51, 3),
        (59, 3),
        (67, 4),
        (83, 4),
        (99, 4),
        (115, 4),
        (131, 5),
        (163, 5),
        (195, 5),
        (227, 5),
        (258, 0),
    ];
    const DISTANCES: [(u32, u32); 30] = [
        (1, 0),
        (2, 0),
        (3, 0),
        (4, 0),
        (5, 1),
        (7, 1),
        (9, 2),
        (13, 2),
        (17, 3),
        (25, 3),
        (33, 4),
        (49, 4),
        (65, 5),
        (97, 5),
        (129, 6),
        (193, 6),
        (257, 7),
        (385, 7),
        (513, 8),
        (769, 8),
        (1025, 9),
        (1537, 9),
        (2049, 10),
        (3073, 10),
        (4097, 11),
        (6145, 11),
        (8193, 12),
        (12289, 12),
        (16385, 13),
        (24577, 13),
    ];
    loop {
        let symbol = literals.decode(bits)? as usize;
        match symbol {
            0..=255 => out.push(symbol as u8),
            256 => return Ok(()),
            _ => {
                let Some(&(base, extra)) = LENGTHS.get(symbol - 257) else {
                    return Err("a length of no code".into());
                };
                let length = base + bits.read(extra)?;
                let Some(&(base, extra)) = DISTANCES.get(distances.decode(bits)? as usize) else {
                    return Err("a distance of no code".into());
                };
                let distance = (base + bits.read(extra)?) as usize;
                if distance > out.len() {
                    return Err("a distance before the start".into());
                }
                for _ in 0..length {
                    out.push(out[out.len() - distance]);
                }
            }
        }
    }
}
