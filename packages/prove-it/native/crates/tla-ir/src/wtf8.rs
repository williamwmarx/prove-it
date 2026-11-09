//! WTF-8, the IR's encoding of its texts: UTF-8 that also encodes a lone surrogate, as a code
//! point of three bytes, since a JavaScript string, and a string TLC computes, can hold one.

/// Appends UTF-16 code units in WTF-8.
pub fn encode(units: &[u16], out: &mut Vec<u8>) {
    for decoded in char::decode_utf16(units.iter().copied()) {
        let point = match decoded {
            Ok(character) => u32::from(character),
            Err(error) => u32::from(error.unpaired_surrogate()),
        };
        match point {
            0..0x80 => out.push(point as u8),
            0x80..0x800 => out.extend([0xC0 | (point >> 6) as u8, 0x80 | (point & 0x3F) as u8]),
            0x800..0x10000 => out.extend([
                0xE0 | (point >> 12) as u8,
                0x80 | ((point >> 6) & 0x3F) as u8,
                0x80 | (point & 0x3F) as u8,
            ]),
            _ => out.extend([
                0xF0 | (point >> 18) as u8,
                0x80 | ((point >> 12) & 0x3F) as u8,
                0x80 | ((point >> 6) & 0x3F) as u8,
                0x80 | (point & 0x3F) as u8,
            ]),
        }
    }
}

/// The code point that starts at `bytes[at]` and its length in bytes, or `None` where the bytes
/// aren't WTF-8 there.
fn decode_point(bytes: &[u8], at: usize) -> Option<(u32, usize)> {
    let lead = *bytes.get(at)?;
    let (length, initial, minimum) = match lead {
        0x00..0x80 => return Some((u32::from(lead), 1)),
        0xC2..0xE0 => (2, u32::from(lead & 0x1F), 0x80),
        0xE0..0xF0 => (3, u32::from(lead & 0x0F), 0x800),
        0xF0..0xF5 => (4, u32::from(lead & 0x07), 0x10000),
        _ => return None,
    };
    let point = bytes
        .get(at + 1..at + length)?
        .iter()
        .try_fold(initial, |point, &byte| {
            (byte & 0xC0 == 0x80).then_some((point << 6) | u32::from(byte & 0x3F))
        })?;
    (minimum..=0x10FFFF)
        .contains(&point)
        .then_some((point, length))
}

/// The UTF-16 code units of WTF-8 bytes, or the offset where they aren't WTF-8. A surrogate pair
/// written as two code points isn't, as WTF-8 has it, since it would read back as one.
pub fn decode(bytes: &[u8]) -> Result<Vec<u16>, usize> {
    let mut units = Vec::with_capacity(bytes.len());
    let mut at = 0;
    while at < bytes.len() {
        let (point, length) = decode_point(bytes, at).ok_or(at)?;
        let is_trail = (0xDC00..0xE000).contains(&point);
        if is_trail
            && units
                .last()
                .is_some_and(|&unit| (0xD800..0xDC00).contains(&unit))
        {
            return Err(at);
        }
        match point {
            0x10000.. => {
                let offset = point - 0x10000;
                units.extend([
                    0xD800 | (offset >> 10) as u16,
                    0xDC00 | (offset & 0x3FF) as u16,
                ]);
            }
            _ => units.push(point as u16),
        }
        at += length;
    }
    Ok(units)
}
