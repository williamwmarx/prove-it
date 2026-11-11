//! Ported from OCaml: LGPL-2.1 with OCaml's linking exception, not MIT (THIRD_PARTY_NOTICES.md).
//! OCaml's Marshal format, ported from runtime/intern.c and runtime/extern.c, for the values in
//! tlapm's fingerprints file. It writes no sharing, which OCaml reads the same. A port of
//! `src/prover/tlapm/ocaml-marshal.ts`.
//!
//! A shared value read back is the same block, by `Rc`, as the TypeScript hands out the same object:
//! a small input that shares a block many times stays small once read.

use std::rc::Rc;

use crate::errors::{ObligationError, Result};

/// An OCaml value: an immediate int, a string, a block with a tag and fields, or a float.
#[derive(Clone, Debug, PartialEq)]
pub enum MarshalValue {
    Int(i64),
    Text(String),
    Block(Rc<MarshalBlock>),
    Float(f64),
}

#[derive(Clone, Debug, PartialEq)]
pub struct MarshalBlock {
    pub tag: u8,
    pub fields: Vec<MarshalValue>,
}

const MAGIC_NUMBER_SMALL: u32 = 0x8495a6be;

const CODE_INT8: u8 = 0x0;
const CODE_INT16: u8 = 0x1;
const CODE_INT32: u8 = 0x2;
const CODE_SHARED8: u8 = 0x4;
const CODE_SHARED16: u8 = 0x5;
const CODE_SHARED32: u8 = 0x6;
const CODE_BLOCK32: u8 = 0x8;
const CODE_STRING8: u8 = 0x9;
const CODE_STRING32: u8 = 0xa;
const CODE_DOUBLE_LITTLE: u8 = 0xc;

const PREFIX_SMALL_INT: u8 = 0x40;
const PREFIX_SMALL_STRING: u8 = 0x20;
const PREFIX_SMALL_BLOCK: u8 = 0x80;

const HEADER_SIZE: usize = 20;

// How high a value may be: the longest path down its blocks, through shared references too, which
// bounds the reader's recursion and the recursion of dropping, comparing and writing the value.
// intern.c reads with its own stack and has no bound; the TypeScript recurses until JavaScript's
// stack runs out. A higher value is corrupt here rather than a stack overflow, which in Rust aborts
// the process; 256 levels drop and compare within a 2 MB thread's stack in a debug build. The deepest nesting in tlapm's files is a hash bucket's
// chain, a few fingerprints long.
const MAX_DEPTH: usize = 256;

// How many bytes a value may take written out, which `write_marshaled` does without sharing: a
// block shared many times is written as often as it is referenced, so a few bytes of shared
// references can stand for gigabytes, which writing, comparing or dropping it would then walk. A
// fingerprints file tlapm writes grows by a tenth or so, as it shares only strings, small blocks
// and versions; above this it is corrupt here. The TypeScript has no bound and runs out of memory.
const MAX_WRITTEN_SIZE: usize = 1 << 28;

pub fn block(tag: u8, fields: Vec<MarshalValue>) -> MarshalValue {
    MarshalValue::Block(Rc::new(MarshalBlock { tag, fields }))
}

fn corrupted() -> ObligationError {
    ObligationError::proof("corrupted fingerprint file")
}

/// A value read, with its height (the longest path down its blocks, shared ones included) and the
/// bytes it takes written without sharing.
#[derive(Clone)]
struct Measured {
    value: MarshalValue,
    height: usize,
    size: usize,
}

impl Measured {
    fn new(value: MarshalValue, size: usize) -> Measured {
        Measured {
            value,
            height: 0,
            size,
        }
    }
}

/// The values read so far that a shared code can refer to: blocks with fields, strings and floats,
/// in the order they started, as intern.c numbers them.
struct Reader<'b> {
    bytes: &'b [u8],
    position: usize,
    end: usize,
    objects: Vec<Option<Measured>>,
    depth: usize,
}

impl Reader<'_> {
    fn take(&mut self, length: usize) -> Result<&[u8]> {
        let start = self.position;
        self.position = match start.checked_add(length) {
            Some(position) if position <= self.end => position,
            _ => return Err(corrupted()),
        };
        // The header's length can claim more than the file holds.
        self.bytes.get(start..self.position).ok_or_else(corrupted)
    }

    fn take_array<const N: usize>(&mut self) -> Result<[u8; N]> {
        let bytes = self.take(N)?;
        Ok(bytes.try_into().expect("take returns the length asked"))
    }

    fn read_string(&mut self, length: usize) -> Result<Measured> {
        let text = String::from_utf8_lossy(self.take(length)?).into_owned();
        let size = get_text_header_size(text.len()) + text.len();
        let measured = Measured::new(MarshalValue::Text(text), size);
        self.objects.push(Some(measured.clone()));
        Ok(measured)
    }

    fn read_block(&mut self, tag: u8, size: usize) -> Result<Measured> {
        if self.depth == MAX_DEPTH {
            return Err(corrupted());
        }
        self.depth += 1;
        // A block is numbered when it starts and complete once its fields are read; a shared
        // reference to it from inside itself cannot occur in what extern.c writes without cycles.
        let index = self.objects.len();
        if size > 0 {
            self.objects.push(None);
        }
        // Each field takes a byte at least, so a header claiming more fields than bytes remain is
        // corrupt; reserving for it could exhaust memory.
        if size > self.end - self.position {
            return Err(corrupted());
        }
        let mut fields = Vec::with_capacity(size);
        let mut height = 1;
        let mut written_size = get_block_header_size(tag, size);
        for _ in 0..size {
            let field = self.read()?;
            fields.push(field.value);
            height = height.max(field.height + 1);
            written_size = written_size.saturating_add(field.size);
        }
        // Shared references can stack blocks higher, and repeat them more, than the encoding does.
        if height > MAX_DEPTH || written_size > MAX_WRITTEN_SIZE {
            return Err(corrupted());
        }
        self.depth -= 1;
        let measured = Measured {
            value: block(tag, fields),
            height,
            size: written_size,
        };
        if size > 0 {
            self.objects[index] = Some(measured.clone());
        }
        Ok(measured)
    }

    fn read_shared(&self, distance: usize) -> Result<Measured> {
        self.objects
            .len()
            .checked_sub(distance)
            .and_then(|index| self.objects.get(index).cloned().flatten())
            .ok_or_else(corrupted)
    }

    fn read(&mut self) -> Result<Measured> {
        let code = self.take(1)?[0];
        if code >= PREFIX_SMALL_BLOCK {
            return self.read_block(code & 0xf, usize::from((code >> 4) & 0x7));
        }
        if code >= PREFIX_SMALL_INT {
            return Ok(get_int(i64::from(code & 0x3f)));
        }
        if code >= PREFIX_SMALL_STRING {
            return self.read_string(usize::from(code & 0x1f));
        }
        match code {
            CODE_INT8 => Ok(get_int(i64::from(i8::from_be_bytes(self.take_array()?)))),
            CODE_INT16 => Ok(get_int(i64::from(i16::from_be_bytes(self.take_array()?)))),
            CODE_INT32 => Ok(get_int(i64::from(i32::from_be_bytes(self.take_array()?)))),
            CODE_SHARED8 => {
                let distance = usize::from(u8::from_be_bytes(self.take_array()?));
                self.read_shared(distance)
            }
            CODE_SHARED16 => {
                let distance = usize::from(u16::from_be_bytes(self.take_array()?));
                self.read_shared(distance)
            }
            CODE_SHARED32 => {
                let distance = u32::from_be_bytes(self.take_array()?) as usize;
                self.read_shared(distance)
            }
            CODE_BLOCK32 => {
                let header = u32::from_be_bytes(self.take_array()?);
                self.read_block((header & 0xff) as u8, (header >> 10) as usize)
            }
            CODE_STRING8 => {
                let length = usize::from(u8::from_be_bytes(self.take_array()?));
                self.read_string(length)
            }
            CODE_STRING32 => {
                let length = u32::from_be_bytes(self.take_array()?) as usize;
                self.read_string(length)
            }
            CODE_DOUBLE_LITTLE => {
                let float = f64::from_le_bytes(self.take_array()?);
                let measured = Measured::new(MarshalValue::Float(float), 9);
                self.objects.push(Some(measured.clone()));
                Ok(measured)
            }
            _ => Err(corrupted()),
        }
    }
}

/// readMarshaled: the value marshaled at `offset`, and where the next one starts.
pub fn read_marshaled(bytes: &[u8], offset: usize) -> Result<(MarshalValue, usize)> {
    let get_word = |at: usize| {
        bytes
            .get(at..at + 4)
            .map(|word| u32::from_be_bytes(word.try_into().expect("four bytes")))
    };
    if bytes.len() < offset + HEADER_SIZE || get_word(offset) != Some(MAGIC_NUMBER_SMALL) {
        return Err(corrupted());
    }
    let length = get_word(offset + 4).ok_or_else(corrupted)? as usize;
    let end = (offset + HEADER_SIZE)
        .checked_add(length)
        .ok_or_else(corrupted)?;
    let mut reader = Reader {
        bytes,
        position: offset + HEADER_SIZE,
        end,
        objects: Vec::new(),
        depth: 0,
    };
    Ok((reader.read()?.value, end))
}

fn get_int(integer: i64) -> Measured {
    Measured::new(MarshalValue::Int(integer), get_int_size(integer))
}

// The bytes `write` takes for each kind of value: an int, a string's header and a block's header.
fn get_int_size(integer: i64) -> usize {
    match integer {
        0..0x40 => 1,
        -0x80..0x80 => 2,
        -0x8000..0x8000 => 3,
        _ => 5,
    }
}

fn get_text_header_size(length: usize) -> usize {
    match length {
        0..0x20 => 1,
        0x20..0x100 => 2,
        _ => 5,
    }
}

fn get_block_header_size(tag: u8, size: usize) -> usize {
    if tag < 16 && size < 8 { 1 } else { 5 }
}

#[derive(Default)]
struct Sizes {
    objects: u32,
    words32: u32,
    words64: u32,
}

// The bytes of `integer`'s low `length` bytes, most significant first, as `>>>` takes them from a
// 32-bit integer.
fn push_integer(bytes: &mut Vec<u8>, integer: i64, length: u32) {
    let word = integer as u32;
    for shift in (0..length).rev() {
        bytes.push((word >> (shift * 8)) as u8);
    }
}

fn write(bytes: &mut Vec<u8>, sizes: &mut Sizes, value: &MarshalValue) {
    match value {
        MarshalValue::Int(integer) => {
            let integer = *integer;
            if (0..0x40).contains(&integer) {
                bytes.push(PREFIX_SMALL_INT + integer as u8);
            } else if (-0x80..0x80).contains(&integer) {
                bytes.extend([CODE_INT8, integer as u8]);
            } else if (-0x8000..0x8000).contains(&integer) {
                bytes.push(CODE_INT16);
                push_integer(bytes, integer, 2);
            } else {
                bytes.push(CODE_INT32);
                push_integer(bytes, integer, 4);
            }
        }
        MarshalValue::Text(text) => {
            sizes.objects += 1;
            let encoded = text.as_bytes();
            let length = encoded.len();
            if length < 0x20 {
                bytes.push(PREFIX_SMALL_STRING + length as u8);
            } else if length < 0x100 {
                bytes.extend([CODE_STRING8, length as u8]);
            } else {
                bytes.push(CODE_STRING32);
                push_integer(bytes, length as i64, 4);
            }
            bytes.extend_from_slice(encoded);
            sizes.words32 += 1 + (length as u32 + 4) / 4;
            sizes.words64 += 1 + (length as u32 + 8) / 8;
        }
        MarshalValue::Float(float) => {
            sizes.objects += 1;
            bytes.push(CODE_DOUBLE_LITTLE);
            bytes.extend(float.to_le_bytes());
            sizes.words32 += 3;
            sizes.words64 += 2;
        }
        MarshalValue::Block(inner) => {
            let size = inner.fields.len();
            if size > 0 {
                sizes.objects += 1;
                sizes.words32 += 1 + size as u32;
                sizes.words64 += 1 + size as u32;
            }
            if inner.tag < 16 && size < 8 {
                bytes.push(PREFIX_SMALL_BLOCK + inner.tag + ((size as u8) << 4));
            } else {
                bytes.push(CODE_BLOCK32);
                push_integer(bytes, size as i64 * 1024 + i64::from(inner.tag), 4);
            }
            for field in &inner.fields {
                write(bytes, sizes, field);
            }
        }
    }
}

/// writeMarshaled: the value with its header, without sharing.
pub fn write_marshaled(value: &MarshalValue) -> Vec<u8> {
    let mut data = Vec::new();
    let mut sizes = Sizes::default();
    write(&mut data, &mut sizes, value);
    let mut bytes = Vec::with_capacity(HEADER_SIZE + data.len());
    for field in [
        MAGIC_NUMBER_SMALL,
        data.len() as u32,
        sizes.objects,
        sizes.words32,
        sizes.words64,
    ] {
        bytes.extend(field.to_be_bytes());
    }
    bytes.extend(data);
    bytes
}
