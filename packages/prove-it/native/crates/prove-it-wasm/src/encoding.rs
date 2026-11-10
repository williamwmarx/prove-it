//! The format a call's arguments and results take in the module's memory, little-endian: a tag
//! byte, then 0 undefined, 1 null, 2 false and 3 true with nothing; 4 a number as an f64; and,
//! after a u32 count, 5 a string's UTF-16 units, 6 an Int32Array's, 7 a Float64Array's, 8 a
//! BigInt64Array's and 9 a Uint8Array's elements, 10 an array's values and 11 an object's
//! properties, each a key's length and units and then its value.

use prove_it_host::value::HostValue;

const UNDEFINED: u8 = 0;
const NULL: u8 = 1;
const FALSE: u8 = 2;
const TRUE: u8 = 3;
const NUMBER: u8 = 4;
const TEXT: u8 = 5;
const INT32S: u8 = 6;
const FLOAT64S: u8 = 7;
const BIGINT64S: u8 = 8;
const UINT8S: u8 = 9;
const ARRAY: u8 = 10;
const OBJECT: u8 = 11;

fn put_count(out: &mut Vec<u8>, count: usize) {
    out.extend((count as u32).to_le_bytes());
}

fn put_units(out: &mut Vec<u8>, units: impl ExactSizeIterator<Item = u16>) {
    put_count(out, units.len());
    for unit in units {
        out.extend(unit.to_le_bytes());
    }
}

/// Appends a value to `out`.
pub fn encode(value: &HostValue, out: &mut Vec<u8>) {
    macro_rules! elements {
        ($tag:expr, $values:expr) => {{
            out.push($tag);
            put_count(out, $values.len());
            for value in $values {
                out.extend(value.to_le_bytes());
            }
        }};
    }
    match value {
        HostValue::Undefined => out.push(UNDEFINED),
        HostValue::Null => out.push(NULL),
        HostValue::Bool(false) => out.push(FALSE),
        HostValue::Bool(true) => out.push(TRUE),
        HostValue::Number(number) => {
            out.push(NUMBER);
            out.extend(number.to_le_bytes());
        }
        HostValue::Text(units) => {
            out.push(TEXT);
            put_units(out, units.iter().copied());
        }
        HostValue::Int32s(values) => elements!(INT32S, values),
        HostValue::Float64s(values) => elements!(FLOAT64S, values),
        HostValue::BigInt64s(values) => elements!(BIGINT64S, values),
        HostValue::Uint8s(values) => elements!(UINT8S, values),
        HostValue::Array(elements) => {
            out.push(ARRAY);
            put_count(out, elements.len());
            for element in elements {
                encode(element, out);
            }
        }
        HostValue::Object(properties) => {
            out.push(OBJECT);
            put_count(out, properties.len());
            for (name, property) in properties {
                put_units(out, name.encode_utf16().collect::<Vec<_>>().into_iter());
                encode(property, out);
            }
        }
    }
}

struct Reader<'a> {
    bytes: &'a [u8],
}

impl Reader<'_> {
    fn take<const N: usize>(&mut self) -> Result<[u8; N], String> {
        let (taken, rest) = self
            .bytes
            .split_first_chunk::<N>()
            .ok_or_else(|| "the arguments end too soon".to_owned())?;
        self.bytes = rest;
        Ok(*taken)
    }

    fn take_many<const N: usize, T>(
        &mut self,
        from_bytes: fn([u8; N]) -> T,
    ) -> Result<Vec<T>, String> {
        let count = u32::from_le_bytes(self.take()?) as usize;
        if self.bytes.len() < count.saturating_mul(N) {
            return Err("the arguments end too soon".into());
        }
        (0..count).map(|_| self.take().map(from_bytes)).collect()
    }

    fn read(&mut self) -> Result<HostValue, String> {
        Ok(match self.take::<1>()?[0] {
            UNDEFINED => HostValue::Undefined,
            NULL => HostValue::Null,
            FALSE => HostValue::Bool(false),
            TRUE => HostValue::Bool(true),
            NUMBER => HostValue::Number(f64::from_le_bytes(self.take()?)),
            TEXT => HostValue::Text(self.take_many(u16::from_le_bytes)?),
            INT32S => HostValue::Int32s(self.take_many(i32::from_le_bytes)?),
            FLOAT64S => HostValue::Float64s(self.take_many(f64::from_le_bytes)?),
            BIGINT64S => HostValue::BigInt64s(self.take_many(i64::from_le_bytes)?),
            UINT8S => HostValue::Uint8s(self.take_many(u8::from_le_bytes)?),
            ARRAY => {
                let count = u32::from_le_bytes(self.take()?);
                HostValue::Array((0..count).map(|_| self.read()).collect::<Result<_, _>>()?)
            }
            tag => return Err(format!("{tag} tags no argument")),
        })
    }
}

/// The value `bytes` holds, which mustn't be an object: arguments have none.
pub fn decode(bytes: &[u8]) -> Result<HostValue, String> {
    let mut reader = Reader { bytes };
    let value = reader.read()?;
    if !reader.bytes.is_empty() {
        return Err("the arguments run on past their value".into());
    }
    Ok(value)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decodes_what_it_encodes() {
        let value = HostValue::Array(vec![
            HostValue::Undefined,
            HostValue::Null,
            HostValue::Bool(true),
            HostValue::Number(-1.5),
            HostValue::text("é∀"),
            HostValue::Int32s(vec![-1, 2]),
            HostValue::Float64s(vec![0.25]),
            HostValue::BigInt64s(vec![i64::MIN]),
            HostValue::Uint8s(vec![7]),
            HostValue::Array(Vec::new()),
        ]);
        let mut bytes = Vec::new();
        encode(&value, &mut bytes);
        assert_eq!(decode(&bytes), Ok(value));
    }

    #[test]
    fn writes_objects_by_property() {
        let mut bytes = Vec::new();
        encode(&HostValue::Object(vec![("a", HostValue::Null)]), &mut bytes);
        assert_eq!(bytes, [OBJECT, 1, 0, 0, 0, 1, 0, 0, 0, b'a', 0, NULL]);
    }

    #[test]
    fn rejects_what_is_cut_short() {
        assert!(decode(&[INT32S, 9, 0, 0, 0, 1]).is_err());
        assert!(decode(&[NULL, NULL]).is_err());
        assert!(decode(&[OBJECT, 0, 0, 0, 0]).is_err());
    }
}
