//! The values a binding hands its host and reads from it: what JavaScript gets back from the
//! engine, built once here, which the N-API binding turns into JavaScript values and the
//! WebAssembly binding writes into its memory for its loader.

/// A JavaScript value of the kinds the engine's exports take and give.
#[derive(Clone, Debug, PartialEq)]
pub enum HostValue {
    Undefined,
    Null,
    Bool(bool),
    Number(f64),
    /// A string, as UTF-16 code units.
    Text(Vec<u16>),
    Int32s(Vec<i32>),
    Float64s(Vec<f64>),
    BigInt64s(Vec<i64>),
    Uint8s(Vec<u8>),
    Array(Vec<HostValue>),
    /// An object, with its properties in the order they were set.
    Object(Vec<(&'static str, HostValue)>),
}

impl HostValue {
    pub fn text(text: &str) -> HostValue {
        HostValue::Text(text.encode_utf16().collect())
    }

    pub fn texts(texts: &[Vec<u16>]) -> HostValue {
        HostValue::Array(texts.iter().cloned().map(HostValue::Text).collect())
    }

    /// Counts as JavaScript numbers.
    pub fn counts(values: &[u64]) -> HostValue {
        HostValue::Float64s(values.iter().map(|&value| value as f64).collect())
    }

    pub fn words(values: &[u32]) -> HostValue {
        HostValue::Int32s(values.iter().map(|&value| value as i32).collect())
    }
}
