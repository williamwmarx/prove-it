//! TLC's variable coverage (`CountDistinct.HyperLogLog` with 10 bits, message 2779): an estimate
//! of how many distinct values each variable took in the states the search queued, from each
//! value's fingerprint (`Value.fingerPrint(FP64.New())`) with TLC's polynomial (`-fp`). Without
//! `-fp` TLC picks the polynomial at random, and an estimate past a few values may differ
//! between its runs; the binary estimates with the polynomial its banner names: `-fp`'s, or
//! the first without it.

use tla_values::fingerprint::Polynomial;

use crate::value::{Value, elements};

const BOOL_VALUE: u8 = 0;
const INT_VALUE: u8 = 1;
const STRING_VALUE: u8 = 3;
const SET_ENUM_VALUE: u8 = 5;
const FCN_RCD_VALUE: u8 = 9;
const MODEL_VALUE: u8 = 21;

fn push_int(bytes: &mut Vec<u8>, int: i32) {
    bytes.extend_from_slice(&(int as u32).to_le_bytes());
}

/// The bytes TLC extends a fingerprint by for a value, or none for one the port doesn't
/// fingerprint as TLC does.
pub(crate) fn value_bytes(value: &Value, bytes: &mut Vec<u8>) -> Option<()> {
    match value {
        Value::Bool(boolean) => {
            bytes.push(BOOL_VALUE);
            bytes.push(if *boolean { b't' } else { b'f' });
        }
        Value::Int(int) => {
            bytes.push(INT_VALUE);
            push_int(bytes, *int);
        }
        Value::Str(text) => {
            bytes.push(STRING_VALUE);
            push_int(bytes, text.units.len() as i32);
            bytes.extend(text.units.iter().map(|&unit| unit as u8));
        }
        Value::Model(text) => {
            if text.rank < 0 {
                return None;
            }
            bytes.push(MODEL_VALUE);
            push_int(bytes, text.rank + 1);
        }
        Value::Function(function) => {
            bytes.push(FCN_RCD_VALUE);
            push_int(bytes, function.domain.len() as i32);
            for (key, held) in function.domain.iter().zip(&function.range) {
                value_bytes(key, bytes)?;
                value_bytes(held, bytes)?;
            }
        }
        Value::Set(_) | Value::Interval(..) => {
            let elements = elements(value).ok()?;
            bytes.push(SET_ENUM_VALUE);
            push_int(bytes, elements.len() as i32);
            for element in elements.iter() {
                value_bytes(element, bytes)?;
            }
        }
        Value::Lazy(_) | Value::Unsorted(_) | Value::Lambda(_) => return None,
    }
    Some(())
}

// The fingerprints of the IR's encoding agree with these bytes; this keeps the tables honest.
#[cfg(test)]
fn store_length(value: &Value) -> u64 {
    let polynomial = Polynomial::get(0);
    match value {
        Value::Bool(boolean) => polynomial.of_bool(*boolean).1,
        Value::Int(int) => polynomial.of_int(*int).1,
        Value::Str(text) => polynomial.of_string(&text.units).1,
        Value::Model(text) => polynomial.of_model(text.rank).1,
        _ => 0,
    }
}

/// `HyperLogLog(10)`.
struct HyperLogLog {
    registers: Vec<i32>,
}

const BITS: u32 = 10;

impl HyperLogLog {
    fn new() -> HyperLogLog {
        HyperLogLog {
            registers: vec![0; 1 << BITS],
        }
    }

    fn add(&mut self, hash: u64) {
        let index = (hash >> (64 - BITS)) as usize;
        let w = ((hash << BITS) | (1u64 << (BITS - 1))).leading_zeros() as i32 + 1;
        self.registers[index] = self.registers[index].max(w);
    }

    fn count(&self) -> i64 {
        let m = self.registers.len() as f64;
        let alpha = 0.7213 / (1.0 + 1.079 / m);
        let mut z = 0.0;
        for &register in &self.registers {
            // Java's int shift takes its distance modulo 32.
            z += 1.0 / f64::from(1i32.wrapping_shl(register as u32));
        }
        let mut estimate = alpha * m * m / z;
        if estimate <= 2.5 * m {
            let zeros = self
                .registers
                .iter()
                .filter(|&&register| register == 0)
                .count();
            if zeros != 0 {
                estimate = m * (m / zeros as f64).ln();
            }
        } else if estimate > 1.0 / 30.0 * 2f64.powi(64) {
            estimate = -(2f64.powi(64)) * (1.0 - estimate / 2f64.powi(64)).ln();
        }
        // `(int) estimate`, which Java saturates.
        i64::from(estimate as i32)
    }
}

/// The estimates of how many distinct values each variable took in the states the search queued,
/// which a value seen again leaves as they are.
pub(crate) struct Distinct {
    estimates: Vec<HyperLogLog>,
    polynomial: &'static Polynomial,
    bytes: Vec<u8>,
}

impl Distinct {
    /// The values fingerprinted with the polynomial at `polynomial`.
    pub fn new(width: usize, polynomial: usize) -> Distinct {
        Distinct {
            estimates: (0..width).map(|_| HyperLogLog::new()).collect(),
            polynomial: Polynomial::get(polynomial),
            bytes: Vec::new(),
        }
    }

    /// Records a queued state's values; none where one has no fingerprint the port computes.
    pub fn add(&mut self, state: &[Option<Value>]) -> Option<()> {
        for (estimate, value) in self.estimates.iter_mut().zip(state) {
            self.bytes.clear();
            value_bytes(value.as_ref()?, &mut self.bytes)?;
            let fingerprint = self
                .bytes
                .iter()
                .fold(self.polynomial.value(), |fingerprint, &byte| {
                    self.polynomial.extend_byte(fingerprint, byte)
                });
            estimate.add(fingerprint);
        }
        Some(())
    }

    pub fn counts(&self) -> Vec<i64> {
        self.estimates.iter().map(HyperLogLog::count).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn extends_by_the_bytes_the_store_fingerprints() {
        // The store's integers take five bytes.
        let mut bytes = Vec::new();
        value_bytes(&Value::Int(7), &mut bytes).expect("an integer");
        assert_eq!(bytes.len() as u64, store_length(&Value::Int(7)));
    }

    #[test]
    fn counts_few_values_exactly() {
        let mut estimate = HyperLogLog::new();
        assert_eq!(estimate.count(), 0);
        estimate.add(0);
        estimate.add(1 << 63);
        assert_eq!(estimate.count(), 2);
    }
}
