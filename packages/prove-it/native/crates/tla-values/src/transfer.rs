//! States in `src/transfer.ts`'s encoding: a word stream of tagged values and a table of the texts
//! of strings and model values. The writer gives the words `createStateEncoder` gives the
//! interpreter's values of the same ids (`toValue` in `src/engine/convert.ts`), so a checkpoint
//! or a state log written here decodes in TypeScript as one written there. The reader interns a
//! state as `fromValue` interns the decoded values, operation for operation.

use std::collections::HashMap;

use crate::store::{
    Bail, FALSE, Id, KIND_BOOL, KIND_FUNCTION, KIND_INT, KIND_MODEL, KIND_SET, KIND_STRING,
    KIND_TUPLE, SMALL_INT_MAX, Store, TRUE,
};

const FALSE_TAG: i32 = 0;
const TRUE_TAG: i32 = 1;
const INTEGER_TAG: i32 = 2;
const STRING_TAG: i32 = 3;
const MODEL_VALUE_TAG: i32 = 4;
const SET_TAG: i32 = 5;
const FUNCTION_TAG: i32 = 6;
const INTERVAL_FUNCTION_TAG: i32 = 7;

// The positions of TLC's function classes in FUNCTION_CLASSES: none, "lambda", "tuple", "record".
const NO_CLASS: i32 = 0;
const TUPLE_CLASS: i32 = 2;
const RECORD_CLASS: i32 = 3;

#[derive(Debug, Default, PartialEq, Eq)]
pub struct EncodedStates {
    pub words: Vec<i32>,
    pub strings: Vec<Vec<u16>>,
    pub count: u32,
}

/// Writes states, each a slice of ids, into one encoding with one table of texts.
#[derive(Default)]
pub struct StateEncoder {
    encoded: EncodedStates,
    string_indexes: HashMap<Vec<u16>, i32>,
}

impl StateEncoder {
    pub fn new() -> StateEncoder {
        StateEncoder::default()
    }

    pub fn encode(&mut self, store: &Store, state: &[Id]) {
        for &id in state {
            self.encode_value(store, id);
        }
        self.encoded.count += 1;
    }

    pub fn finish(self) -> EncodedStates {
        self.encoded
    }

    fn push_text(&mut self, text: &[u16]) {
        let strings = &mut self.encoded.strings;
        let index = *self.string_indexes.entry(text.to_vec()).or_insert_with(|| {
            strings.push(text.to_vec());
            strings.len() as i32 - 1
        });
        self.encoded.words.push(index);
    }

    fn encode_value(&mut self, store: &Store, id: Id) {
        let size = store.size_of(id);
        match store.kind_of(id) {
            KIND_BOOL => self
                .encoded
                .words
                .push(if id == TRUE { TRUE_TAG } else { FALSE_TAG }),
            KIND_INT => self
                .encoded
                .words
                .extend_from_slice(&[INTEGER_TAG, store.int_of(id)]),
            KIND_STRING => {
                self.encoded.words.push(STRING_TAG);
                self.push_text(store.text_of(id));
            }
            KIND_MODEL => {
                self.encoded.words.push(MODEL_VALUE_TAG);
                self.push_text(store.text_of(id));
            }
            KIND_SET => {
                self.encoded
                    .words
                    .extend_from_slice(&[SET_TAG, size as i32]);
                for index in 0..size {
                    self.encode_value(store, store.element_at(id, index));
                }
            }
            // The interpreter's tuple has the domain 1..n, which the encoding keeps as an
            // interval, except for the empty one.
            KIND_TUPLE if size > 0 => {
                self.encoded.words.extend_from_slice(&[
                    INTERVAL_FUNCTION_TAG,
                    TUPLE_CLASS,
                    1,
                    size as i32,
                ]);
                for index in 0..size {
                    self.encode_value(store, store.get_range_value(id, index));
                }
            }
            kind => {
                let class = if kind == KIND_TUPLE {
                    TUPLE_CLASS
                } else if store.is_record(id) {
                    RECORD_CLASS
                } else {
                    NO_CLASS
                };
                self.encoded
                    .words
                    .extend_from_slice(&[FUNCTION_TAG, class, size as i32]);
                debug_assert!(kind == KIND_TUPLE || kind == KIND_FUNCTION);
                for index in 0..size {
                    let key = store
                        .peek_key(id, index)
                        .expect("a function's key is interned");
                    self.encode_value(store, key);
                }
                for index in 0..size {
                    self.encode_value(store, store.get_range_value(id, index));
                }
            }
        }
    }
}

/// States as the table of the values they hold, each written once, after its parts, as
/// [`StateEncoder`] writes it but with each part as its position in the table, and each state as
/// the positions of its values: a checkpoint of millions of states that share their values takes
/// words for the values, not for every state's copy of them. Interning the values in the table's
/// order interns what is new in the order that decoding the states one by one in `transfer.ts`'s
/// encoding would, so it gives the same ids.
#[derive(Debug, Default, PartialEq, Eq)]
pub struct SharedStates {
    /// The values, `count` of them.
    pub values: EncodedStates,
    /// Each state's values, by position in the table.
    pub states: Vec<i32>,
}

/// Writes states into one [`SharedStates`].
pub struct SharedEncoder {
    encoder: StateEncoder,
    // The position of each id in the table, or -1.
    positions: Vec<i32>,
    states: Vec<i32>,
}

impl SharedEncoder {
    pub fn new(store: &Store) -> SharedEncoder {
        SharedEncoder {
            encoder: StateEncoder::new(),
            positions: vec![-1; store.value_count()],
            states: Vec::new(),
        }
    }

    pub fn encode(&mut self, store: &Store, state: &[Id]) {
        for &id in state {
            let position = self.write(store, id);
            self.states.push(position);
        }
    }

    pub fn finish(self) -> SharedStates {
        SharedStates {
            values: self.encoder.finish(),
            states: self.states,
        }
    }

    fn push(&mut self, words: &[i32]) -> i32 {
        let encoded = &mut self.encoder.encoded;
        encoded.words.extend_from_slice(words);
        encoded.count += 1;
        encoded.count as i32 - 1
    }

    fn write_parts(&mut self, store: &Store, parts: impl Iterator<Item = Id>) -> Vec<i32> {
        parts.map(|part| self.write(store, part)).collect()
    }

    // The value's position, writing it and the parts not yet written first.
    fn write(&mut self, store: &Store, id: Id) -> i32 {
        let known = self.positions[id as usize];
        if known != -1 {
            return known;
        }
        let size = store.size_of(id);
        let position = match store.kind_of(id) {
            KIND_BOOL | KIND_INT => {
                self.encoder.encode_value(store, id);
                self.encoder.encoded.count += 1;
                self.encoder.encoded.count as i32 - 1
            }
            kind @ (KIND_STRING | KIND_MODEL) => {
                let tag = if kind == KIND_STRING {
                    STRING_TAG
                } else {
                    MODEL_VALUE_TAG
                };
                self.encoder.encoded.words.push(tag);
                self.encoder.push_text(store.text_of(id));
                self.encoder.encoded.count += 1;
                self.encoder.encoded.count as i32 - 1
            }
            KIND_SET => {
                let elements =
                    self.write_parts(store, (0..size).map(|index| store.element_at(id, index)));
                self.push(&[&[SET_TAG, size as i32][..], &elements].concat())
            }
            // A reader interns an interval's keys before its values, so the keys a reset store
            // doesn't hold already are written first.
            KIND_TUPLE if size > 0 => {
                for key in SMALL_INT_MAX + 1..=size as i32 {
                    self.push(&[INTEGER_TAG, key]);
                }
                let values = self.write_parts(
                    store,
                    (0..size).map(|index| store.get_range_value(id, index)),
                );
                self.push(
                    &[
                        &[INTERVAL_FUNCTION_TAG, TUPLE_CLASS, 1, size as i32][..],
                        &values,
                    ]
                    .concat(),
                )
            }
            kind => {
                let class = if kind == KIND_TUPLE {
                    TUPLE_CLASS
                } else if store.is_record(id) {
                    RECORD_CLASS
                } else {
                    NO_CLASS
                };
                let keys = self.write_parts(
                    store,
                    (0..size).map(|index| {
                        store
                            .peek_key(id, index)
                            .expect("a function's key is interned")
                    }),
                );
                let values = self.write_parts(
                    store,
                    (0..size).map(|index| store.get_range_value(id, index)),
                );
                self.push(&[&[FUNCTION_TAG, class, size as i32][..], &keys, &values].concat())
            }
        };
        self.positions[id as usize] = position;
        position
    }
}

/// Reads [`SharedStates`] of `width` values each and interns their values in the table's order.
pub fn decode_shared_states(
    store: &mut Store,
    shared: &SharedStates,
    width: usize,
) -> Result<Vec<Id>, DecodeError> {
    let encoded = &shared.values;
    let mut reader = Reader {
        words: &encoded.words,
        strings: &encoded.strings,
        index: 0,
    };
    let mut ids: Vec<Id> = Vec::with_capacity(encoded.count as usize);
    for _ in 0..encoded.count {
        let id = reader.read_shared(store, &ids)?;
        ids.push(id);
    }
    if reader.index != encoded.words.len() {
        return Err(DecodeError::Malformed("words follow the last value"));
    }
    if !shared.states.len().is_multiple_of(width.max(1)) {
        return Err(DecodeError::Malformed("a state cut short"));
    }
    shared
        .states
        .iter()
        .map(|&position| {
            usize::try_from(position)
                .ok()
                .and_then(|position| ids.get(position).copied())
                .ok_or(DecodeError::Malformed("a position outside the table"))
        })
        .collect()
}

/// Why words couldn't be read as states.
#[derive(Debug, PartialEq, Eq)]
pub enum DecodeError {
    /// The store stopped, as `fromValue` would have.
    Bail(Bail),
    Malformed(&'static str),
}

impl From<Bail> for DecodeError {
    fn from(bail: Bail) -> DecodeError {
        DecodeError::Bail(bail)
    }
}

/// Reads `count` states of `width` values each and interns them, as `fromValue` interns each
/// decoded value: a value's parts first, a function's keys before its values.
pub fn decode_states(
    store: &mut Store,
    encoded: &EncodedStates,
    width: usize,
) -> Result<Vec<Id>, DecodeError> {
    let mut reader = Reader {
        words: &encoded.words,
        strings: &encoded.strings,
        index: 0,
    };
    let mut ids = Vec::with_capacity(encoded.count as usize * width);
    for _ in 0..encoded.count as usize * width {
        ids.push(reader.read_value(store)?);
    }
    if reader.index != encoded.words.len() {
        return Err(DecodeError::Malformed("words follow the last state"));
    }
    Ok(ids)
}

struct Reader<'a> {
    words: &'a [i32],
    strings: &'a [Vec<u16>],
    index: usize,
}

impl Reader<'_> {
    fn next(&mut self) -> Result<i32, DecodeError> {
        let word = *self
            .words
            .get(self.index)
            .ok_or(DecodeError::Malformed("the words end inside a value"))?;
        self.index += 1;
        Ok(word)
    }

    // A length of values to read, each of which takes a word at least.
    fn next_length(&mut self) -> Result<usize, DecodeError> {
        let length = usize::try_from(self.next()?)
            .map_err(|_| DecodeError::Malformed("a negative length"))?;
        if length > self.words.len() - self.index {
            return Err(DecodeError::Malformed("a length past the words"));
        }
        Ok(length)
    }

    fn next_text(&mut self) -> Result<&[u16], DecodeError> {
        let index = self.next()?;
        usize::try_from(index)
            .ok()
            .and_then(|index| self.strings.get(index))
            .map(Vec::as_slice)
            .ok_or(DecodeError::Malformed("a string outside the table"))
    }

    fn read_values(&mut self, store: &mut Store, length: usize) -> Result<Vec<Id>, DecodeError> {
        (0..length).map(|_| self.read_value(store)).collect()
    }

    // Parts, each the position of a value read before.
    fn read_parts(&mut self, ids: &[Id], length: usize) -> Result<Vec<Id>, DecodeError> {
        (0..length)
            .map(|_| {
                let position = self.next()?;
                usize::try_from(position)
                    .ok()
                    .and_then(|position| ids.get(position).copied())
                    .ok_or(DecodeError::Malformed("a part not read before"))
            })
            .collect()
    }

    fn read_shared(&mut self, store: &mut Store, ids: &[Id]) -> Result<Id, DecodeError> {
        match self.words.get(self.index) {
            Some(&SET_TAG) => {
                self.index += 1;
                let length = self.next_length()?;
                let elements = self.read_parts(ids, length)?;
                Ok(store.set_of(&elements)?)
            }
            Some(&FUNCTION_TAG) => {
                self.index += 2;
                let length = self.next_length()?;
                let keys = self.read_parts(ids, length)?;
                let values = self.read_parts(ids, length)?;
                Ok(store.function_of(&keys, &values)?)
            }
            Some(&INTERVAL_FUNCTION_TAG) => {
                self.index += 2;
                let low = i64::from(self.next()?);
                let length = self.next_length()?;
                let keys = (0..length as i64)
                    .map(|offset| store.int(low + offset))
                    .collect::<Result<Vec<Id>, Bail>>()?;
                let values = self.read_parts(ids, length)?;
                Ok(store.function_of(&keys, &values)?)
            }
            _ => self.read_value(store),
        }
    }

    fn read_value(&mut self, store: &mut Store) -> Result<Id, DecodeError> {
        match self.next()? {
            FALSE_TAG => Ok(FALSE),
            TRUE_TAG => Ok(TRUE),
            INTEGER_TAG => Ok(store.int(i64::from(self.next()?))?),
            STRING_TAG => {
                let text = self.next_text()?;
                Ok(store.str(text))
            }
            MODEL_VALUE_TAG => {
                let text = self.next_text()?;
                Ok(store.model(text))
            }
            SET_TAG => {
                let length = self.next_length()?;
                let elements = self.read_values(store, length)?;
                Ok(store.set_of(&elements)?)
            }
            FUNCTION_TAG => {
                self.next()?;
                let length = self.next_length()?;
                let keys = self.read_values(store, length)?;
                let values = self.read_values(store, length)?;
                Ok(store.function_of(&keys, &values)?)
            }
            INTERVAL_FUNCTION_TAG => {
                self.next()?;
                let low = i64::from(self.next()?);
                let length = self.next_length()?;
                let keys = (0..length as i64)
                    .map(|offset| store.int(low + offset))
                    .collect::<Result<Vec<Id>, Bail>>()?;
                let values = self.read_values(store, length)?;
                Ok(store.function_of(&keys, &values)?)
            }
            _ => Err(DecodeError::Malformed("an unknown tag")),
        }
    }
}
