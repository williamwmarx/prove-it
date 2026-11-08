//! transfer.ts's encoding of states: what the writer gives, and the reader interning it back.

use tla_values::store::{Id, Store, TRUE};
use tla_values::transfer::{
    DecodeError, EncodedStates, SharedEncoder, SharedStates, StateEncoder, decode_shared_states,
    decode_states,
};

fn utf16(text: &str) -> Vec<u16> {
    text.encode_utf16().collect()
}

#[test]
fn writes_what_create_state_encoder_writes() {
    let mut store = Store::new();
    let (one, two) = (store.int(1).unwrap(), store.int(2).unwrap());
    let (a, b) = (store.str(&utf16("a")), store.str(&utf16("b")));
    let model = store.model(&utf16("m"));
    let record = store.function_of(&[a, b], &[one, a]).unwrap();
    let zero = store.int(0).unwrap();
    let function = store.function_of(&[zero, one], &[two, model]).unwrap();
    let tuple = store.tuple_of(&[TRUE, one]);
    let set = store.set_of(&[two, one]).unwrap();
    let empty = store.tuple_of(&[]);
    let mut encoder = StateEncoder::new();
    encoder.encode(&store, &[record, function, tuple, set, empty]);
    encoder.encode(&store, &[a, model, one, b, TRUE]);
    let encoded = encoder.finish();
    #[rustfmt::skip]
    let words = vec![
        6, 3, 2, 3, 0, 3, 1, 2, 1, 3, 0, // [a |-> 1, b |-> "a"], a record
        6, 0, 2, 2, 0, 2, 1, 2, 2, 4, 2, // (0 :> 2 @@ 1 :> m), a function
        7, 2, 1, 2, 1, 2, 1,             // <<TRUE, 1>>, a tuple over the interval 1..2
        5, 2, 2, 1, 2, 2,                // {1, 2}
        6, 2, 0,                         // <<>>, a tuple that isn't over an interval
        3, 0, 4, 2, 2, 1, 3, 1, 1,       // "a", m, 1, "b", TRUE
    ];
    assert_eq!(encoded.words, words);
    assert_eq!(encoded.strings, [utf16("a"), utf16("b"), utf16("m")]);
    assert_eq!(encoded.count, 2);
}

#[test]
fn reads_states_back_as_the_same_values() {
    let mut store = Store::new();
    let ids: Vec<Id> = (0..40)
        .map(|value| store.int(value * 1000).unwrap())
        .collect();
    let long = store.tuple_of(&ids);
    // A lone surrogate, which JavaScript's strings may hold.
    let keys = [store.str(&utf16("x")), store.str(&[0xd800])];
    let shape = store.create_record_shape(&keys);
    let record = store.record_of(&shape, &[long, keys[1]]);
    let set = store.set_of(&[record, long, ids[3]]).unwrap_or(ids[3]);
    let state = [record, long, set, TRUE];
    let mut encoder = StateEncoder::new();
    encoder.encode(&store, &state);
    let encoded = encoder.finish();
    assert_eq!(decode_states(&mut store, &encoded, 4), Ok(state.to_vec()));
    // Into another store, where the same values get ids of their own.
    let mut other = Store::new();
    let decoded = decode_states(&mut other, &encoded, 4).unwrap();
    let mut again = StateEncoder::new();
    again.encode(&other, &decoded);
    assert_eq!(again.finish(), encoded);
}

// States that share values, nested, and a tuple longer than the integers a reset store holds.
fn shared_states(store: &mut Store) -> Vec<Vec<Id>> {
    let a = store.str(&utf16("a"));
    let model = store.model(&utf16("m"));
    let small: Vec<Id> = (0..3).map(|value| store.int(value).unwrap()).collect();
    let pair = store.set_of(&[small[1], a]).unwrap_or(small[1]);
    let record = store.function_of(&[a], &[pair]).unwrap();
    let long: Vec<Id> = (0..5000)
        .map(|value| store.int(value * 7).unwrap())
        .collect();
    let tuple = store.tuple_of(&long);
    let nested = store.tuple_of(&[record, tuple, record]);
    let set = store.set_of(&[record, nested, model]).unwrap_or(model);
    vec![
        vec![record, nested, small[0]],
        vec![set, record, pair],
        vec![record, nested, small[0]],
        vec![model, tuple, a],
    ]
}

#[test]
fn shares_values_and_interns_them_as_the_states_would() {
    let mut store = Store::new();
    let states = shared_states(&mut store);
    let mut encoder = StateEncoder::new();
    let mut shared = SharedEncoder::new(&store);
    for state in &states {
        encoder.encode(&store, state);
        shared.encode(&store, state);
    }
    let (encoded, shared) = (encoder.finish(), shared.finish());
    // The long tuple is written once, rather than in three of the states.
    assert!(shared.values.words.len() * 5 < encoded.words.len() * 3);
    assert_eq!(shared.states.len(), states.len() * 3);
    // Each state's values in a store of their own, and the order of what each decoding interns,
    // which gives the same ids.
    let (mut one, mut other) = (Store::new(), Store::new());
    let decoded = decode_states(&mut one, &encoded, 3).unwrap();
    assert_eq!(
        decode_shared_states(&mut other, &shared, 3),
        Ok(decoded.clone())
    );
    assert_eq!(other.value_count(), one.value_count());
    let mut again = StateEncoder::new();
    for state in decoded.chunks(3) {
        again.encode(&other, state);
    }
    assert_eq!(again.finish(), encoded);
}

#[test]
fn refuses_a_table_that_is_not_states() {
    let mut store = Store::new();
    let decode = |store: &mut Store, words: Vec<i32>, states: Vec<i32>| {
        let values = EncodedStates {
            words,
            strings: vec![],
            count: 1,
        };
        decode_shared_states(store, &SharedStates { values, states }, 1)
    };
    assert_eq!(
        decode(&mut store, vec![5, 1, 0], vec![0]),
        Err(DecodeError::Malformed("a part not read before"))
    );
    assert_eq!(
        decode(&mut store, vec![1], vec![1]),
        Err(DecodeError::Malformed("a position outside the table"))
    );
    assert_eq!(
        decode(&mut store, vec![1, 1], vec![0]),
        Err(DecodeError::Malformed("words follow the last value"))
    );
}

#[test]
fn refuses_words_that_are_not_states() {
    let mut store = Store::new();
    let count = store.value_count();
    let decode = |store: &mut Store, words: Vec<i32>| {
        decode_states(
            store,
            &EncodedStates {
                words,
                strings: vec![],
                count: 1,
            },
            1,
        )
    };
    assert_eq!(
        decode(&mut store, vec![5, 1, 2]),
        Err(DecodeError::Malformed("the words end inside a value"))
    );
    assert_eq!(
        decode(&mut store, vec![7, 0, 1, i32::MAX]),
        Err(DecodeError::Malformed("a length past the words"))
    );
    assert_eq!(
        decode(&mut store, vec![3, 0]),
        Err(DecodeError::Malformed("a string outside the table"))
    );
    assert_eq!(
        decode(&mut store, vec![9]),
        Err(DecodeError::Malformed("an unknown tag"))
    );
    assert_eq!(
        decode(&mut store, vec![1, 1]),
        Err(DecodeError::Malformed("words follow the last state"))
    );
    // Nothing was interned for the interval function of 2^31 - 1 keys.
    assert_eq!(store.value_count(), count);
}
