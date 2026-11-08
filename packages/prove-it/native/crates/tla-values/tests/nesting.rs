//! Values nested 100,000 deep, past where the TypeScript store runs out of stack, compare, test
//! for equality, fingerprint and go through the transfer encoding on `on_nesting_stack`, in any
//! build, a debug one included.

use tla_values::fingerprint::Fingerprints;
use tla_values::on_nesting_stack;
use tla_values::store::{Id, Store};
use tla_values::transfer::{StateEncoder, decode_states};

const DEPTH: usize = 100_000;

// <<<<...<<value>>...>>>>, as deep as DEPTH.
fn nest(store: &mut Store, value: i64) -> Id {
    let mut id = store.int(value).unwrap();
    for _ in 0..DEPTH {
        id = store.tuple_of(&[id]);
    }
    id
}

#[test]
#[cfg_attr(miri, ignore)]
fn hold_values_nested_past_the_typescript_stores_stack() {
    on_nesting_stack(|| {
        let mut store = Store::new();
        let (left, right) = (nest(&mut store, 1), nest(&mut store, 2));
        assert_eq!(store.compare(left, right), Ok(-1));
        assert_eq!(store.equals(left, right), Ok(false));
        let mut fingerprints = Fingerprints::new();
        let fingerprint = fingerprints.get_state(&store, &[left], &[0]);
        let mut encoder = StateEncoder::new();
        encoder.encode(&store, &[left]);
        let encoded = encoder.finish();
        let mut other = Store::new();
        let read = decode_states(&mut other, &encoded, 1).unwrap();
        assert_eq!(
            Fingerprints::new().get_state(&other, &read, &[0]),
            fingerprint
        );
    });
}
