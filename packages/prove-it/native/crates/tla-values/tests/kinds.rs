//! A function TLC keeps lazy, and Nat, Int or STRING, which the store holds as scalars: what
//! doesn't model them refuses them at any depth rather than reading them as empty.

use tla_values::fingerprint::{Fingerprints, Polynomial, UNFINGERPRINTABLE};
use tla_values::json::write_json;
use tla_values::print::{format_value, is_printable};
use tla_values::store::{Id, NAT, Store};
use tla_values::transfer::{SharedEncoder, StateEncoder, UNENCODABLE};

// Each value in a tuple, a set and a record, and the value itself.
fn nested(store: &mut Store, value: Id) -> Vec<Id> {
    let field = store.str(&"a".encode_utf16().collect::<Vec<u16>>());
    let tuple = store.tuple_of(&[value]);
    let set = store.set_of(&[value]).unwrap();
    let record = store.function_of(&[field], &[value]).unwrap();
    vec![value, tuple, set, record]
}

#[test]
fn refuse_a_function_tlc_keeps_lazy_at_any_depth() {
    let mut store = Store::new();
    let lazy = store.lazy_function(0);
    for value in nested(&mut store, lazy) {
        assert!(write_json(&store, value, &mut Vec::new()).is_err());
        assert!(!is_printable(&store, value));
        assert!(format_value(&store, value).is_err());
        assert_eq!(
            StateEncoder::new().encode(&store, &[value]),
            Err(UNENCODABLE)
        );
        assert_eq!(
            SharedEncoder::new(&store).encode(&store, &[value]),
            Err(UNENCODABLE)
        );
        assert_eq!(
            Fingerprints::new(Polynomial::get(0)).get_state(&store, &[value], &[0]),
            Err(UNFINGERPRINTABLE)
        );
    }
}

#[test]
fn print_nat_as_tlc_does_and_refuse_it_where_tlc_fails() {
    let mut store = Store::new();
    let nat = store.infinite_set(NAT);
    let expected = ["Nat", "<<Nat>>", "{Nat}", "[a |-> Nat]"];
    for (value, text) in nested(&mut store, nat).into_iter().zip(expected) {
        assert!(is_printable(&store, value));
        assert_eq!(format_value(&store, value).unwrap(), text);
        // TLC's Json module can't convert a UserValue.
        assert!(write_json(&store, value, &mut Vec::new()).is_err());
        assert_eq!(
            StateEncoder::new().encode(&store, &[value]),
            Err(UNENCODABLE)
        );
        assert_eq!(
            Fingerprints::new(Polynomial::get(0)).get_state(&store, &[value], &[0]),
            Err(UNFINGERPRINTABLE)
        );
    }
}

#[test]
fn refuse_membership_in_what_isnt_a_set() {
    let mut store = Store::new();
    let one = store.int(1).unwrap();
    let lazy = store.lazy_function(0);
    let tuple = store.tuple_of(&[one]);
    for set in [lazy, tuple, one] {
        assert!(store.is_member(one, set).is_err());
    }
    let nat = store.infinite_set(NAT);
    assert_eq!(store.is_member(one, nat), Ok(true));
}
