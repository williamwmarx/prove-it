use tla_ir::{decode, encode};

fn bytes() -> Vec<u8> {
    std::fs::read(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../../tests/conformance/ir/examples/specifications/transaction_commit/TCommit.ir"
    ))
    .unwrap()
}

#[test]
fn a_next_state_relation_failing_at_a_substituted_constant_round_trips() {
    let mut ir = decode(&bytes()).unwrap();
    assert!(!ir.model.startup.is_next_constant_cast);
    ir.model.startup.is_next_constant_cast = true;
    let decoded = decode(&encode(&ir)).unwrap();
    assert!(decoded.model.startup.is_next_constant_cast);
    assert_eq!(decoded.model.startup, ir.model.startup);
    assert_eq!(decoded.model.next_substitution, ir.model.next_substitution);
}

#[test]
fn an_ir_without_the_cast_encodes_as_before() {
    let bytes = bytes();
    assert_eq!(encode(&decode(&bytes).unwrap()), bytes);
}
