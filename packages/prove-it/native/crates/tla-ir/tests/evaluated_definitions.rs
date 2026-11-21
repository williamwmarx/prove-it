use tla_ir::{EvaluatedDefinition, decode, encode};

fn ir() -> tla_ir::Ir {
    let bytes = std::fs::read(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../../tests/conformance/ir/examples/specifications/transaction_commit/TCommit.ir"
    ))
    .unwrap();
    decode(&bytes).unwrap()
}

#[test]
fn what_tlc_eval_definition_finds_round_trips() {
    let mut ir = ir();
    let name = ir.texts.len() as u32;
    ir.texts.push("D".into());
    let signature = ir.texts.len() as u32;
    ir.texts.push("F(a, Op(_,_))".into());
    ir.model.evaluated_definitions = vec![
        (name, EvaluatedDefinition::Body(0)),
        (name, EvaluatedDefinition::Signature(signature)),
        (name, EvaluatedDefinition::Missing),
    ];
    let decoded = decode(&encode(&ir)).unwrap();
    assert_eq!(
        decoded.model.evaluated_definitions,
        ir.model.evaluated_definitions
    );
    assert_eq!(decoded.model.tlc_spec, ir.model.tlc_spec);
}

#[test]
fn a_definition_past_the_ir_is_rejected() {
    let mut ir = ir();
    let name = ir.texts.len() as u32;
    ir.texts.push("D".into());
    let past = ir.definitions.len() as u32;
    ir.model.evaluated_definitions = vec![(name, EvaluatedDefinition::Body(past))];
    assert!(decode(&encode(&ir)).is_err());
}

#[test]
fn an_ir_without_lookups_encodes_as_before() {
    let bytes = std::fs::read(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../../tests/conformance/ir/examples/specifications/transaction_commit/TCommit.ir"
    ))
    .unwrap();
    let ir = decode(&bytes).unwrap();
    assert!(ir.model.evaluated_definitions.is_empty());
    assert_eq!(encode(&ir), bytes);
}
