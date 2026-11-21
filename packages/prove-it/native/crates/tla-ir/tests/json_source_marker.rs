use tla_ir::{Builtin, IR_VERSION, decode, encode};

fn ir() -> tla_ir::Ir {
    let bytes = std::fs::read(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../../tests/conformance/ir/examples/specifications/transaction_commit/TCommit.ir"
    ))
    .unwrap();
    decode(&bytes).unwrap()
}

fn marker(ir: &mut tla_ir::Ir, name: &str) -> Builtin {
    let index = ir.texts.len() as u32;
    ir.texts.push(name.into());
    Builtin {
        name: index,
        arity: 1,
        flags: Builtin::PINNED_STANDARD_SOURCES,
        table: vec![],
    }
}

#[test]
fn only_json_conversion_markers_roundtrip() {
    let mut ir = ir();
    for name in ["ToJson", "ToJsonArray", "ToJsonObject"] {
        let marker = marker(&mut ir, name);
        ir.builtins.push(marker.clone());
        assert_eq!(decode(&encode(&ir)).unwrap().builtins.last(), Some(&marker));
        ir.builtins.last_mut().unwrap().flags |= Builtin::STATE_LEVEL;
        assert!(decode(&encode(&ir)).is_ok());
    }
}

#[test]
fn other_opcodes_and_wrong_arity_are_rejected() {
    for name in ["F", "\\in", "TLCDefer", "PrintT", "JsonSerialize", ""] {
        let mut ir = ir();
        let marker = marker(&mut ir, name);
        ir.builtins.push(marker);
        assert!(decode(&encode(&ir)).is_err());
    }
    for arity in [-1, 0, 2] {
        let mut ir = ir();
        let mut marker = marker(&mut ir, "ToJson");
        marker.arity = arity;
        ir.builtins.push(marker);
        assert!(decode(&encode(&ir)).is_err());
    }
}

#[test]
fn other_certificates_flags_and_table_rows_are_rejected() {
    for extra in [
        Builtin::LEVEL_CONSTANT,
        Builtin::LAZY,
        Builtin::TABLE,
        Builtin::DECLINED,
        Builtin::EXTERNAL_CLASS,
        Builtin::PACKAGED_TLC_DEFER,
        Builtin::CLOSED_JAVA_CONTEXT,
        Builtin::TABLE_PHASE_KNOWN,
        1 << 29,
    ] {
        let mut ir = ir();
        let mut marker = marker(&mut ir, "ToJson");
        marker.flags |= extra;
        ir.builtins.push(marker);
        assert!(decode(&encode(&ir)).is_err());
    }
}

#[test]
fn legacy_unrelated_bits_and_version_rejection_are_preserved() {
    let mut ir = ir();
    let mut legacy = marker(&mut ir, "F");
    legacy.flags = 1 << 29;
    ir.builtins.push(legacy.clone());
    assert_eq!(decode(&encode(&ir)).unwrap().builtins.last(), Some(&legacy));
    let marker = marker(&mut ir, "ToJsonObject");
    *ir.builtins.last_mut().unwrap() = marker;
    let original = encode(&ir);
    for version in [0, 15, IR_VERSION + 100] {
        let mut bytes = original.clone();
        bytes[4..8].copy_from_slice(&version.to_le_bytes());
        assert!(decode(&bytes).is_err());
    }
}
