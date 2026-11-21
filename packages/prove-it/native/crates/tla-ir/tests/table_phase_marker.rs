use tla_ir::{Builtin, IR_VERSION, Value, decode, encode};
fn ir() -> tla_ir::Ir {
    let bytes = std::fs::read(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../../tests/conformance/ir/examples/specifications/transaction_commit/TCommit.ir"
    ))
    .unwrap();
    decode(&bytes).unwrap()
}
fn table(ir: &mut tla_ir::Ir, name: &str) -> Builtin {
    let text = ir.texts.len() as u32;
    ir.texts.push(name.into());
    let row = ir.values.list.len() as u32;
    ir.values.list.push(Value::IntervalFunction {
        class: 2,
        low: 1,
        range: vec![Value::Int(1)],
    });
    Builtin {
        name: text,
        arity: 1,
        flags: Builtin::TABLE | Builtin::TABLE_PHASE_KNOWN,
        table: vec![(Some(row), None), (None, None)],
    }
}
#[test]
fn generic_table_names_and_missing_data_roundtrip() {
    let mut ir = ir();
    for name in ["F", "G", "ToJsonArray", "TLCDefer"] {
        let marker = table(&mut ir, name);
        ir.builtins.push(marker.clone());
        assert_eq!(decode(&encode(&ir)).unwrap().builtins.last(), Some(&marker));
    }
}
#[test]
fn row_arity_mismatch_is_valid_data_for_runtime_diagnostics() {
    let mut ir = ir();
    let mut marker = table(&mut ir, "G");
    marker.arity = 2;
    ir.builtins.push(marker.clone());
    assert_eq!(decode(&encode(&ir)).unwrap().builtins.last(), Some(&marker));
}
#[test]
fn invalid_opcode_role_and_flag_profiles_reject() {
    let mut ir = ir();
    let marker = table(&mut ir, "PrintT");
    ir.builtins.push(marker.clone());
    for flags in [
        Builtin::TABLE_PHASE_KNOWN,
        marker.flags | Builtin::STATE_LEVEL,
        marker.flags | Builtin::LAZY,
        marker.flags | Builtin::DECLINED,
        marker.flags | Builtin::EXTERNAL_CLASS,
        marker.flags | Builtin::PACKAGED_TLC_DEFER,
        marker.flags | Builtin::CLOSED_JAVA_CONTEXT,
        marker.flags | (1 << 29),
    ] {
        ir.builtins.last_mut().unwrap().flags = flags;
        assert!(decode(&encode(&ir)).is_err(), "{flags}");
    }
}
#[test]
fn invalid_table_header_and_argument_shapes_reject() {
    let mut ir = ir();
    let marker = table(&mut ir, "G");
    ir.builtins.push(marker.clone());
    for arity in [0, -1] {
        ir.builtins.last_mut().unwrap().arity = arity;
        assert!(decode(&encode(&ir)).is_err());
    }
    *ir.builtins.last_mut().unwrap() = marker.clone();
    ir.builtins.last_mut().unwrap().table.clear();
    assert!(decode(&encode(&ir)).is_err());
    *ir.builtins.last_mut().unwrap() = marker.clone();
    let row = marker.table[0].0.unwrap() as usize;
    for value in [
        Value::Int(1),
        Value::IntervalFunction {
            class: 0,
            low: 1,
            range: vec![Value::Int(1)],
        },
        Value::IntervalFunction {
            class: 2,
            low: 0,
            range: vec![Value::Int(1)],
        },
        Value::IntervalFunction {
            class: 2,
            low: 1,
            range: vec![],
        },
        Value::Function {
            class: 2,
            domain: vec![Value::Int(1)],
            range: vec![Value::Int(1)],
        },
    ] {
        ir.values.list[row] = value;
        assert!(decode(&encode(&ir)).is_err());
    }
}
#[test]
fn existing_defer_strictness_unknown_bits_and_version_rules_stay() {
    let mut ir = ir();
    let name = ir.texts.len() as u32;
    ir.texts.push("TLCDefer".into());
    let marker = Builtin {
        name,
        arity: 1,
        flags: Builtin::PACKAGED_TLC_DEFER | Builtin::STATE_LEVEL | Builtin::LAZY,
        table: vec![],
    };
    ir.builtins.push(marker.clone());
    assert!(decode(&encode(&ir)).is_ok());
    for extra in [
        Builtin::TABLE_PHASE_KNOWN,
        Builtin::TABLE,
        Builtin::CLOSED_JAVA_CONTEXT,
        Builtin::EXTERNAL_CLASS,
        1 << 29,
    ] {
        ir.builtins.last_mut().unwrap().flags = marker.flags | extra;
        assert!(decode(&encode(&ir)).is_err());
    }
    let legacy = Builtin {
        name,
        arity: 1,
        flags: 1 << 29,
        table: vec![],
    };
    *ir.builtins.last_mut().unwrap() = legacy.clone();
    assert_eq!(decode(&encode(&ir)).unwrap().builtins.last(), Some(&legacy));
    let marker = table(&mut ir, "G");
    *ir.builtins.last_mut().unwrap() = marker;
    let original = encode(&ir);
    for version in [0, 15, IR_VERSION + 100] {
        let mut bytes = original.clone();
        bytes[4..8].copy_from_slice(&version.to_le_bytes());
        assert!(decode(&bytes).is_err());
    }
}
