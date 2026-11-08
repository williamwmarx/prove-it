//! The golden IR files of tests/conformance/ir, which `scripts/engine-ir.ts` writes from the
//! corpus: each decodes and encodes again byte for byte, and holds what its model asks for.

use std::path::{Path, PathBuf};

use tla_ir::{AtomKind, Ir, NodeKind, Resolution, decode, encode};

fn golden_directory() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../tests/conformance/ir")
}

fn find_goldens(directory: &Path, found: &mut Vec<PathBuf>) {
    for entry in std::fs::read_dir(directory).expect("the golden directory") {
        let path = entry.expect("an entry").path();
        if path.is_dir() {
            find_goldens(&path, found);
        } else if path.extension().is_some_and(|extension| extension == "ir") {
            found.push(path);
        }
    }
}

fn read_golden(model: &str) -> (Vec<u8>, Ir) {
    let bytes = std::fs::read(golden_directory().join(model)).expect("the golden file");
    let ir = decode(&bytes).expect("a golden file decodes");
    (bytes, ir)
}

fn text(ir: &Ir, id: u32) -> &str {
    &ir.texts[id as usize]
}

fn definition_names(ir: &Ir) -> Vec<&str> {
    ir.definitions
        .iter()
        .map(|&id| match &ir.nodes.arena[id as usize].kind {
            NodeKind::Definition(definition) => text(ir, definition.name),
            other => panic!("a definition, not {other:?}"),
        })
        .collect()
}

#[test]
fn every_golden_file_round_trips() {
    let mut goldens = Vec::new();
    find_goldens(&golden_directory(), &mut goldens);
    assert!(goldens.len() >= 30, "{} golden files", goldens.len());
    for path in goldens {
        let bytes = std::fs::read(&path).expect("the golden file");
        let ir = decode(&bytes).unwrap_or_else(|error| panic!("{}: {error}", path.display()));
        assert!(
            encode(&ir) == bytes,
            "{} encodes differently",
            path.display()
        );
    }
}

#[test]
fn reaches_the_definitions_the_model_names() {
    let (_, ir) = read_golden("examples/specifications/transaction_commit/2PCwithBTM.ir");
    let names = definition_names(&ir);
    for name in ["Next", "TypeOK", "Consistency", "RManager"] {
        assert!(names.contains(&name), "{name} among {names:?}");
    }
    let invariants: Vec<&str> = ir
        .model
        .invariants
        .iter()
        .map(|invariant| text(&ir, invariant.root.name))
        .collect();
    assert_eq!(invariants, ["TypeOK", "Consistency"]);
    for invariant in &ir.model.invariants {
        let definition = invariant.root.definition.expect("the invariant is defined");
        assert_eq!(
            definition_names(&ir)[definition as usize],
            text(&ir, invariant.root.name)
        );
    }
}

#[test]
fn resolves_each_variable_by_its_position() {
    let (_, ir) = read_golden("examples/specifications/transaction_commit/2PCwithBTM.ir");
    let variables: Vec<&str> = ir.variables.iter().map(|&id| text(&ir, id)).collect();
    let mut resolved = 0;
    for node in &ir.nodes.arena {
        if let NodeKind::Identifier(name) = &node.kind
            && let Resolution::Variable(index) = name.resolution
        {
            assert_eq!(variables[index as usize], text(&ir, name.text));
            resolved += 1;
        }
    }
    assert!(resolved > 0);
    let mut order = ir.tlc_order.clone();
    order.sort();
    assert_eq!(order, (0..variables.len() as i32).collect::<Vec<_>>());
}

#[test]
fn holds_the_atoms_a_liveness_check_asks_about() {
    let (_, ir) = read_golden("examples/specifications/ewd426/TokenRing.ir");
    assert!(ir.model.is_recording_graph);
    assert!(!ir.model.atoms.is_empty());
    let (_, ir) = read_golden("examples/specifications/ReadersWriters/MC.ir");
    assert!(
        ir.model
            .atoms
            .iter()
            .any(|atom| matches!(atom.kind, AtomKind::Enabled { .. }))
    );
}

#[test]
fn holds_the_symmetry_group_as_model_values() {
    let (_, ir) = read_golden("summerset/tla+/paxos/Paxos_MC.ir");
    let symmetry = ir.model.symmetry.as_ref().expect("a symmetry group");
    assert!(!symmetry.is_empty());
    for &(from, to) in symmetry.iter().flatten() {
        assert!(
            from < ir.ranked_count && to < ir.ranked_count,
            "model values are ranked"
        );
    }
}

#[test]
fn refuses_a_damaged_file() {
    let (bytes, _) = read_golden("examples/specifications/transaction_commit/2PCwithBTM.ir");
    let error = decode(&bytes[..bytes.len() - 4]).expect_err("a truncated file");
    assert!(error.message.contains("don't make"), "{error}");
    let mut version = bytes.clone();
    version[4] = 99;
    assert_eq!(
        decode(&version).expect_err("another version").message,
        format!("IR version 99, not {}", tla_ir::IR_VERSION)
    );
    // Every word of the nodes, changed, makes a file that decodes as something else or not at
    // all, and never panics.
    let words = bytes.len() / 4;
    for word in (words / 2..words).step_by(7) {
        let mut damaged = bytes.clone();
        damaged[word * 4..word * 4 + 4].copy_from_slice(&i32::MAX.to_le_bytes());
        if let Ok(ir) = decode(&damaged) {
            assert!(encode(&ir) == damaged);
        }
    }
}
