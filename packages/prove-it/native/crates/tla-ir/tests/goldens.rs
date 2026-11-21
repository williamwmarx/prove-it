//! The golden IR files of tests/conformance/ir, frozen fixtures the deleted TypeScript lowering
//! wrote from the corpus: each decodes and encodes again byte for byte, and holds what its model asks for.

use std::path::{Path, PathBuf};

use tla_ir::{AtomKind, Ir, Junction, NodeKind, Resolution, decode, encode};

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
fn holds_the_symmetry_definition_and_the_sets_it_permutes() {
    // Paxos_MC's SYMMETRY SymmetricPerms permutes the constants Acceptors and Values, which TLC
    // checks.
    let (_, ir) = read_golden("summerset/tla+/paxos/Paxos_MC.ir");
    let symmetry = ir.model.startup.symmetry.as_ref().expect("a symmetry");
    assert!((symmetry.definition as usize) < ir.definitions.len());
    let sets: Vec<(&str, bool)> = symmetry
        .permuted_sets
        .iter()
        .map(|set| (&*ir.texts[set.name as usize], set.operand.is_some()))
        .collect();
    assert_eq!(sets, [("Acceptors", true), ("Values", true)]);
}

#[test]
fn names_a_property_tlc_checks_as_an_invariant() {
    // ACP_NB_WRONG_TLC's PROPERTY AC1 asserts [] of a state predicate, which TLC reports as
    // "Invariant AC1 is violated."
    let (_, ir) = read_golden("examples/specifications/acp/ACP_NB_WRONG_TLC.ir");
    let names: Vec<&str> = ir
        .model
        .property_invariant_names
        .iter()
        .map(|&name| text(&ir, name))
        .collect();
    assert_eq!(names, ["AC1"]);
    assert_eq!(ir.model.property_invariants.len(), 1);
}

// TLC prints where an expression is written as `line 41, col 11 to line 41, col 50 of module
// TCommit`, so each node carries its range.
#[test]
fn holds_where_each_expression_is_written() {
    let (_, ir) = read_golden("examples/specifications/transaction_commit/TCommit.ir");
    let next = ir
        .definitions
        .iter()
        .find_map(|&id| match &ir.nodes.arena[id as usize].kind {
            NodeKind::Definition(definition) if text(&ir, definition.name) == "TCNext" => {
                Some(definition.body)
            }
            _ => None,
        })
        .expect("TCNext");
    let range = ir.nodes.arena[next as usize].range.expect("a range");
    assert_eq!(text(&ir, range.module), "TCommit");
    assert_eq!(
        (
            range.start_line,
            range.start_column,
            range.end_line,
            range.end_column
        ),
        (41, 11, 41, 50)
    );
}

#[test]
fn holds_how_each_junction_is_written() {
    let (_, ir) = read_golden("examples/specifications/transaction_commit/TCommit.ir");
    let body = |name: &str| {
        ir.definitions
            .iter()
            .find_map(|&id| match &ir.nodes.arena[id as usize].kind {
                NodeKind::Definition(definition) if text(&ir, definition.name) == name => {
                    Some(definition.body)
                }
                _ => None,
            })
            .expect("a definition")
    };
    // A node met again is a reference to the first, which holds the junction.
    let junction = |id: u32| {
        let id = match ir.nodes.arena[id as usize].kind {
            NodeKind::Reference(target) => target,
            _ => id,
        };
        ir.nodes.junctions.get(&id).cloned().unwrap_or_default()
    };
    // Decide is a bulleted disjunction of bulleted conjunctions.
    let NodeKind::Or(disjuncts) = &ir.nodes.arena[body("Decide") as usize].kind else {
        panic!("Decide as a disjunction");
    };
    assert_eq!(
        junction(body("Decide")),
        Junction {
            is_bulleted: true,
            prefix_ends: Vec::new()
        }
    );
    assert!(junction(disjuncts[0]).is_bulleted);
    // TCNext's body, Prepare(rm) \/ Decide(rm), is an infix junction, whose one prefix ends where
    // it does.
    let NodeKind::Exists { body: inner, .. } = &ir.nodes.arena[body("TCNext") as usize].kind else {
        panic!("TCNext as \\E");
    };
    assert_eq!(
        junction(*inner),
        Junction {
            is_bulleted: false,
            prefix_ends: vec![(41, 50)]
        }
    );
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

#[test]
fn unavailable_literal_marker_retains_its_decline_boundary() {
    use tla_ir::Builtin;
    let (_, mut ir) = read_golden("examples/specifications/transaction_commit/TCommit.ir");
    let name = ir.texts.len() as u32;
    ir.texts.push("$UninitializedLiteral".into());
    let marker = Builtin {
        name,
        arity: 0,
        flags: Builtin::UNINITIALIZED_LITERAL | Builtin::DECLINED,
        table: Vec::new(),
    };
    ir.builtins.push(marker.clone());
    assert_eq!(decode(&encode(&ir)).unwrap().builtins.last(), Some(&marker));
    for malformed in [
        Builtin {
            arity: 1,
            ..marker.clone()
        },
        Builtin {
            name: 0,
            ..marker.clone()
        },
        Builtin {
            flags: Builtin::UNINITIALIZED_LITERAL,
            ..marker.clone()
        },
        Builtin {
            flags: marker.flags | Builtin::TABLE,
            ..marker.clone()
        },
    ] {
        *ir.builtins.last_mut().unwrap() = malformed;
        assert!(decode(&encode(&ir)).is_err());
    }
}

#[test]
fn packaged_defer_provenance_round_trips_only_on_its_builtin() {
    use tla_ir::Builtin;
    let (_, mut ir) = read_golden("examples/specifications/transaction_commit/TCommit.ir");
    let name = ir.texts.len() as u32;
    ir.texts.push("TLCDefer".into());
    let marker = Builtin {
        name,
        arity: 1,
        flags: Builtin::STATE_LEVEL | Builtin::LAZY | Builtin::PACKAGED_TLC_DEFER,
        table: Vec::new(),
    };
    ir.builtins.push(marker.clone());
    assert_eq!(decode(&encode(&ir)).unwrap().builtins.last(), Some(&marker));
    for malformed in [
        Builtin {
            arity: 0,
            ..marker.clone()
        },
        Builtin {
            name: 0,
            ..marker.clone()
        },
        Builtin {
            flags: marker.flags | Builtin::TABLE,
            ..marker.clone()
        },
        Builtin {
            flags: marker.flags | Builtin::DECLINED,
            ..marker.clone()
        },
        Builtin {
            flags: marker.flags | Builtin::EXTERNAL_CLASS,
            ..marker.clone()
        },
        Builtin {
            flags: Builtin::PACKAGED_TLC_DEFER,
            ..marker.clone()
        },
        Builtin {
            flags: marker.flags | 8192,
            ..marker.clone()
        },
    ] {
        *ir.builtins.last_mut().unwrap() = malformed;
        assert!(decode(&encode(&ir)).is_err());
    }
}

#[test]
fn startup_warning_flag_round_trips_without_accepting_unknown_definition_flags() {
    let (_, mut ir) = read_golden("examples/specifications/transaction_commit/TCommit.ir");
    let node = ir.definitions[0] as usize;
    let NodeKind::Definition(definition) = &mut ir.nodes.arena[node].kind else {
        panic!("a definition");
    };
    let original_flags = definition.flags;
    assert_eq!(tla_ir::Definition::STARTUP_WARNING_ONLY, 256);
    definition.flags |= tla_ir::Definition::STARTUP_WARNING_ONLY;
    let encoded = encode(&ir);
    assert_eq!(u32::from_le_bytes(encoded[4..8].try_into().unwrap()), 16);
    assert_eq!(decode(&encoded).unwrap(), ir);
    let NodeKind::Definition(definition) = &mut ir.nodes.arena[node].kind else {
        unreachable!();
    };
    assert_eq!(tla_ir::Definition::CONFIGURED_SUBSTITUTE, 2048);
    definition.flags = original_flags | tla_ir::Definition::CONFIGURED_SUBSTITUTE;
    assert_eq!(decode(&encode(&ir)).unwrap(), ir);
    assert_eq!(tla_ir::Definition::NAMED_AT_STARTUP, 4096);
    let NodeKind::Definition(definition) = &mut ir.nodes.arena[node].kind else {
        unreachable!();
    };
    definition.flags = original_flags | tla_ir::Definition::NAMED_AT_STARTUP;
    assert_eq!(decode(&encode(&ir)).unwrap(), ir);
    let NodeKind::Definition(definition) = &mut ir.nodes.arena[node].kind else {
        unreachable!();
    };
    assert_eq!(tla_ir::Definition::NESTED_SUBSTITUTION, 1024);
    definition.flags =
        original_flags | tla_ir::Definition::SUBSTITUTED | tla_ir::Definition::NESTED_SUBSTITUTION;
    assert_eq!(decode(&encode(&ir)).unwrap(), ir);
    for invalid in [
        128,
        512,
        8192,
        16384,
        128 | 256,
        128 | 2048,
        128 | 1024,
        128 | 4096,
    ] {
        let NodeKind::Definition(definition) = &mut ir.nodes.arena[node].kind else {
            unreachable!();
        };
        definition.flags = original_flags | invalid;
        assert!(
            decode(&encode(&ir)).is_err(),
            "IR16 definition flags {invalid}"
        );
    }
}

#[test]
fn closed_java_membership_marker_accepts_only_core_membership() {
    use tla_ir::Builtin;
    let (_, mut ir) = read_golden("examples/specifications/transaction_commit/TCommit.ir");
    for operator in ["\\in", "\\notin"] {
        let name = ir.texts.len() as u32;
        ir.texts.push(operator.into());
        let marker = Builtin {
            name,
            arity: 2,
            flags: Builtin::CLOSED_JAVA_CONTEXT,
            table: Vec::new(),
        };
        ir.builtins.push(marker.clone());
        assert_eq!(decode(&encode(&ir)).unwrap().builtins.last(), Some(&marker));
        for malformed in [
            Builtin {
                arity: 1,
                ..marker.clone()
            },
            Builtin {
                name: 0,
                ..marker.clone()
            },
            Builtin {
                flags: marker.flags | Builtin::TABLE,
                ..marker.clone()
            },
            Builtin {
                flags: marker.flags | Builtin::EXTERNAL_CLASS,
                ..marker.clone()
            },
            Builtin {
                flags: marker.flags | Builtin::PACKAGED_TLC_DEFER,
                ..marker.clone()
            },
            Builtin {
                flags: marker.flags | Builtin::TABLE_PHASE_KNOWN,
                ..marker.clone()
            },
            Builtin {
                flags: marker.flags | (1 << 20),
                ..marker.clone()
            },
        ] {
            *ir.builtins.last_mut().unwrap() = malformed;
            assert!(decode(&encode(&ir)).is_err());
        }
        ir.builtins.pop();
    }
}

#[test]
fn writes_the_startup_dependents_only_in_their_version() {
    let (bytes, mut ir) = read_golden("examples/specifications/transaction_commit/2PCwithBTM.ir");
    assert!(ir.model.startup.dependents.is_empty());
    assert_eq!(encode(&ir), bytes);
    ir.model.startup.dependents.push((0, 0));
    let encoded = encode(&ir);
    assert_eq!(
        u32::from_le_bytes(encoded[4..8].try_into().unwrap()),
        tla_ir::IR_VERSION
    );
    assert_eq!(decode(&encoded).unwrap(), ir);
}
