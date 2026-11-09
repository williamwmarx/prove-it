//! Nodes nested to the decoder's limit decode and encode in any build, a debug one included, and
//! nodes nested past it fail as an error rather than overflowing the stack and aborting.

use std::path::Path;

use tla_ir::{Ir, Node, NodeKind, decode, encode};

/// The decoder's limit on nested nodes, counting the level a top-level node is at.
const MAXIMUM_DEPTH: usize = 10_000;

fn small_ir() -> Ir {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../../tests/conformance/ir/tlc/tlatools/org.lamport.tlatools/test-model/suite/test61.ir");
    decode(&std::fs::read(path).expect("the golden file")).expect("a golden file decodes")
}

/// The small golden IR with one more top-level node: a number under `primes` Primes.
fn with_primes(primes: usize) -> Vec<u8> {
    let mut ir = small_ir();
    let arena = &mut ir.nodes.arena;
    arena.push(Node {
        line: 1,
        column: 1,
        range: None,
        kind: NodeKind::Number(0),
    });
    for _ in 0..primes {
        let inner = (arena.len() - 1) as u32;
        arena.push(Node {
            line: 1,
            column: 1,
            range: None,
            kind: NodeKind::Prime(inner),
        });
    }
    ir.nodes.top.push((arena.len() - 1) as u32);
    encode(&ir)
}

#[test]
fn decodes_nodes_nested_to_the_limit() {
    let bytes = with_primes(MAXIMUM_DEPTH - 1);
    let ir = decode(&bytes).expect("nodes nested to the limit decode");
    assert!(encode(&ir) == bytes, "nested nodes encode differently");
}

#[test]
fn refuses_nodes_nested_past_the_limit() {
    let error = decode(&with_primes(MAXIMUM_DEPTH)).expect_err("nodes nested too deep");
    assert!(error.message.contains("nested too deep"), "{error}");
}
