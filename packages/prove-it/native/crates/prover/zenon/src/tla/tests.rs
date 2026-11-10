//! Checks the extension against the TypeScript on the fixtures: from each fixture's hypotheses, a
//! walk that adds each formula to the index, takes it apart where it's a connective, asks for its
//! extension nodes and goes on with their branches. Each step prints the nodes as the TypeScript's
//! twin of the walk printed them.

use std::collections::VecDeque;
use std::fmt::Write;
use std::path::Path;

use super::{PREDEFINED_SYMBOLS, get_built_in_definitions, get_extension_nodes};
use crate::expr::{Expr, Expressions, Kind};
use crate::index_table::Index;
use crate::node::Priority;
use crate::parse::{Definition, Phrase, parse_zenon};
use crate::phrase::separate;

const LIMIT: usize = 300;

fn join(exprs: &[Expr], separator: &str) -> String {
    exprs
        .iter()
        .map(|inner| inner.hash.to_string())
        .collect::<Vec<_>>()
        .join(separator)
}

fn decompose(exprs: &Expressions, formula: &Expr) -> Vec<Expr> {
    match formula.kind {
        Kind::And | Kind::Or => formula.args.clone(),
        Kind::Imply => vec![exprs.enot(&formula.args[0]), formula.args[1].clone()],
        Kind::Not => {
            let operand = &formula.args[0];
            match operand.kind {
                Kind::Not => vec![operand.args[0].clone()],
                Kind::And | Kind::Or => {
                    operand.args.iter().map(|inner| exprs.enot(inner)).collect()
                }
                Kind::Imply => vec![operand.args[0].clone(), exprs.enot(&operand.args[1])],
                _ => vec![],
            }
        }
        _ => vec![],
    }
}

fn trace(text: &str) -> Vec<String> {
    let exprs = Expressions::new();
    let Ok(parsed) = parse_zenon(&exprs, text) else {
        return vec!["parse error".into()];
    };
    let phrases = [get_built_in_definitions(&exprs), parsed].concat();
    let separated = separate(PREDEFINED_SYMBOLS, &phrases);
    let mut index = Index::new();
    for definition in &separated.definitions {
        index.add_definition(definition.clone());
    }
    let mut queue: VecDeque<(Expr, i64)> = separated
        .hypotheses
        .iter()
        .map(|hypothesis| (hypothesis.formula.clone(), hypothesis.goalness))
        .collect();
    let mut lines = Vec::new();
    while let Some((formula, goalness)) = queue.pop_front() {
        if lines.len() == LIMIT {
            break;
        }
        if index.is_member(&formula) {
            continue;
        }
        index.add(&formula, goalness);
        if formula.is_relation() {
            index.add_trans(&formula);
        }
        for part in decompose(&exprs, &formula) {
            queue.push_back((part, goalness));
        }
        let mut line = format!("{} {}:", lines.len() + 1, formula.hash);
        match get_extension_nodes(&index, &exprs, &formula, goalness) {
            Ok(result) => {
                for node in &result.nodes {
                    let rule = &node.rule;
                    let definition = rule
                        .definition
                        .as_ref()
                        .map(|definition| format!("[{}]", definition.symbol()))
                        .unwrap_or_default();
                    let priority = match &node.priority {
                        Priority::Prop => "prop".to_owned(),
                        Priority::Arity => "arity".to_owned(),
                        Priority::ArityEq => "arity_eq".to_owned(),
                        Priority::Instance(instance) => format!("i{}", instance.hash),
                    };
                    let branches = node
                        .branches
                        .iter()
                        .map(|branch| join(branch, ","))
                        .collect::<Vec<_>>()
                        .join(";");
                    let _ = write!(
                        line,
                        " {}{definition}/{}/{}/{}/{priority}/{}/{branches}/{}",
                        rule.name.as_str(),
                        rule.args.len(),
                        node.branches.len(),
                        join(&node.conclusions, ","),
                        node.goalness,
                        join(&rule.args, ","),
                    );
                }
                let _ = write!(line, " stop={}", result.is_stopped);
                for node in &result.nodes {
                    for formula in node.branches.iter().flatten() {
                        queue.push_back((formula.clone(), node.goalness));
                    }
                }
            }
            Err(error) => {
                let _ = write!(line, " error {}", error.0);
            }
        }
        let _ = write!(line, " created={}", exprs.get_created_count());
        lines.push(line);
    }
    lines
}

/// FNV-1a over the lines, each ended by a newline.
fn get_digest(lines: &[String]) -> u64 {
    lines
        .iter()
        .flat_map(|line| line.bytes().chain(std::iter::once(b'\n')))
        .fold(0xcbf29ce484222325, |hash, byte| {
            (hash ^ u64::from(byte)).wrapping_mul(0x100000001b3)
        })
}

#[test]
fn walks_the_fixtures_as_the_typescript_does() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../../tests/fixtures/zenon");
    for (fixture, line_count, digest) in TRACES {
        let text = std::fs::read_to_string(root.join(fixture)).unwrap();
        let lines = trace(&text);
        assert_eq!(
            (lines.len(), get_digest(&lines)),
            (*line_count, *digest),
            "{fixture}"
        );
    }
}

/// Each fixture's walk, from the TypeScript: the number of steps and the digest of their lines.
const TRACES: &[(&str, usize, u64)] = &[
    ("rules/boolcase_all.znn", 16, 0xe45a09e36769c3ed),
    ("rules/boolcase_equal.znn", 300, 0x0a04e2a458269468),
    ("rules/boolcase_equiv.znn", 17, 0x325487b65ddac231),
    ("rules/boolcase_imply.znn", 19, 0xc3d6bdc7aa17db57),
    ("rules/boolcase_not.znn", 16, 0xc626d8c26d029787),
    ("rules/boolcase_or.znn", 19, 0x674db0e9106814fe),
    ("rules/box_p.znn", 3, 0x834dc59d9e528043),
    ("rules/case.znn", 13, 0x1b791c9afc234427),
    ("rules/case_other.znn", 9, 0x3afb65a5d8c08d63),
    ("rules/cup_subseteq.znn", 4, 0x43e57a33daa5f21c),
    ("rules/iffalse.znn", 2, 0x6a6afb91db7b2cce),
    ("rules/iftrue.znn", 2, 0x7df78aa4c9619738),
    ("rules/in_addElt.znn", 9, 0x7ce146c25016b3fd),
    ("rules/in_nat_succ.znn", 3, 0xfa37573414df57ae),
    ("rules/in_upair.znn", 6, 0x99abc9b281af7b19),
    ("rules/neq_record.znn", 10, 0x2b194fcc98c53bbd),
    ("rules/noteq_x_true.znn", 5, 0xe4e222275d766607),
    ("rules/notin_UNION.znn", 4, 0x41250db7eb596cb7),
    ("rules/notin_addElt.znn", 4, 0xd8b76367d753f949),
    ("rules/notin_upair.znn", 3, 0x9cc6db7759a7cead),
    ("rules/notisafcn_extend.znn", 1, 0x4fa8d9bef820483c),
    ("rules/notisafcn_onearg.znn", 1, 0x810a72f6c0d59b5c),
    ("rules/np_eq_r.znn", 11, 0x4d7babfeceab80fe),
    ("rules/p_eq_l.znn", 16, 0x71ca8e546344839f),
    ("rules/p_eq_r.znn", 16, 0x57e73a2c72876a4f),
    ("rules/record_domain.znn", 4, 0x93b48351fd859fa6),
    ("rules/record_eq_match.znn", 4, 0xd455b305e745cbaf),
    ("rules/record_eq_mismatch.znn", 2, 0xc8deab5168e4d620),
    ("rules/record_neq.znn", 10, 0xb6dcc73a219ee24d),
    ("rules/record_notisafcn.znn", 1, 0x1f50f69052c13714),
    ("rules/relation-close_sym.znn", 3, 0xddf34911e816f429),
    ("rules/relation-p_not_p_sym.znn", 4, 0xe4f9db02abe897c1),
    ("rules/relation-refl.znn", 3, 0x6a4fe0ff269b649e),
    ("rules/relation-trans.znn", 5, 0x7f5ef9f6936a295a),
    ("rules/relation-trans_eq.znn", 6, 0xad041c6c80c0411a),
    ("rules/relation-trans_eq2.znn", 5, 0x2a89db0e5751b3e0),
    ("rules/relation-trans_eq_sym.znn", 6, 0x124382ff13a7e5b3),
    ("rules/relation-trans_sym.znn", 5, 0x12f7362754ab1478),
    ("rules/relation-transsym.znn", 5, 0x4dda06c51df47b13),
    ("rules/setemptyequal.znn", 3, 0x66f5f3bfffd7c4e4),
    ("rules/subseteq_cap.znn", 3, 0x33f664777b23ca18),
    ("rules/tuple_eq_mismatch.znn", 2, 0xa947f38d2e30adcb),
    (
        "proved/AtomicBakeryWithoutSMT-116.znn",
        134,
        0x68e7e3764c26c867,
    ),
    (
        "proved/AtomicBakeryWithoutSMT-414.znn",
        207,
        0xf98dedf211f2d798,
    ),
    ("proved/BubbleSort-14.znn", 22, 0xfb022ff9a0505ddf),
    ("proved/ByzPaxos-VoteProof-770.znn", 300, 0x15aadabe504c48df),
    ("proved/EWD687a_proof-55.znn", 36, 0xf5bdcd477bd18380),
    ("proved/EWD998PCal_proof-186.znn", 24, 0xa8e1a8450fa09b0a),
    (
        "proved/EmptySetEqCases_proofs-630.znn",
        7,
        0xd9ea6e278f2eee43,
    ),
    (
        "proved/EmptySetEqCases_proofs-643.znn",
        2,
        0xb4e9be51b6652ac4,
    ),
    (
        "proved/FiniteSetTheorems_proofs-138.znn",
        28,
        0x2c4b090708eda3eb,
    ),
    (
        "proved/FiniteSetTheorems_proofs-467.znn",
        3,
        0x45f00f59961fc7bd,
    ),
    (
        "proved/FiniteSetTheorems_proofs-536.znn",
        19,
        0xe74bea9ff2949c52,
    ),
    (
        "proved/FiniteSetTheorems_proofs-557.znn",
        9,
        0xeeda3a09206fde86,
    ),
    (
        "proved/FiniteSetTheorems_proofs-657.znn",
        13,
        0x6b4c00b446665a23,
    ),
    ("proved/NestedCdot_test-1.znn", 27, 0x88b1cacb4cb36a6e),
    ("proved/SnapShot_test-142.znn", 4, 0xe7af4571abf21ddc),
    ("proved/VoteProof-3.znn", 4, 0x145395246cdcd140),
    ("proved/VoteProof-429.znn", 19, 0x98631cfcb02c442f),
    (
        "proved/WellFoundedInduction_proofs-261.znn",
        3,
        0x9f998b406f1c5345,
    ),
    ("proved/bcastByz-720.znn", 131, 0x1cd37481a3a5074f),
    ("proved/setEuclid_test-105.znn", 13, 0x1cbd29161c7519a5),
    (
        "unknown/DiningPhilosophers_proof-304.znn",
        12,
        0xfe905b48a88a6076,
    ),
    (
        "unknown/DiningPhilosophers_proof-464.znn",
        4,
        0xe424bb5401079821,
    ),
    ("memory/PaxosCommit_proof-253.znn", 47, 0xf921eaed629d9c9a),
];

#[test]
fn builds_the_built_in_definitions() {
    let exprs = Expressions::new();
    let summary: Vec<String> = get_built_in_definitions(&exprs)
        .iter()
        .map(|phrase| match phrase {
            Phrase::Def(definition) => match &**definition {
                Definition::Real {
                    name, params, body, ..
                } => format!("{name}:{}:{}", body.hash, join(params, ",")),
                Definition::Pseudo { .. } => String::new(),
            },
            Phrase::Hyp { .. } => String::new(),
        })
        .collect();
    assert_eq!(
        format!(
            "builtins {} {}",
            exprs.get_created_count(),
            summary.join(" ")
        ),
        "builtins 17 subset_def:958903087:25455452,368984435 bAll_def:537373764:933356622,827327593 \
         bEx_def:59232964:933356622,827327593 bChoose_def:939137746:933356622,827327593 \
         prod_def:591673288:25455452,368984435"
    );
}
