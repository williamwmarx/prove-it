//! The lowering to the engine IR on a small spec. `scripts/front-differential.ts ir` holds the
//! Rust IR to the TypeScript one, byte for byte, on every corpus module.

use tla_front::TlcVersion;
use tla_front::config::parse_config;
use tla_front::environment::{EnvironmentOptions, create_environment};
use tla_front::lower::{Lowering, RankedTexts};
use tla_ir::{Ir, Junction, Model, NodeKind, Resolution, Startup};

fn lower(source: &str, name: &str) -> Ir {
    let config = parse_config("", TlcVersion::Master).expect("a configuration");
    let environment = create_environment(&EnvironmentOptions {
        source,
        load_module: &|_| None,
        config: &config,
        is_unconfigured: true,
        version: TlcVersion::Master,
        is_level_checked: false,
    })
    .expect("an environment");
    let mut lowering = Lowering::new(
        &environment,
        RankedTexts {
            texts: &[],
            ranks: Default::default(),
        },
    );
    let invariant = lowering.config_name(name);
    lowering
        .finish(Model {
            init: 0,
            next: 0,
            scope: None,
            actions: Vec::new(),
            is_labelled: false,
            invariants: vec![invariant],
            property_invariants: Vec::new(),
            property_invariant_names: Vec::new(),
            constraints: Vec::new(),
            action_constraints: Vec::new(),
            possible: Vec::new(),
            action_properties: Vec::new(),
            initial_predicates: Vec::new(),
            view: None,
            alias: None,
            postconditions: Vec::new(),
            check_deadlock: true,
            is_warning_enabled: true,
            is_recording_graph: false,
            version: None,
            // TLC's default seed, 0, and java.util.Random seeded with it, which no assumption has drawn
            // from: the model `ir.ts` writes for an environment that evaluated nothing at startup.
            random_seed: 0,
            atoms: Vec::new(),
            live_formula: Vec::new(),
            live_properties: Vec::new(),
            specification: None,
            startup: Startup::default(),
            next_substitution: None,
            instance_actions: Vec::new(),
            instance_names: Vec::new(),
            tlc_spec: None,
        })
        .expect("an IR")
}

#[test]
fn lowers_the_definitions_a_configuration_names() {
    let ir = lower(
        "---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nInc == x' = x + 1\n====",
        "Inc",
    );
    assert_eq!(ir.definitions.len(), 1);
    let NodeKind::Definition(definition) = &ir.nodes.arena[ir.definitions[0] as usize].kind else {
        panic!("a definition");
    };
    assert_eq!(&*ir.texts[definition.name as usize], "Inc");
    let NodeKind::Apply { name, args } = &ir.nodes.arena[definition.body as usize].kind else {
        panic!("x' = x + 1");
    };
    assert!(matches!(name.resolution, Resolution::Builtin(_)));
    let NodeKind::Prime(primed) = &ir.nodes.arena[args[0] as usize].kind else {
        panic!("x'");
    };
    let NodeKind::Identifier(variable) = &ir.nodes.arena[*primed as usize].kind else {
        panic!("x");
    };
    assert_eq!(variable.resolution, Resolution::Variable(0));
}

#[test]
fn records_how_each_junction_is_written() {
    let ir = lower(
        "---- MODULE M ----\nVARIABLE x\nInv ==\n  /\\ x\n  /\\ x \\/ x \\/ x\n====",
        "Inv",
    );
    let NodeKind::Definition(definition) = &ir.nodes.arena[ir.definitions[0] as usize].kind else {
        panic!("a definition");
    };
    let NodeKind::And(operands) = &ir.nodes.arena[definition.body as usize].kind else {
        panic!("the bulleted list");
    };
    assert_eq!(
        ir.nodes.junctions[&definition.body],
        Junction {
            is_bulleted: true,
            prefix_ends: Vec::new(),
        }
    );
    assert_eq!(
        ir.nodes.junctions[&operands[1]],
        Junction {
            is_bulleted: false,
            prefix_ends: vec![(5, 11), (5, 16)],
        }
    );
}
