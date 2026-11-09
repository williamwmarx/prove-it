//! The lowering to the engine IR on a small spec. `scripts/front-differential.ts ir` holds the
//! Rust IR to the TypeScript one, byte for byte, on every corpus module.

use tla_front::TlcVersion;
use tla_front::config::parse_config;
use tla_front::environment::{EnvironmentOptions, create_environment};
use tla_front::lower::{Lowering, RankedTexts};
use tla_ir::{Model, NodeKind, Resolution};

#[test]
fn lowers_the_definitions_a_configuration_names() {
    let config = parse_config("", TlcVersion::Master).expect("a configuration");
    let environment = create_environment(&EnvironmentOptions {
        source: "---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nInc == x' = x + 1\n====",
        load_module: &|_| None,
        config: &config,
        is_unconfigured: true,
        version: TlcVersion::Master,
    })
    .expect("an environment");
    let mut lowering = Lowering::new(
        &environment,
        RankedTexts {
            texts: &[],
            ranks: Default::default(),
        },
    );
    let invariant = lowering.config_name("Inc");
    let ir = lowering
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
            symmetry: None,
            check_deadlock: true,
            is_warning_enabled: true,
            is_recording_graph: false,
            version: None,
            atoms: Vec::new(),
            live_formula: Vec::new(),
            live_properties: Vec::new(),
        })
        .expect("an IR");
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
