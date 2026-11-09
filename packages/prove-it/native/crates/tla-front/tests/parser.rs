//! The parser's results and errors on cases `src/parser.ts` decides in its own way.
//! `scripts/front-differential.ts ast` holds the two to the same AST on every corpus module.

use tla_front::ast::{ExpressionKind, ModuleUnit};
use tla_front::dump;
use tla_front::parser::{extract_module, get_numeral_value, parse_module};

fn error(source: &str) -> String {
    parse_module(source).expect_err("an error").message
}

fn body_json(source: &str) -> String {
    let module = parse_module(source).expect("a module");
    let mut out = String::new();
    dump::expression(&module.definitions[0].body).write(&mut out);
    out
}

#[test]
fn reports_precedence_conflicts_as_sany_does() {
    assert_eq!(
        error("---- MODULE M ----\nx == 1 + 2 * 3 = 4 = 5\n===="),
        "Precedence conflict between = and = at line 2, column 20"
    );
    assert_eq!(
        error(
            r"---- MODULE M ----
x == a \cup b \cap c
===="
        ),
        r"Precedence conflict between \cup and \cap at line 2, column 15"
    );
    assert!(parse_module("---- MODULE M ----\nx == ~a = b\n====").is_ok());
    assert_eq!(
        error("---- MODULE M ----\nx == a * -b\n===="),
        "Precedence conflict between * and - at line 2, column 10"
    );
}

#[test]
fn ends_a_junction_list_at_its_column() {
    let module = parse_module("---- MODULE M ----\nx == /\\ a\n     /\\ b \\/ c\n  y == 1\n====")
        .expect("a module");
    assert_eq!(module.definitions.len(), 2);
    let ExpressionKind::Junction {
        operands,
        is_bulleted,
        ..
    } = &module.definitions[0].body.kind
    else {
        panic!("a junction list");
    };
    assert!(is_bulleted);
    assert_eq!(operands.len(), 2);
}

#[test]
fn chains_an_infix_junction_with_its_prefix_ends() {
    let json = body_json("---- MODULE M ----\nx == a /\\ b /\\ c\n====");
    assert!(json.contains(r#""prefixEnds":[{"column":11,"line":2},{"column":16,"line":2}]"#));
}

#[test]
fn reads_proofs_and_their_step_names() {
    let module = parse_module(
        "---- MODULE M ----\nTHEOREM T == TRUE\n<1>1. TRUE\n  OBVIOUS\n<1> QED BY <1>1\n====",
    )
    .expect("a module");
    assert!(matches!(module.units[0], ModuleUnit::Theorem(_)));
    assert_eq!(&*module.definitions[0].name, "T");
    assert_eq!(
        error("---- MODULE M ----\nx == <1>1\n===="),
        "Step number used outside proof at line 2, column 6"
    );
}

#[test]
fn reads_numerals_as_javascript_does() {
    assert_eq!(get_numeral_value("\\hFF"), 255.0);
    assert_eq!(get_numeral_value("\\B101"), 5.0);
    assert_eq!(get_numeral_value("007"), 7.0);
    assert_eq!(get_numeral_value("9007199254740993"), 9007199254740992.0);
}

#[test]
fn extracts_a_module_from_the_root_file() {
    let source = "---- MODULE A ----\n====\r\n---- MODULE B ----\r\nx == 1\r\n=====\nrest";
    assert_eq!(
        extract_module(source, "B").as_deref(),
        Some("---- MODULE B ----\nx == 1\n=====\n")
    );
    assert_eq!(extract_module(source, "C"), None);
}
