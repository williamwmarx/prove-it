//! SANY's report of a module its lexer or parser rejects. `scripts/front-differential.ts
//! sany-parse-error` holds it to `src/sany/parse-error.ts` on every corpus module and their
//! mutations.

use tla_front::TlcVersion;
use tla_front::sany_parse_error::{get_sany_174_lexical_error, get_sany_parse_error};

fn parse_error(source: &str) -> Option<String> {
    get_sany_parse_error(source, TlcVersion::Master)
}

#[test]
fn accepts_a_module_that_parses() {
    assert_eq!(
        parse_error("---- MODULE M ----\nx == a + b * c\n===="),
        None
    );
    assert_eq!(
        parse_error("---- MODULE M ----\nx == /\\ a\n  /\\ b\n===="),
        None
    );
}

#[test]
fn reports_where_the_parser_fails_and_its_productions() {
    assert_eq!(
        parse_error("---- MODULE M ----\nx == 1 +\n====").as_deref(),
        Some(
            "***Parse Error***\nEncountered \"====\" at line 3, column 1 and token \"+\" \n\nResidual stack trace follows:\nExtendableExpr starting at line 3, column 1.\nExtendableExpr starting at line 2, column 6.\nExpression starting at line 2, column 6.\nDefinition starting at line 2, column 1.\nModule body starting at line 2, column 1.\n"
        )
    );
}

#[test]
fn reports_lexical_errors() {
    assert_eq!(
        parse_error("---- MODULE M ----\nx == \"a\\q\"\n====").as_deref(),
        Some("Lexical error at line 2, column 9.  Encountered: \"q\" (113), after : \"\\\"a\\\\\"")
    );
    let source = "---- MODULE M ----\nx == \"é∀ŝ\"\ny == ŝ\n====";
    assert_eq!(
        parse_error(source).as_deref(),
        Some("Lexical error at line 3, column 6.  Encountered: \"\\u015d\" (349), after : \"\"")
    );
    assert_eq!(
        get_sany_174_lexical_error(source).as_deref(),
        Some(
            "Lexical error at line 2, column 8.  Encountered: \"\\u2200\" (8704), after : \"\\\"\\u00e9\""
        )
    );
}

#[test]
fn reports_except_at_fields_as_parser_errors_without_a_parse_exception() {
    assert_eq!(
        parse_error("---- MODULE M ----\nx == [[a |-> 1] EXCEPT !.@ = 2]\n===="),
        Some("@ used in !.@".to_owned())
    );
    assert_eq!(
        parse_error("---- MODULE M ----\nx == [[a |-> 1] EXCEPT !.@ = 2, !.@ = 3]\n===="),
        Some("@ used in !.@\n@ used in !.@".to_owned())
    );
}

#[test]
fn preserves_parser_error_order_when_java_lookahead_reaches_a_lexical_error() {
    let error =
        parse_error("---- MODULE M ----\nbad == [[a |-> 1] EXCEPT !.@ = \"unclosed\n====\n")
            .expect("a lexical error");
    assert!(error.starts_with("Lexical error"));
    let error = parse_error(
        "---- MODULE M ----\nbad == [[a |-> 1] EXCEPT !.@ = 2]\nLater == 2 (* unclosed\n====\n",
    )
    .expect("parser and lexical errors");
    assert!(error.starts_with("@ used in !.@\nLexical {error: EOF reached"));
}
