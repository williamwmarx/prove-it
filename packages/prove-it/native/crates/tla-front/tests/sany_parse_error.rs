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
