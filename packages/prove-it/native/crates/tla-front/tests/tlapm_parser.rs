//! The parser in tlapm's mode, on the cases `src/parser.ts` decides only in that mode, with the
//! results `parseTlapmModule` gives. `scripts/front-differential.ts tlapm-ast` holds the two to
//! the same AST and failures on every corpus module.

use tla_front::dump;
use tla_front::parser::{parse_module, parse_tlapm_module};

fn module(body: &str) -> String {
    format!("---- MODULE M ----\n{body}\n====\n")
}

/// The first definition's body, or else the whole module, as JSON, or the error and its failure.
fn tlapm(source: &str) -> String {
    let mut out = String::new();
    match parse_tlapm_module(source, None) {
        Ok(module) => match module.definitions.first() {
            Some(definition) => dump::expression(&definition.body).write(&mut out),
            None => dump::module(&module).write(&mut out),
        },
        Err(error) => dump::syntax_error(&error).write(&mut out),
    }
    out
}

#[test]
fn reads_true_and_the_other_constants_only_as_keywords() {
    assert_eq!(
        tlapm(&module("TRUE == 1")),
        r#"{"error":"Unexpected keyword TRUE at line 2, column 1","failure":{"column":19,"isEnd":false,"line":1,"reason":"Unexpected keyword TRUE"}}"#
    );
    assert_eq!(
        tlapm(&module("x == r.TRUE")),
        r#"{"error":"Expected an identifier but found \".\" at line 2, column 7","failure":{"column":7,"isEnd":false,"line":2,"reason":"Unexpected ."}}"#
    );
    assert!(parse_module(&module("TRUE == 1")).is_ok());
}

#[test]
fn locates_a_string_at_its_closing_quote() {
    assert_eq!(
        tlapm(&module(r#"x == "ab""#)),
        r#"{"kind":"String","location":{"column":9,"line":2,"range":{"end":{"column":9,"line":2},"module":"M","start":{"column":9,"line":2}}},"value":"ab"}"#
    );
}

#[test]
fn keeps_at_as_a_token() {
    assert_eq!(
        tlapm(&module("x == @(1)")),
        r#"{"error":"Expected an identifier but found \"(\" at line 2, column 7","failure":{"column":7,"isEnd":false,"line":2,"reason":"Unexpected ("}}"#
    );
}

#[test]
fn reads_a_prefix_operator_argument_and_a_based_numeral_as_incomplete() {
    assert_eq!(
        tlapm(&module("x == F(SUBSET)")),
        r#"{"error":"incomplete expression at line 2, column 8","failure":{"column":8,"isEnd":false,"line":2,"reason":"incomplete expression"}}"#
    );
    assert_eq!(
        tlapm(&module(r"x == \B101")),
        r#"{"error":"incomplete expression at line 2, column 6","failure":{"column":6,"isEnd":false,"line":2,"reason":"incomplete expression"}}"#
    );
}

#[test]
fn fails_at_the_end_of_the_token_before_an_unexpected_one() {
    assert_eq!(
        tlapm(&module("x == 1 +")),
        r#"{"error":"Unexpected \"====\" at line 3, column 1","failure":{"column":9,"isEnd":false,"line":2,"reason":"Unexpected ===="}}"#
    );
    assert_eq!(
        tlapm(&module("x == +")),
        r#"{"error":"Unexpected \"+\" at line 2, column 6","failure":{"column":5,"isEnd":false,"line":2,"reason":"Unexpected operator +"}}"#
    );
    assert_eq!(
        tlapm(&module("x == [a]")),
        r#"{"error":"Expected \"]_\" but found \"]\" at line 2, column 8","failure":{"column":8,"isEnd":false,"line":2,"reason":"Unexpected ]"}}"#
    );
}

#[test]
fn fails_after_the_definition_sign_at_the_end_of_input() {
    assert_eq!(
        tlapm("---- MODULE M ----\nx == 1 +"),
        r#"{"error":"Unexpected end of expression at line 2, column 9","failure":{"column":5,"isEnd":true,"line":2,"reason":"Unexpected EOF"}}"#
    );
    assert_eq!(
        tlapm("---- MODULE M ----\nx == 1\ny == f(1,"),
        r#"{"error":"Unexpected end of expression at line 3, column 10","failure":{"column":5,"isEnd":true,"line":3,"reason":"Unexpected EOF"}}"#
    );
}

#[test]
fn reads_lambda_as_an_expression() {
    assert_eq!(
        tlapm(&module("x == LAMBDA a, b : a")),
        r#"{"body":{"kind":"Identifier","location":{"column":20,"line":2,"range":{"end":{"column":20,"line":2},"module":"M","start":{"column":20,"line":2}}},"name":"a"},"kind":"Lambda","location":{"column":6,"line":2,"range":{"end":{"column":20,"line":2},"module":"M","start":{"column":6,"line":2}}},"params":["a","b"]}"#
    );
}

#[test]
fn rejects_recursive_inside_let() {
    assert_eq!(
        tlapm(&module("x == LET RECURSIVE f(_) f(n) == n IN f(1)")),
        r#"{"error":"Unexpected keyword RECURSIVE at line 2, column 5","failure":{"column":5,"isEnd":false,"line":2,"reason":"Unexpected keyword RECURSIVE"}}"#
    );
}

#[test]
fn reads_definables_after_def() {
    assert!(tlapm(&module("THEOREM TRUE BY DEF +, M!x")).contains(
        r#""defs":[{"kind":"OperatorReference","location":{"column":21,"line":2,"range":{"end":{"column":21,"line":2},"module":"M","start":{"column":21,"line":2}}},"operator":"+"},{"kind":"Identifier","location":{"column":24,"line":2,"range":{"end":{"column":26,"line":2},"module":"M","start":{"column":24,"line":2}}},"name":"M!x"}],"facts":[],"isOnly":false"#
    ));
    assert_eq!(
        tlapm(&module("THEOREM TRUE BY DEF 1")),
        r#"{"error":"Expected a definition name but found \"1\" at line 2, column 21","failure":{"column":20,"isEnd":false,"line":2,"reason":"Unexpected 1"}}"#
    );
}

#[test]
fn runs_sanys_parser_on_a_module_named_by_an_underscore() {
    let error = parse_tlapm_module(&module("INSTANCE _\nx == 1"), None).expect_err("an error");
    assert!(error.failure.is_none());
    assert_eq!(
        error.message,
        "***Parse Error***\nWas expecting \"LOCAL, INSTANCE, PROOF, ASSUMPTION, THEOREM, RECURSIVE, declaration, or definition\"\nEncountered \"INSTANCE _\" at line 2, column 1 and token \"----\" \n\nResidual stack trace follows:\nModule body starting at line 2, column 1.\nModule definition starting at line 1, column 1.\n"
    );
}

// tlapm's usebody takes facts, or DEF with its names where there are none; and its expressions
// name a step by its level, so `<*>` is unexpected where SANY reads a step reference.
#[test]
fn rejects_a_bare_by_and_a_star_step_reference() {
    assert_eq!(
        tlapm("---- MODULE M ----\nTHEOREM TRUE\nBY\n====\n"),
        r#"{"error":"Expected a fact or DEF after BY at line 4, column 1","failure":{"column":3,"isEnd":false,"line":3,"reason":"Unexpected ===="}}"#
    );
    assert_eq!(
        tlapm("---- MODULE M ----\nTHEOREM TRUE\nPROOF\n  <1>a TRUE\n  <1>b QED BY <*>a\n====\n"),
        r#"{"error":"<*> step number used in an expression at line 5, column 15","failure":{"column":14,"isEnd":false,"line":5,"reason":"Unexpected <*>"}}"#
    );
    assert!(parse_module("---- MODULE M ----\nTHEOREM TRUE\nBY\n====\n").is_ok());
    assert!(
        parse_module(
            "---- MODULE M ----\nTHEOREM TRUE\nPROOF\n  <1>a TRUE\n  <1>b QED BY <*>a\n====\n"
        )
        .is_ok()
    );
}

// tlapm's lexer reads WF_vars as the tokens WF_ and vars of one match, both located at the whole
// word, so the subscript's locus starts at the WF_ (its Auto-expanding note says so); a subscript
// after a space, or in parentheses, has its own.
#[test]
fn locates_a_joined_fairness_subscript_at_the_operator() {
    let subscript_range = |text: &str| {
        let subscript = text.split("\"subscript\":").nth(1).expect("a subscript");
        let range = subscript.split("\"range\":").nth(1).expect("a range");
        range[..range.find("}}").expect("the range's end") + 2].to_owned()
    };
    assert_eq!(
        subscript_range(&tlapm(&module("F == WF_vars(Next)"))),
        r#"{"end":{"column":12,"line":2},"module":"M","start":{"column":6,"line":2}}"#
    );
    assert_eq!(
        subscript_range(&tlapm(&module("F == WF_ vars(Next)"))),
        r#"{"end":{"column":13,"line":2},"module":"M","start":{"column":10,"line":2}}"#
    );
    let sany = parse_module(&module("F == WF_vars(Next)")).expect("parses");
    let mut out = String::new();
    dump::expression(&sany.definitions.first().expect("a definition").body).write(&mut out);
    assert_eq!(
        subscript_range(&out),
        r#"{"end":{"column":12,"line":2},"module":"M","start":{"column":9,"line":2}}"#
    );
}
