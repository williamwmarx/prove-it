//! The lexer's positions and errors on the cases where JavaScript's strings set them: tabs, UTF-16
//! code units and synonyms. `scripts/front-differential.ts tokens` holds it to `src/lexer.ts` on
//! every module of the corpora.

use tla_front::lexer::{TokenKind, tokenize};

fn describe(source: &str) -> Vec<String> {
    tokenize(source)
        .expect("tokens")
        .iter()
        .map(|token| {
            format!(
                "{} {} {}:{}-{}{}",
                token.kind.name(),
                token.text,
                token.line,
                token.column,
                token.end_column,
                token
                    .spelling
                    .as_ref()
                    .map_or(String::new(), |spelling| format!(" as {spelling}"))
            )
        })
        .collect()
}

#[test]
fn reads_from_the_module_header() {
    let tokens = describe("text before\n---- MODULE M ----\nx == 1\n====\nafter");
    assert_eq!(
        tokens,
        [
            "Separator ---- 2:1-4",
            "Keyword MODULE 2:6-11",
            "Identifier M 2:13-13",
            "Separator ---- 2:15-18",
            "Identifier x 3:1-1",
            "Operator == 3:3-4",
            "Number 1 3:6-6",
            "ModuleEnd ==== 4:1-4",
            "End  4:5-5",
        ]
    );
}

#[test]
fn counts_tabs_and_utf16_code_units() {
    let tokens = describe("---- MODULE M ----\n\tx ≜ \"😀\" ∧ (+)\n====");
    assert_eq!(
        tokens[4..9],
        [
            "Identifier x 2:9-9",
            "Operator == 2:11-11 as ≜",
            "String 😀 2:13-16",
            "Operator /\\ 2:18-18 as ∧",
            "Operator \\oplus 2:20-22 as (+)",
        ]
    );
}

#[test]
fn reads_steps_numerals_and_backslash_words() {
    let tokens = describe("---- MODULE M ----\n<1>a. <+> \\hFF 1.5 S\\used WF_x 1_\n====");
    assert_eq!(
        tokens[4..14],
        [
            "Step <1>a. 2:1-5",
            "Step <+> 2:7-9",
            "Number \\hFF 2:11-14",
            "Decimal 1.5 2:16-18",
            "Identifier S 2:20-20",
            "Operator \\ 2:21-21",
            "Identifier used 2:22-25",
            "Keyword WF_ 2:27-29",
            "Identifier x 2:30-30",
            "Number 1 2:32-32",
        ]
    );
}

#[test]
fn reports_errors_where_typescript_does() {
    let error = |source: &str| tokenize(source).expect_err("an error");
    assert_eq!(
        error("no header").message,
        "Expected a module header such as ---- MODULE Name ----"
    );
    let unterminated = error("---- MODULE M ----\n  \"abc\n====");
    assert_eq!(
        unterminated.message,
        "Unterminated string at line 2, column 7"
    );
    assert!(!unterminated.failure.expect("a failure").is_end);
    assert_eq!(
        error("---- MODULE M ----\n(* (* *)").message,
        "Unterminated comment at line 2, column 9"
    );
    assert_eq!(
        error("---- MODULE M ----\n x 😀").message,
        "Unexpected character \"\\ud83d\" at line 2, column 4"
    );
    assert_eq!(
        error("---- MODULE M ----\n\u{c}").message,
        "Unexpected character \"\\f\" at line 2, column 1"
    );
    assert_eq!(
        tokenize("---- MODULE M ----")
            .expect("tokens")
            .last()
            .map(|token| token.kind),
        Some(TokenKind::End)
    );
}
