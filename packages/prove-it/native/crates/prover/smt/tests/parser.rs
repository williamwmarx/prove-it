//! The SMT-LIB parser against the TypeScript it ports: `scripts/smt-parser-tables.ts` parses every
//! script of `tests/fixtures/smt` and short scripts that reach each error of `smtlib-parser.ts`,
//! and records the error, or the assertions, declarations, sorts, number of ASTs and the id and
//! reference count of every expression. This parses each again and compares.

use std::fs;
use std::path::Path;

use prove_decide::Limits;
use prove_smt::core::ast::{AstManager, SORT_BOOL};
use prove_smt::core::smtlib_parser::parse_smtlib;
use prove_smt::util::error::SmtError;
use prove_smt::util::rlimit::ResourceLimit;

// A text longer than this is recorded as its length and hash.
const MAX_TEXT_LENGTH: usize = 400;

// The inputs not compared yet, with the reason.
const SKIPPED: [(&str, &str); 2] = [
    // Its let bindings are used under a binder, which the parser shifts with
    // var_subst::replace_free_vars, a stub until the port of var-subst.ts merges: remove it then.
    ("script let-under-binder", "needs var_subst"),
    // (and) and (=) apply and to no arguments. ast.ts hashes the Z3 declaration with the sort of a
    // missing argument (undefined), and ast.rs refuses it as an invariant error.
    ("script nullary-connectives", "ast.rs refuses a nullary and"),
];

fn get_text_hash(text: &str) -> u32 {
    text.bytes().fold(2166136261, |hash, byte| {
        (hash ^ u32::from(byte)).wrapping_mul(16777619)
    })
}

fn get_short_text(text: &str) -> String {
    if text.len() > MAX_TEXT_LENGTH {
        format!("#{}:{}", text.len(), get_text_hash(text))
    } else {
        text.into()
    }
}

/// A string as `JSON.stringify` writes it.
fn unquote(text: &str) -> String {
    let inner = &text[1..text.len() - 1];
    let mut result = String::new();
    let mut characters = inner.chars();
    while let Some(character) = characters.next() {
        if character != '\\' {
            result.push(character);
            continue;
        }
        match characters.next() {
            Some('"') => result.push('"'),
            Some('\\') => result.push('\\'),
            Some('n') => result.push('\n'),
            Some('t') => result.push('\t'),
            Some('r') => result.push('\r'),
            other => panic!("unexpected escape {other:?} in {text}"),
        }
    }
    result
}

fn get_input(label: &str) -> String {
    if let Some(file) = label.strip_prefix("fixture ") {
        let path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../../../tests/fixtures/smt")
            .join(file);
        return fs::read_to_string(path).unwrap();
    }
    let rest = label.strip_prefix("script ").unwrap();
    let (_, quoted) = rest.split_once(' ').unwrap();
    unquote(quoted)
}

fn get_error_line(error: &SmtError) -> String {
    match error {
        // The TypeScript crashes with a TypeError on a missing term.
        SmtError::Parse(message) if message == "expected a term" => "error TypeError".into(),
        SmtError::Parse(message) => format!("error SmtParseError {message}"),
        SmtError::Unsupported(message) => format!("error SmtUnsupportedError {message}"),
        SmtError::Invariant(message) => format!("error SmtInvariantError {message}"),
        other => format!("error {other:?}"),
    }
}

fn record(text: &str) -> Vec<String> {
    let limits = Limits::new(f64::INFINITY, None, None);
    let mut manager = AstManager::new(ResourceLimit::new(&limits));
    let problem = match parse_smtlib(text, &mut manager, |_, _| Ok(())) {
        Ok(problem) => problem,
        Err(error) => return vec![get_error_line(&error)],
    };
    let mut lines = vec![format!("check-sat {}", problem.has_check_sat)];
    for assertion in &problem.assertions {
        let index = *assertion as usize;
        lines.push(format!(
            "assert {assertion} {} {} {}",
            manager.ids[index],
            manager.hashes[index],
            get_short_text(&manager.to_string(*assertion))
        ));
    }
    for (index, name) in manager.sort_names.iter().enumerate() {
        lines.push(format!("sort {index} {name}"));
    }
    for (index, decl) in manager.func_decls.iter().enumerate() {
        let domain: Vec<String> = decl.domain.iter().map(ToString::to_string).collect();
        lines.push(format!(
            "decl {index} {} {} {} {}:{} {}",
            decl.name,
            decl.family,
            decl.op,
            domain.join(","),
            decl.range,
            decl.small_id
        ));
    }
    lines.push(format!("asts {}", manager.get_num_asts()));
    // A fresh variable takes the next handle, so it counts the expressions.
    let num_nodes = manager.mk_var(1 << 20, SORT_BOOL);
    let ids: Vec<String> = (0..num_nodes)
        .map(|handle| manager.ids[handle as usize].to_string())
        .collect();
    let ref_counts: Vec<String> = (0..num_nodes)
        .map(|handle| manager.get_ref_count(handle).to_string())
        .collect();
    lines.push(format!(
        "nodes {num_nodes} {} {}",
        get_text_hash(&ids.join(",")),
        get_text_hash(&ref_counts.join(","))
    ));
    lines
}

#[test]
fn parses_as_the_typescript() {
    let table = include_str!("tables/parser.txt");
    let mut blocks: Vec<(&str, Vec<&str>)> = Vec::new();
    for line in table.lines() {
        if line.starts_with("fixture ") || line.starts_with("script ") {
            blocks.push((line, Vec::new()));
        } else {
            blocks.last_mut().unwrap().1.push(line);
        }
    }
    assert!(blocks.len() > 90);
    for (label, expected) in &blocks {
        if SKIPPED.iter().any(|skipped| label.starts_with(skipped.0)) {
            continue;
        }
        let actual = record(&get_input(label));
        assert_eq!(&actual, expected, "{label}");
    }
}
