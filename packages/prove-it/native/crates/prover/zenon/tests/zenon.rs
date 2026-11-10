//! `tests/unit/zenon.test.ts`, on the same fixtures: the search, the proofs it prints and its input,
//! against tlapm's Zenon. The checker's tests are in `src/check.rs`.

use std::collections::HashMap;
use std::sync::Arc;

use prove_decide::{Limits, Statistic};
use prove_zenon::decide::{ZenonDecision, decide_zenon, run_zenon};

const FIXTURES: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../../../tests/fixtures/zenon"
);

fn read_fixture(path: &str) -> String {
    std::fs::read_to_string(format!("{FIXTURES}/{path}")).expect("a fixture")
}

/// tlapm gives Zenon 10 s. The fixtures take a fraction of that, so a slow machine doesn't change
/// their verdicts.
const TIME_LIMIT_MS: f64 = 60_000.0;

fn limits() -> Limits {
    Limits::new(TIME_LIMIT_MS, None, None)
}

struct Fixture {
    path: String,
    nodes_searched: u64,
    proof_nodes: u64,
    text: String,
}

/// Real .znn files that tlapm wrote, and in rules/ small true goals that need the rule in their
/// name, which no corpus proof uses. Each comes with what tlapm's Zenon reports for it under -stats,
/// one fixture per line of statistics.json.
fn fixtures() -> Vec<Fixture> {
    let statistics = read_fixture("statistics.json");
    let get_number = |line: &str, field: &str| {
        let start = line.find(field).expect("the field") + field.len() + 3;
        line[start..]
            .chars()
            .take_while(char::is_ascii_digit)
            .collect::<String>()
            .parse()
            .expect("a count")
    };
    statistics
        .lines()
        .filter(|line| line.contains("nodesSearched"))
        .map(|line| {
            let path = line.split('"').nth(1).expect("a path").to_owned();
            Fixture {
                text: read_fixture(&path),
                nodes_searched: get_number(line, "nodesSearched"),
                proof_nodes: get_number(line, "proofNodes"),
                path,
            }
        })
        .collect()
}

fn is_unknown(fixture: &Fixture) -> bool {
    fixture.path.starts_with("unknown/")
}

fn read_isar(fixture: &Fixture) -> String {
    read_fixture(&fixture.path.replace(".znn", ".isar"))
}

/// Zenon shares alpha-equivalent formulas through a weak hash table, so a formula takes the names
/// of an older equal formula until OCaml's garbage collector frees that one. On these fixtures the
/// binary's names depend on when it collected garbage, so only the names differ.
const COLLECTOR_NAMED: [&str; 3] = [
    "proved/AtomicBakeryWithoutSMT-116.znn",
    "proved/AtomicBakeryWithoutSMT-414.znn",
    "proved/FiniteSetTheorems_proofs-138.znn",
];

fn is_word(char: char) -> bool {
    char.is_ascii_alphanumeric() || char == '_'
}

/// The tokens of an Isar proof, as the TypeScript test's
/// `/z_[Hh][a-z]+(?=_z_[Hh]|[^\w']|$)|_(?=z_[Hh])|[A-Za-z_][\w']*|\s+|./gs` splits it.
fn tokenize(text: &str) -> Vec<&str> {
    let starts_label = |rest: &str| rest.starts_with("z_H") || rest.starts_with("z_h");
    let mut tokens = Vec::new();
    let mut rest = text;
    while let Some(first) = rest.chars().next() {
        let label_end = starts_label(rest).then(|| {
            3 + rest[3..]
                .chars()
                .take_while(char::is_ascii_lowercase)
                .count()
        });
        let length = match label_end {
            Some(end)
                if end > 3
                    && (rest[end..].starts_with("_z_H")
                        || rest[end..].starts_with("_z_h")
                        || rest[end..]
                            .chars()
                            .next()
                            .is_none_or(|next| !is_word(next) && next != '\'')) =>
            {
                end
            }
            _ if first == '_' && starts_label(&rest[1..]) => 1,
            _ if first.is_ascii_alphabetic() || first == '_' => rest
                .char_indices()
                .find(|(_, next)| !is_word(*next) && *next != '\'')
                .map_or(rest.len(), |(index, _)| index),
            _ if first.is_whitespace() => rest
                .char_indices()
                .find(|(_, next)| !next.is_whitespace())
                .map_or(rest.len(), |(index, _)| index),
            _ => first.len_utf8(),
        };
        tokens.push(&rest[..length]);
        rest = &rest[length..];
    }
    tokens
}

fn get_label(token: &str) -> Option<(char, &str)> {
    let rest = token.strip_prefix("z_")?;
    let kind = rest
        .chars()
        .next()
        .filter(|kind| *kind == 'H' || *kind == 'h')?;
    let letters = &rest[1..];
    (!letters.is_empty() && letters.chars().all(|char| char.is_ascii_lowercase()))
        .then_some((kind, letters))
}

fn is_name(token: &str) -> bool {
    token
        .chars()
        .next()
        .is_some_and(|first| first.is_ascii_alphabetic() || first == '_')
        && token.chars().all(|char| is_word(char) || char == '\'')
}

/// A renaming and its inverse.
type Bijection = (HashMap<String, String>, HashMap<String, String>);

const BINDERS: [&str; 5] = ["\\<lambda>", "\\\\A ", "\\\\E ", "CHOOSE ", "!!"];

struct Scope<'a> {
    left: &'a str,
    right: &'a str,
    depth: i64,
}

/// Whether two Isar proofs agree up to alpha-equivalence and a renaming of names. A bound variable
/// pairs with the one at the same binder in the other proof, until the parenthesis around the
/// binder or the quote that ends its pattern. Fresh zenon_V variables outside any binder, and the
/// z_H and ?z_h labels that number formulas, pair through one bijection each, in order of first
/// appearance. Every other token matches byte for byte.
fn is_equal_up_to_renaming(left: &str, right: &str) -> bool {
    let left_tokens = tokenize(left);
    let right_tokens = tokenize(right);
    if left_tokens.len() != right_tokens.len() {
        return false;
    }
    let mut bijections: HashMap<&str, Bijection> = HashMap::new();
    let mut is_paired = |kind: &'static str, from: &str, to: &str| {
        let maps = bijections.entry(kind).or_default();
        if !maps.0.contains_key(from) && !maps.1.contains_key(to) {
            maps.0.insert(from.to_owned(), to.to_owned());
            maps.1.insert(to.to_owned(), from.to_owned());
        }
        maps.0.get(from).is_some_and(|paired| paired == to)
            && maps.1.get(to).is_some_and(|paired| paired == from)
    };
    let is_binder = |tokens: &[&str], position: usize| {
        let preceding = tokens[position.saturating_sub(4)..position].concat();
        BINDERS.iter().any(|binder| preceding.ends_with(binder))
    };
    let mut scopes: Vec<Scope> = Vec::new();
    let mut depth = 0;
    for (position, (left_token, right_token)) in left_tokens.iter().zip(&right_tokens).enumerate() {
        let is_match = match (get_label(left_token), get_label(right_token)) {
            (Some(left_label), Some(right_label)) => {
                left_label.0 == right_label.0 && is_paired("label", left_label.1, right_label.1)
            }
            _ if !is_name(left_token) || !is_name(right_token) => left_token == right_token,
            _ if is_binder(&left_tokens, position) && is_binder(&right_tokens, position) => {
                scopes.push(Scope {
                    left: left_token,
                    right: right_token,
                    depth,
                });
                true
            }
            _ => {
                let left_scope = scopes.iter().rposition(|scope| scope.left == *left_token);
                let right_scope = scopes.iter().rposition(|scope| scope.right == *right_token);
                if left_scope.is_some() || right_scope.is_some() {
                    left_scope == right_scope
                } else if left_token.starts_with("zenon_V") && right_token.starts_with("zenon_V") {
                    is_paired("fresh", left_token, right_token)
                } else {
                    left_token == right_token
                }
            }
        };
        depth += match *left_token {
            "(" => 1,
            ")" => -1,
            _ => 0,
        };
        while scopes.last().is_some_and(|scope| {
            scope.depth > depth || (*left_token == "\"" && scope.depth == depth)
        }) {
            scopes.pop();
        }
        if !is_match {
            return false;
        }
    }
    true
}

fn get_proof(decision: ZenonDecision) -> Option<String> {
    match decision {
        ZenonDecision::Unsat(proof) => Some(proof),
        ZenonDecision::Unknown => None,
    }
}

#[test]
fn searches_each_fixture_the_same_way() {
    for fixture in fixtures() {
        let run = run_zenon(&fixture.text, &limits()).expect("a valid input");
        assert_eq!(
            (run.nodes_searched, run.proof_nodes),
            (fixture.nodes_searched, fixture.proof_nodes),
            "{}",
            fixture.path
        );
        let proof = get_proof(decide_zenon(&fixture.text, &limits()).expect("a valid input"));
        assert_eq!(proof.is_none(), is_unknown(&fixture), "{}", fixture.path);
        if is_unknown(&fixture) {
            assert_eq!(run.failure, Some("exhausted"), "{}", fixture.path);
        }
    }
}

#[test]
fn prints_the_proof_that_tlapm_writes() {
    for fixture in fixtures() {
        if is_unknown(&fixture) || COLLECTOR_NAMED.contains(&fixture.path.as_str()) {
            continue;
        }
        let proof = get_proof(decide_zenon(&fixture.text, &limits()).expect("a valid input"));
        assert_eq!(proof, Some(read_isar(&fixture)), "{}", fixture.path);
    }
}

#[test]
fn prints_the_proof_that_tlapm_writes_up_to_the_names_of_variables() {
    for fixture in fixtures() {
        if !COLLECTOR_NAMED.contains(&fixture.path.as_str()) {
            continue;
        }
        let isar = read_isar(&fixture);
        let proof = get_proof(decide_zenon(&fixture.text, &limits()).expect("a valid input"))
            .unwrap_or_default();
        assert_ne!(proof, isar, "{}", fixture.path);
        assert!(is_equal_up_to_renaming(&proof, &isar), "{}", fixture.path);
    }
}

#[test]
fn tells_proofs_apart_beyond_the_names_of_variables() {
    let fixture = fixtures()
        .into_iter()
        .find(|fixture| !is_unknown(fixture))
        .expect("a proved fixture");
    let isar = read_isar(&fixture);
    assert!(is_equal_up_to_renaming(&isar, &isar));
    assert!(!is_equal_up_to_renaming(
        &isar,
        &isar.replacen("z_Ha", "z_Hb", 1)
    ));
    assert!(!is_equal_up_to_renaming(
        &isar,
        &isar.replacen("FALSE", "TRUE", 1)
    ));
}

#[test]
fn runs_out_of_memory_where_tlapms_zenon_does() {
    // Zenon gives up on this file once its heap passes 1 GB, after 12559 nodes.
    let text = read_fixture("memory/PaxosCommit_proof-253.znn");
    let run = run_zenon(&text, &limits()).expect("a valid input");
    assert_eq!(run.failure, Some("memory limit"));
}

#[test]
fn stops_at_the_deadline_where_tlapm_kills_zenon() {
    let text = read_fixture("memory/PaxosCommit_proof-253.znn");
    let run = run_zenon(&text, &Limits::new(200.0, None, None)).expect("a valid input");
    assert_eq!(run.failure, Some("time limit"));
}

/// Each goal is false, next to a true one, so no sound search proves it.
const FALSE_GOALS: [(&str, &str); 18] = [
    (
        "a disjunction implies its first disjunct",
        "$goal (=> (\\/ p q) p)",
    ),
    (
        "an existential gives a universal",
        "$hyp \"h\" (E. ((x) (P x)))\n$goal (A. ((x) (P x)))",
    ),
    (
        "equality relates any two terms",
        "$hyp \"h\" (= a b)\n$goal (= a c)",
    ),
    (
        "a member of a union is in its first set",
        "$hyp \"h\" (TLA.in a (TLA.cup b c))\n$goal (TLA.in a b)",
    ),
    (
        "a bounded universal holds outside its bound",
        "$hyp \"h\" (TLA.bAll s ((x) (P x)))\n$goal (P a)",
    ),
    (
        "a function applies outside its domain",
        "$goal (= (TLA.fapply (TLA.Fcn s ((x) x)) a) a)",
    ),
    (
        "tuples with different components are equal",
        "$goal (= (TLA.tuple a b) (TLA.tuple a c))",
    ),
    ("distinct strings are equal", "$goal (= \"a\" \"b\")"),
    ("IF p THEN a ELSE b is a", "$goal (= (TLA.cond p a b) a)"),
    (
        "CHOOSE satisfies an unsatisfiable predicate",
        "$goal (P (TLA.bChoice s ((x) (P x))))",
    ),
    (
        "a member of {b, c} is b",
        "$hyp \"h\" (TLA.in a (TLA.set b c))\n$goal (= a b)",
    ),
    (
        "a member of b is in b \\ c",
        "$hyp \"h\" (TLA.in a b)\n$goal (TLA.in a (TLA.setminus b c))",
    ),
    (
        "EXCEPT changes every argument",
        "$goal (= (TLA.fapply (TLA.except f a b) c) b)",
    ),
    ("every set is a subset", "$goal (TLA.in a (TLA.SUBSET b))"),
    (
        "subset is symmetric",
        "$hyp \"h\" (TLA.subseteq a b)\n$goal (TLA.subseteq b a)",
    ),
    (
        "records with different fields are equal",
        "$goal (= (TLA.record \"a\" x) (TLA.record \"a\" y))",
    ),
    (
        "a relation is symmetric",
        "$hyp \"h\" (R a b)\n$goal (R b a)",
    ),
    (
        "a symmetric relation is transitive",
        "$hyp \"sym\" (A. ((x) (A. ((y) (=> (R x y) (R y x))))))\n$hyp \"h1\" (R a b)\n$hyp \"h2\" (R b c)\n$goal (R a c)",
    ),
];

#[test]
fn finds_no_proof_of_a_false_goal() {
    for (name, text) in FALSE_GOALS {
        let decision = decide_zenon(text, &Limits::new(1000.0, None, None));
        assert!(
            matches!(decision, Ok(ZenonDecision::Unknown)),
            "{name}: {decision:?}"
        );
    }
}

#[test]
fn rejects_the_proof_that_zenons_not_subseteq_cap_rule_gives() {
    // tlapm's Zenon proves this. Its rule for ~(a \subseteq b \cap c) opens two branches, both
    // ~(a \subseteq c), where Zenon.thy's lemma has ~(a \subseteq b) and ~(a \subseteq c).
    let text = "$hyp \"h\" (TLA.subseteq a c)\n$goal (TLA.subseteq a (TLA.cap b c))";
    let run = run_zenon(text, &limits()).expect("a valid input");
    assert!(run.proof.is_some());
    assert!(run.isar.is_none());
    assert!(matches!(
        decide_zenon(text, &limits()),
        Ok(ZenonDecision::Unknown)
    ));
}

#[test]
fn rejects_malformed_input() {
    for text in ["$goal (= a b", "$sig a", "$goal (= \"\\q\" a)"] {
        assert!(decide_zenon(text, &limits()).is_err(), "{text}");
    }
}

#[test]
fn gives_up_once_the_cancel_cell_is_set() {
    let limits = Limits::new(TIME_LIMIT_MS, None, Some(Arc::new(|| true)));
    let run = run_zenon("$goal (= a a)", &limits).expect("a valid input");
    assert_eq!(run.failure, Some("aborted"));
}

/// What `bun scripts/zenon-fixtures.ts` recorded from the TypeScript in
/// tests/fixtures/zenon/decisions.txt: per fixture and step limit, the statistics `decideZenon`
/// reports, which show the port made the same search and printed the same proof.
#[test]
fn decides_as_the_typescript_does_under_a_step_limit() {
    let root = concat!(env!("CARGO_MANIFEST_DIR"), "/../../../../tests/fixtures");
    for line in read_fixture("decisions.txt").lines() {
        let mut fields = line.splitn(3, ' ');
        let (Some(path), Some(step_limit)) = (fields.next(), fields.next()) else {
            panic!("a malformed line: {line}");
        };
        let text = std::fs::read_to_string(format!("{root}/{path}")).expect("a fixture");
        let step_limit = step_limit.parse().expect("a step limit");
        let limits = Limits::new(f64::INFINITY, Some(step_limit), None);
        let decision = prove_zenon::decide(&text, &limits).expect("a decision");
        let statistics = decision.statistics.iter().map(|(name, value)| match value {
            Statistic::Count(count) => format!("{name}={count}"),
            Statistic::Text(text) => format!("{name}=\"{text}\""),
        });
        let decided = std::iter::once(format!("{path} {step_limit}"))
            .chain(statistics)
            .collect::<Vec<_>>()
            .join(" ");
        assert_eq!(decided, line);
    }
}
