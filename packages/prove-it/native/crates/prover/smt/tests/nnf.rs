//! The normal forms against the TypeScript they port: `scripts/smt-nnf-tables.ts` records a seeded
//! sequence of operations on random quantified Boolean and arithmetic terms with uninterpreted
//! functions, then applies each transformation to every assertion and quantifier of
//! `tests/fixtures/smt`, with what each returned, the fresh declarations it made, the resource
//! limit's step count and the number of ASTs, and the ids and reference counts of every expression
//! at checkpoints. This replays them: nnf, pull_quant, pattern_inference, maximize_ac_sharing and
//! qe_lite_fm.

use std::collections::HashMap;
use std::fs;
use std::path::Path;

use prove_decide::Limits;
use prove_num::Int;
use prove_smt::core::ast::{
    AstManager, Expr, KIND_APP, KIND_QUANTIFIER, KIND_VAR, OP_AND, OP_NUM, QuantifierData,
    SORT_BOOL, SmtSymbol,
};
use prove_smt::core::maximize_ac_sharing::{MaxBvSharing, MaxBvSharingConfig};
use prove_smt::core::nnf::{DefinedNames, Nnf};
use prove_smt::core::pattern_inference::PatternInference;
use prove_smt::core::pull_quant::{PullQuant, PullQuantConfig, pull_quant};
use prove_smt::core::qe_lite_fm::Fm;
use prove_smt::core::ref_vector::RefVector;
use prove_smt::core::smtlib_parser::parse_smtlib;
use prove_smt::util::rlimit::ResourceLimit;

// A shallow term's text longer than this is left out.
const MAX_TEXT_LENGTH: usize = 200;

fn number<T: std::str::FromStr>(text: &str) -> T
where
    T::Err: std::fmt::Debug,
{
    text.parse().unwrap()
}

fn list<T: std::str::FromStr>(text: &str) -> Vec<T>
where
    T::Err: std::fmt::Debug,
{
    if text == "-" {
        return Vec::new();
    }
    text.split(',').map(number).collect()
}

fn symbol(text: &str) -> SmtSymbol {
    match text.split_at(2) {
        ("n:", rest) => SmtSymbol::Number(number(rest)),
        ("s:", rest) => SmtSymbol::Name(rest.into()),
        _ => panic!("not a symbol: {text}"),
    }
}

fn get_symbol_text(symbol: &SmtSymbol) -> String {
    match symbol {
        SmtSymbol::Number(number) => format!("n:{number}"),
        SmtSymbol::Name(name) => format!("s:{name}"),
    }
}

fn join<T: ToString>(items: impl Iterator<Item = T>) -> String {
    let items: Vec<String> = items.map(|item| item.to_string()).collect();
    if items.is_empty() {
        "-".into()
    } else {
        items.join(",")
    }
}

fn get_text_hash(text: &str) -> u32 {
    text.bytes().fold(2166136261, |hash, byte| {
        (hash ^ u32::from(byte)).wrapping_mul(16777619)
    })
}

fn visit_struct(m: &AstManager, hashes: &mut HashMap<Expr, u32>, expr: Expr) -> u32 {
    if let Some(hash) = hashes.get(&expr) {
        return *hash;
    }
    let index = expr as usize;
    let kind = m.kinds[index];
    let sort = m.sorts[index];
    let text = if kind == KIND_VAR {
        format!("v{}:{sort}", m.values[index])
    } else if kind == KIND_QUANTIFIER {
        let data = m.get_quantifier(expr).unwrap().clone();
        let patterns: Vec<String> = data
            .patterns
            .iter()
            .map(|pattern| visit_struct(m, hashes, *pattern).to_string())
            .collect();
        let body = visit_struct(m, hashes, data.body);
        format!(
            "q{}:{}:{}:{}:{}:{}:{body}",
            u8::from(data.is_forall),
            data.sorts
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(","),
            data.names
                .iter()
                .map(get_symbol_text)
                .collect::<Vec<_>>()
                .join(","),
            data.weight,
            data.qid,
            patterns.join(",")
        )
    } else if m.decls[index] == OP_NUM {
        format!("n{}:{sort}", m.to_string(expr))
    } else {
        let args: Vec<String> = m
            .get_args(expr)
            .iter()
            .map(|arg| visit_struct(m, hashes, *arg).to_string())
            .collect();
        format!("a{}:{sort}({})", m.get_decl_name(expr), args.join(","))
    };
    let hash = get_text_hash(&text);
    hashes.insert(expr, hash);
    hash
}

fn describe(m: &AstManager, expr: Expr) -> String {
    let index = expr as usize;
    let fields = format!(
        "{expr}:{}:{}",
        m.ids[index],
        visit_struct(m, &mut HashMap::new(), expr)
    );
    if m.depths[index] > 5 {
        return fields;
    }
    let text = m.to_string(expr);
    if text.encode_utf16().count() <= MAX_TEXT_LENGTH {
        format!("{fields} | {text}")
    } else {
        fields
    }
}

fn describe_list(m: &AstManager, exprs: &[Expr]) -> String {
    if exprs.is_empty() {
        return "-".into();
    }
    exprs
        .iter()
        .map(|expr| describe(m, *expr))
        .collect::<Vec<_>>()
        .join(" ; ")
}

fn line(m: &AstManager, operation: &str, result: &str) -> String {
    format!(
        "{operation} => {result} steps={} asts={}",
        m.limit.count(),
        m.get_num_asts()
    )
}

// Runs an operation, and the line with the names of the declarations it made.
fn line_fresh(
    m: &mut AstManager,
    operation: &str,
    run: impl FnOnce(&mut AstManager) -> String,
) -> String {
    let start = m.func_decls.len();
    let result = run(m);
    let names = join(
        m.func_decls[start..]
            .iter()
            .map(|decl| decl.name.to_string()),
    );
    line(m, operation, &format!("{result} fresh={names}"))
}

fn line_refs(m: &AstManager) -> String {
    let num_nodes = m.kinds.len();
    let ids = join((0..num_nodes).map(|handle| m.ids[handle]));
    let ref_counts = join((0..num_nodes).map(|handle| m.get_ref_count(handle as Expr)));
    line(
        m,
        "refs",
        &format!(
            "{num_nodes} {} {}",
            get_text_hash(&ids),
            get_text_hash(&ref_counts)
        ),
    )
}

fn line_nnf(
    m: &mut AstManager,
    operation: &str,
    nnf: &mut Nnf,
    names: &mut DefinedNames,
    expr: Expr,
) -> String {
    line_fresh(m, operation, |m| {
        let mut definitions = RefVector::new();
        let result = nnf.apply(m, names, expr, &mut definitions).unwrap();
        let text = format!(
            "{} defs={}",
            describe(m, result),
            describe_list(m, &definitions.items)
        );
        m.dec_ref(result).unwrap();
        definitions.reset(m).unwrap();
        text
    })
}

// pull, pull-rw and sharing: a rewrite whose result comes with a reference.
fn line_rewrite(
    m: &mut AstManager,
    operation: &str,
    rewrite: impl FnOnce(&mut AstManager) -> Expr,
) -> String {
    line_fresh(m, operation, |m| {
        let result = rewrite(m);
        let text = describe(m, result);
        m.dec_ref(result).unwrap();
        text
    })
}

fn line_infer(
    m: &mut AstManager,
    operation: &str,
    inference: &mut PatternInference,
    quantifier: Expr,
    is_pulled: bool,
) -> String {
    m.with_temporaries_keeping(
        |m| {
            let data = m.get_quantifier(quantifier)?.clone();
            Ok(if is_pulled {
                let patterns = inference.infer_pulled(m, data.sorts.len(), data.body)?;
                line(
                    m,
                    operation,
                    &format!("patterns={}", describe_list(m, &patterns)),
                )
            } else {
                let inferred = inference.infer(m, data.sorts.len(), data.body, data.weight)?;
                line(
                    m,
                    operation,
                    &format!(
                        "patterns={} weight={}",
                        describe_list(m, &inferred.patterns),
                        inferred.weight
                    ),
                )
            })
        },
        |_| Vec::new(),
    )
    .unwrap()
}

fn line_fm(
    m: &mut AstManager,
    operation: &str,
    fm: &mut Fm,
    num_vars: i32,
    exprs: &[Expr],
) -> String {
    let mut fmls = RefVector::new();
    for expr in exprs {
        fmls.push(m, *expr);
    }
    fm.num_vars = num_vars;
    fm.apply(m, &mut fmls).unwrap();
    let result = line(m, operation, &describe_list(m, &fmls.items));
    fmls.reset(m).unwrap();
    result
}

// The subterms of terms, under their quantifiers too, each once, in the order of a depth-first
// walk.
fn get_quantifiers(m: &AstManager, exprs: &[Expr]) -> Vec<Expr> {
    let mut quantifiers = Vec::new();
    let mut visited = std::collections::HashSet::new();
    let mut todo: Vec<Expr> = exprs.iter().rev().copied().collect();
    while let Some(current) = todo.pop() {
        if !visited.insert(current) {
            continue;
        }
        if m.kinds[current as usize] == KIND_APP {
            todo.extend(m.get_args(current).into_iter().rev());
        } else if m.kinds[current as usize] == KIND_QUANTIFIER {
            quantifiers.push(current);
            todo.push(m.get_quantifier(current).unwrap().body);
        }
    }
    quantifiers
}

fn new_manager() -> AstManager {
    let limits = Limits::new(f64::INFINITY, None, None);
    AstManager::new(ResourceLimit::new(&limits))
}

fn new_sharing(m: &AstManager) -> MaxBvSharing {
    MaxBvSharing::new(m, MaxBvSharingConfig::new())
}

fn new_pull(m: &AstManager) -> PullQuant {
    PullQuant::new(m, PullQuantConfig::new(m))
}

// Replays the random operations, and returns the line of each.
fn replay_random(expected: &[&str]) -> Vec<String> {
    let mut m = new_manager();
    let mut actual = Vec::new();
    let mut held: Vec<Expr> = Vec::new();
    let mut names = DefinedNames::new();
    let mut nnf = Nnf::new(&m);
    let mut pull = new_pull(&m);
    let mut inference = PatternInference::new();
    let mut sharing = new_sharing(&m);
    let mut fm = Fm::new();
    for expected_line in expected {
        let (operation, _) = expected_line.split_once(" => ").unwrap();
        let fields: Vec<&str> = operation.split(' ').collect();
        let m = &mut m;
        let result = match fields[0] {
            "sort" => {
                let sort = m.mk_sort(fields[1]);
                line(m, operation, &sort.to_string())
            }
            "decl" => {
                let decl = m.mk_func_decl(
                    SmtSymbol::Name(fields[1].into()),
                    &list::<i32>(fields[2]),
                    number(fields[3]),
                    fields[4] == "1",
                );
                line(m, operation, &decl.to_string())
            }
            "app" => {
                let expr = m
                    .mk_app(number(fields[1]), &list(fields[2]), number(fields[3]))
                    .unwrap();
                line(m, operation, &describe(m, expr))
            }
            "var" => {
                let expr = m.mk_var(number(fields[1]), number(fields[2]));
                line(m, operation, &describe(m, expr))
            }
            "int" => {
                let expr = m.mk_numeral(&number::<Int>(fields[1]));
                line(m, operation, &describe(m, expr))
            }
            "pattern" => {
                let expr = m.mk_pattern(&list(fields[1])).unwrap();
                line(m, operation, &describe(m, expr))
            }
            "quant" => {
                let names: Vec<SmtSymbol> = fields[3].split(',').map(symbol).collect();
                let expr = m
                    .mk_quantifier(QuantifierData {
                        is_forall: fields[1] == "1",
                        sorts: list(fields[2]),
                        names,
                        body: number(fields[4]),
                        patterns: list(fields[5]),
                        weight: number(fields[6]),
                        qid: if fields[7] == "-" {
                            String::new()
                        } else {
                            fields[7].into()
                        },
                    })
                    .unwrap();
                line(m, operation, &describe(m, expr))
            }
            "hold" => {
                let expr: Expr = number(fields[1]);
                m.inc_ref(expr);
                held.push(expr);
                line(m, operation, &m.get_ref_count(expr).to_string())
            }
            "begin" => {
                let outer = m.begin_temporaries();
                line(m, operation, &outer.to_string())
            }
            "end" => {
                m.end_temporaries(number(fields[1])).unwrap();
                line(m, operation, "-")
            }
            "refs" => line_refs(m),
            "nnf" => line_nnf(m, operation, &mut nnf, &mut names, number(fields[1])),
            "names-push" => {
                names.push();
                line(m, operation, "-")
            }
            "names-pop" => {
                names.pop(m).unwrap();
                line(m, operation, "-")
            }
            "nnf-renew" => {
                nnf.release(m).unwrap();
                if fields[1] == "1" {
                    names = DefinedNames::new();
                }
                nnf = Nnf::new(m);
                line(m, operation, "-")
            }
            "pull" => {
                let expr = number(fields[1]);
                line_rewrite(m, operation, |m| pull_quant(m, expr).unwrap())
            }
            "pull-rw" => {
                let expr = number(fields[1]);
                line_rewrite(m, operation, |m| pull.rewrite(m, expr).unwrap())
            }
            "pull-renew" => {
                pull.release(m).unwrap();
                pull = new_pull(m);
                line(m, operation, "-")
            }
            "infer" => line_infer(m, operation, &mut inference, number(fields[1]), false),
            "infer-pulled" => line_infer(m, operation, &mut inference, number(fields[1]), true),
            "sharing" => {
                let expr = number(fields[1]);
                line_rewrite(m, operation, |m| sharing.rewrite(m, expr).unwrap())
            }
            "sharing-push" => {
                sharing.cfg.push_scope();
                line(m, operation, "-")
            }
            "sharing-pop" => {
                sharing.cfg.pop_scope(m).unwrap();
                line(m, operation, "-")
            }
            "sharing-renew" => {
                sharing.release(m).unwrap();
                sharing = new_sharing(m);
                line(m, operation, "-")
            }
            "fm" => line_fm(
                m,
                operation,
                &mut fm,
                number(fields[1]),
                &list::<Expr>(fields[2]),
            ),
            "release" => {
                nnf.release(m).unwrap();
                pull.release(m).unwrap();
                sharing.release(m).unwrap();
                fm.release(m).unwrap();
                line(m, operation, "-")
            }
            "dec-held" => {
                for expr in held.drain(..) {
                    m.dec_ref(expr).unwrap();
                }
                line(m, operation, "-")
            }
            other => panic!("unknown operation {other}"),
        };
        assert_eq!(&result, expected_line);
        actual.push(result);
    }
    actual
}

// Applies every transformation to a fixture, as the script does.
fn record_fixture(file: &str) -> Vec<String> {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../../../tests/fixtures/smt")
        .join(file);
    let text = fs::read_to_string(path).unwrap();
    let mut m = new_manager();
    let m = &mut m;
    let assertions = parse_smtlib(&text, m, |_, _| Ok(())).unwrap().assertions;
    for assertion in &assertions {
        m.inc_ref(*assertion);
    }
    let mut lines = vec![line(m, &format!("parsed {}", assertions.len()), "-")];
    let mut names = DefinedNames::new();
    let mut nnf = Nnf::new(m);
    for (index, assertion) in assertions.iter().enumerate() {
        lines.push(line_nnf(
            m,
            &format!("nnf {index}"),
            &mut nnf,
            &mut names,
            *assertion,
        ));
    }
    nnf.release(m).unwrap();
    lines.push(line(m, "nnf-release", "-"));
    for (index, assertion) in assertions.iter().enumerate() {
        lines.push(line_rewrite(m, &format!("pull {index}"), |m| {
            pull_quant(m, *assertion).unwrap()
        }));
    }
    let quantifiers = get_quantifiers(m, &assertions);
    let mut inference = PatternInference::new();
    for (index, quantifier) in quantifiers.iter().enumerate() {
        lines.push(line_infer(
            m,
            &format!("infer {index}"),
            &mut inference,
            *quantifier,
            false,
        ));
        lines.push(line_infer(
            m,
            &format!("infer-pulled {index}"),
            &mut inference,
            *quantifier,
            true,
        ));
    }
    let mut sharing = new_sharing(m);
    sharing.cfg.push_scope();
    for (index, assertion) in assertions.iter().enumerate() {
        lines.push(line_rewrite(m, &format!("sharing {index}"), |m| {
            sharing.rewrite(m, *assertion).unwrap()
        }));
    }
    sharing.cfg.pop_scope(m).unwrap();
    sharing.release(m).unwrap();
    lines.push(line(m, "sharing-release", "-"));
    let mut fm = Fm::new();
    for (index, quantifier) in quantifiers.iter().enumerate() {
        let data = m.get_quantifier(*quantifier).unwrap().clone();
        let fmls = if m.get_op(data.body) == OP_AND {
            m.get_args(data.body)
        } else {
            vec![data.body]
        };
        lines.push(line_fm(
            m,
            &format!("fm {index}"),
            &mut fm,
            data.sorts.len() as i32,
            &fmls,
        ));
    }
    fm.release(m).unwrap();
    lines.push(line(m, "fm-release", "-"));
    lines.push(line_refs(m));
    lines
}

fn replay_table() {
    let table = include_str!("tables/nnf.txt");
    let mut random: Vec<&str> = Vec::new();
    let mut fixtures: Vec<(&str, Vec<&str>)> = Vec::new();
    for table_line in table.lines() {
        if let Some(file) = table_line.strip_prefix("fixture ") {
            fixtures.push((file, Vec::new()));
        } else if let Some(fixture) = fixtures.last_mut() {
            fixture.1.push(table_line);
        } else {
            random.push(table_line);
        }
    }
    assert!(random.len() > 5000);
    assert!(fixtures.len() > 40);
    replay_random(&random);
    for (file, expected) in &fixtures {
        let actual = record_fixture(file);
        for (index, expected_line) in expected.iter().enumerate() {
            assert_eq!(
                actual.get(index).map(String::as_str),
                Some(*expected_line),
                "{file}"
            );
        }
        assert_eq!(actual.len(), expected.len(), "{file}");
    }
}

#[test]
fn normalizes_as_the_typescript() {
    // The fixtures' terms are deep, and the table's printer recurses on them.
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(replay_table)
        .unwrap()
        .join()
        .unwrap();
}

/// A shared DAG whose unfolded size doubles at each level (t₀ = x, tₙ₊₁ = f(tₙ, tₙ)). The
/// candidate sizes are JavaScript numbers in the TypeScript, which never overflow; the patterns
/// are the TypeScript's for depth 20 (`PatternInference.infer`, printed as handle, Z3 id, number
/// of arguments and the distinct arguments).
#[test]
fn infers_patterns_on_a_shared_dag_as_the_typescript_does() {
    let limits = Limits::new(f64::INFINITY, None, None);
    let mut m = AstManager::new(ResourceLimit::new(&limits));
    let u = m.mk_sort("U");
    let f = m.mk_func_decl(SmtSymbol::Name("f".into()), &[u, u], u, false);
    let p = m.mk_func_decl(SmtSymbol::Name("p".into()), &[u], SORT_BOOL, false);
    let q = m.mk_func_decl(SmtSymbol::Name("q".into()), &[u], SORT_BOOL, false);
    let x = m.mk_var(0, u);
    let mut chain = vec![x];
    for index in 0..20 {
        let next = m.mk_app(f, &[chain[index], chain[index]], u).unwrap();
        chain.push(next);
    }
    let mut inference = PatternInference::new();
    let eq = m.mk_eq(chain[20], x).unwrap();
    let p_term = m.mk_app(p, &[chain[20]], SORT_BOOL).unwrap();
    let q_term = m.mk_app(q, &[chain[19]], SORT_BOOL).unwrap();
    let or = m.mk_or(&[p_term, q_term]).unwrap();
    let describe = |m: &AstManager, pattern: Expr| {
        let mut args: Vec<Expr> = Vec::new();
        for index in 0..m.get_num_args(pattern) {
            let arg = m.get_arg(pattern, index);
            if !args.contains(&arg) {
                args.push(arg);
            }
        }
        let args: Vec<String> = args.iter().map(ToString::to_string).collect();
        format!(
            "{},{},{},{}",
            pattern,
            m.ids[pattern as usize],
            m.get_num_args(pattern),
            args.join("+")
        )
    };
    for (body, expected) in [
        (eq, "0 27,47,524288,3"),
        (or, "0 27,47,524288,3 | 28,48,262144,3"),
    ] {
        let inferred = inference.infer(&mut m, 1, body, 0).unwrap();
        let patterns: Vec<String> = inferred
            .patterns
            .iter()
            .map(|pattern| describe(&m, *pattern))
            .collect();
        assert_eq!(
            format!("{} {}", inferred.weight, patterns.join(" | ")),
            expected
        );
    }
}
