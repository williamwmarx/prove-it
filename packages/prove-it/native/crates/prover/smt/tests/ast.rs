//! The AST manager against the TypeScript it ports: `scripts/smt-core-tables.ts` records a seeded
//! sequence of operations on `ast.ts`'s AstManager with what each returned, and this replays them:
//! the handles, Z3 ids and hashes of the expressions, the small ids of their declarations, the
//! number of ASTs, and the ids and reference counts of every expression at checkpoints.

use prove_decide::Limits;
use prove_num::{Int, Rational};
use prove_smt::core::ast::{AstManager, Decl, Expr, KIND_APP, QuantifierData, SmtSymbol};
use prove_smt::util::rlimit::ResourceLimit;

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

fn symbol(text: &str) -> Option<SmtSymbol> {
    if text == "-" {
        return None;
    }
    Some(match text.split_at(2) {
        ("n:", rest) => SmtSymbol::Number(number(rest)),
        ("s:", rest) => SmtSymbol::Name(rest.into()),
        _ => panic!("not a symbol: {text}"),
    })
}

fn join<T: ToString>(items: impl Iterator<Item = T>) -> String {
    let items: Vec<String> = items.map(|item| item.to_string()).collect();
    if items.is_empty() {
        "-".into()
    } else {
        items.join(",")
    }
}

fn describe(manager: &AstManager<'_>, expr: Expr) -> String {
    let index = expr as usize;
    let decl_id = if manager.kinds[index] == KIND_APP && manager.ids[index] != -1 {
        manager.get_decl_id(expr).unwrap().to_string()
    } else {
        "-".into()
    };
    let fields = format!(
        "{expr}:{}:{}:{}:{decl_id}",
        manager.ids[index], manager.hashes[index], manager.sorts[index]
    );
    if manager.depths[index] <= 4 {
        format!("{fields} | {}", manager.to_string(expr))
    } else {
        fields
    }
}

fn describe_decl(manager: &AstManager<'_>, decl: Decl) -> String {
    format!(
        "{decl}:{}:{}",
        manager.func_decls[decl as usize].small_id,
        manager.get_decl_hash(decl)
    )
}

fn describe_result(
    manager: &AstManager<'_>,
    result: Result<Expr, prove_smt::util::error::SmtError>,
) -> String {
    match result {
        Ok(expr) => describe(manager, expr),
        Err(_) => "error".into(),
    }
}

#[test]
fn the_manager_builds_and_recycles_as_the_typescript_does() {
    let limits = Limits::new(f64::INFINITY, None, None);
    let mut manager = AstManager::new(ResourceLimit::new(&limits));
    let table = include_str!("tables/ast.txt");
    for line in table.lines() {
        let (operation, _) = line.split_once(" => ").unwrap();
        let fields: Vec<&str> = operation.split(' ').collect();
        let result = match fields[0] {
            "sort" => manager.mk_sort(fields[1]).to_string(),
            "decl" => {
                let decl = manager.mk_func_decl(
                    symbol(fields[1]).unwrap(),
                    &list(fields[2]),
                    number(fields[3]),
                    fields[4] == "1",
                );
                describe_decl(&manager, decl)
            }
            "app" => {
                let result = manager.mk_app(number(fields[1]), &list(fields[2]), number(fields[3]));
                describe_result(&manager, result)
            }
            "int" => {
                let expr = manager.mk_numeral(&number::<Int>(fields[1]));
                describe(&manager, expr)
            }
            "real" => {
                let value = Rational::of(number(fields[1]), number(fields[2]));
                let expr = manager.mk_real_numeral(&value);
                describe(&manager, expr)
            }
            "var" => {
                let expr = manager.mk_var(number(fields[1]), number(fields[2]));
                describe(&manager, expr)
            }
            "fresh-const" => {
                let result = manager.mk_fresh_const(symbol(fields[1]).as_ref(), number(fields[2]));
                describe_result(&manager, result)
            }
            "model-value" => {
                let expr = manager.mk_model_value(number(fields[1]), number(fields[2]));
                describe(&manager, expr)
            }
            "and" => {
                let result = manager.mk_and(&list(fields[1]));
                describe_result(&manager, result)
            }
            "or" => {
                let result = manager.mk_or(&list(fields[1]));
                describe_result(&manager, result)
            }
            "not" => {
                let result = manager.mk_not(number(fields[1]));
                describe_result(&manager, result)
            }
            "eq" => {
                let result = manager.mk_eq(number(fields[1]), number(fields[2]));
                describe_result(&manager, result)
            }
            "pattern" => {
                let result = manager.mk_pattern(&list(fields[1]));
                describe_result(&manager, result)
            }
            "quant" => {
                let result = manager.mk_quantifier(QuantifierData {
                    is_forall: fields[1] == "1",
                    sorts: list(fields[2]),
                    names: fields[3]
                        .split(',')
                        .map(|name| symbol(name).unwrap())
                        .collect(),
                    body: number(fields[4]),
                    patterns: list(fields[5]),
                    weight: number(fields[6]),
                    qid: fields[7].into(),
                });
                describe_result(&manager, result)
            }
            "quant-mismatch" => {
                let mut data = manager.get_quantifier(number(fields[1])).unwrap().clone();
                data.names.clear();
                let result = manager.mk_quantifier(data);
                describe_result(&manager, result)
            }
            "begin" => manager.begin_temporaries().to_string(),
            "end" => {
                manager.end_temporaries(number(fields[1])).unwrap();
                "-".into()
            }
            "inc" => {
                let expr = number(fields[1]);
                manager.inc_ref(expr);
                manager.get_ref_count(expr).to_string()
            }
            "dec" => {
                let expr = number(fields[1]);
                manager.dec_ref(expr).unwrap();
                manager.get_ref_count(expr).to_string()
            }
            "release-later" => {
                let expr = number(fields[1]);
                manager.release_later(expr).unwrap();
                manager.get_ref_count(expr).to_string()
            }
            "inc-decl" => {
                let decl = number(fields[1]);
                manager.inc_decl_ref(decl);
                describe_decl(&manager, decl)
            }
            "dec-decl" => {
                let decl = number(fields[1]);
                manager.dec_decl_ref(decl).unwrap();
                describe_decl(&manager, decl)
            }
            "query" => {
                let (left, right, decl) = (number(fields[1]), number(fields[2]), number(fields[3]));
                [
                    manager.is_complement(left, right).to_string(),
                    manager.are_distinct(left, right).to_string(),
                    manager
                        .get_times_minus_one_arg(left)
                        .map_or("-".into(), |arg| arg.to_string()),
                    manager.is_unique_value(left).to_string(),
                    manager.is_occurring(decl, left).to_string(),
                    manager.contains_model_value(left).to_string(),
                    manager.is_ground_app(left).to_string(),
                    manager.is_ground(left).to_string(),
                    manager
                        .get_numeral(left)
                        .map_or("-".into(), |value| value.to_string()),
                    manager.is_uninterpreted_const(left).to_string(),
                ]
                .join(",")
            }
            "fresh-var-name" => {
                manager.mk_fresh_var_name(Some(fields[1]).filter(|prefix| *prefix != "-"))
            }
            "finite-set" => {
                manager.init_finite_set_plugin();
                "-".into()
            }
            "macro" => {
                manager.mk_macro(fields[1], number(fields[2]));
                describe_decl(&manager, (manager.func_decls.len() - 1) as Decl)
            }
            "ids" => join(manager.ids.iter()),
            "refs" => join((0..manager.ids.len()).map(|expr| manager.get_ref_count(expr as Expr))),
            other => panic!("unknown operation {other}"),
        };
        assert_eq!(
            format!("{operation} => {result} asts={}", manager.get_num_asts()),
            line
        );
    }
}

#[test]
fn with_temporaries_releases_what_it_does_not_keep() {
    let limits = Limits::new(f64::INFINITY, None, None);
    let mut manager = AstManager::new(ResourceLimit::new(&limits));
    let asts = manager.get_num_asts();
    let kept = manager
        .with_temporaries(|manager| {
            let first = manager.mk_fresh_const(None, prove_smt::core::ast::SORT_BOOL)?;
            let second = manager.mk_fresh_const(None, prove_smt::core::ast::SORT_BOOL)?;
            manager.mk_and(&[first, second])
        })
        .unwrap();
    assert_eq!(manager.get_ref_count(kept), 1);
    // The conjunction, its two constants and their declarations stay.
    assert_eq!(manager.get_num_asts(), asts + 5);
    let dropped = manager
        .with_temporaries_keeping(
            |manager| Ok(manager.mk_numeral(&Int::from(1234))),
            |_| Vec::new(),
        )
        .unwrap();
    assert_eq!(manager.ids[dropped as usize], -1);
    assert_eq!(manager.get_num_asts(), asts + 5);
    manager.dec_ref(kept).unwrap();
    assert_eq!(manager.get_num_asts(), asts);
}
