//! th_rewriter against the TypeScript it ports: `scripts/smt-th-rewriter-tables.ts` records
//! seeded episodes of random arithmetic, Boolean, ite and quantified terms rewritten by
//! `rewriter.ts`'s Rewriter under its option sets, by its mk_* entry points and by `der.ts`, and
//! the rewrite of every assertion of `tests/fixtures/smt`, with what each returned, the resource
//! limit's step count, the number of ASTs, and digests of the ids and reference counts of every
//! expression. This replays them on rewriter.rs, arith_rewriter.rs, poly_rewriter.rs and der.rs.

use std::fs;
use std::path::Path;

use prove_decide::Limits;
use prove_num::{Int, Rational};
use prove_smt::core::ast::{AstManager, Expr, QuantifierData, SmtSymbol, Sort};
use prove_smt::core::der::Der;
use prove_smt::core::rewriter::{
    KERNEL_REWRITER_OPTIONS, Rewriter, RewriterOptions, TACTIC_REWRITER_OPTIONS,
};
use prove_smt::core::smtlib_parser::parse_smtlib;
use prove_smt::util::error::SmtError;
use prove_smt::util::ordered_map::OrderedMap;
use prove_smt::util::rlimit::ResourceLimit;

// A text longer than this is recorded as its length and hash.
const MAX_TEXT_LENGTH: usize = 200;

// The script's rewriters, by name.
const NAMES: [&str; 5] = ["kernel", "tactic", "pull", "kpull", "elim"];

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

fn describe(m: &AstManager, expr: Expr) -> String {
    let index = expr as usize;
    format!(
        "{expr}:{}:{} | {}",
        m.ids[index],
        m.hashes[index],
        get_short_text(&m.to_string(expr))
    )
}

fn get_options(name: &str) -> RewriterOptions {
    match name {
        "kernel" | "elim" => KERNEL_REWRITER_OPTIONS,
        "tactic" => TACTIC_REWRITER_OPTIONS,
        "pull" => RewriterOptions {
            is_pulling_cheap_ite: true,
            ..TACTIC_REWRITER_OPTIONS
        },
        "kpull" => RewriterOptions {
            is_pulling_cheap_ite: true,
            ..KERNEL_REWRITER_OPTIONS
        },
        other => panic!("unknown rewriter {other}"),
    }
}

// An episode's or a fixture's manager, rewriters and der.
struct State {
    m: AstManager,
    rewriters: Vec<Rewriter>,
    der: Der,
    held: Vec<Expr>,
    assertions: Vec<Expr>,
}

impl State {
    fn new(step_limit: Option<u64>) -> State {
        let limits = Limits::new(f64::INFINITY, step_limit, None);
        let m = AstManager::new(ResourceLimit::new(&limits));
        let mut rewriters: Vec<Rewriter> = NAMES
            .iter()
            .map(|name| Rewriter::new(&m, get_options(name), false))
            .collect();
        rewriters[4].set_eliminating_and(true);
        let der = Der::new(&m);
        State {
            m,
            rewriters,
            der,
            held: Vec::new(),
            assertions: Vec::new(),
        }
    }

    fn release(&mut self) {
        for rewriter in &mut self.rewriters {
            rewriter.release(&mut self.m).unwrap();
        }
        self.der.release(&mut self.m).unwrap();
    }

    // The ids and reference counts of every expression, as two hashes.
    fn dump_refs(&self) -> String {
        let num_nodes = self.m.kinds.len();
        let ids: Vec<String> = (0..num_nodes)
            .map(|handle| self.m.ids[handle].to_string())
            .collect();
        let ref_counts: Vec<String> = (0..num_nodes)
            .map(|handle| self.m.get_ref_count(handle as Expr).to_string())
            .collect();
        format!(
            "{num_nodes} {} {}",
            get_text_hash(&ids.join(",")),
            get_text_hash(&ref_counts.join(","))
        )
    }

    // An operation that returns an expression with a reference, which the caller releases.
    fn run_owned_expr(&mut self, fields: &[&str]) -> Result<Expr, SmtError> {
        let State {
            m,
            rewriters,
            der,
            assertions,
            ..
        } = self;
        let get = |name: &str| NAMES.iter().position(|item| *item == name).unwrap();
        match fields[0] {
            "rw" => rewriters[get(fields[1])].rewrite(m, number(fields[2])),
            "frw" => rewriters[get(fields[1])].rewrite(m, assertions[number::<usize>(fields[2])]),
            "der" => {
                let expr: Expr = number(fields[1]);
                m.with_temporaries(|m| der.apply(m, expr))
            }
            "fder" => {
                let expr = assertions[number::<usize>(fields[1])];
                m.with_temporaries(|m| der.apply(m, expr))
            }
            "mk-app" | "mk-app-core" => {
                let rewriter = &mut rewriters[get(fields[1])];
                let decl: i32 = number(fields[2]);
                let args: Vec<Expr> = list(fields[3]);
                let sort: Sort = number(fields[4]);
                let is_core = fields[0] == "mk-app-core";
                m.with_temporaries(|m| {
                    if is_core {
                        rewriter.mk_app_core(m, decl, &args, sort)
                    } else {
                        rewriter.mk_app(m, decl, &args, sort)
                    }
                })
            }
            "mk-eq" | "mk-not" | "mk-or" | "mk-and" | "mk-add" | "mk-sub" => {
                let rewriter = &mut rewriters[get(fields[1])];
                let args: Vec<Expr> = list(fields[2]);
                let op = fields[0];
                m.with_temporaries(|m| match op {
                    "mk-eq" => rewriter.mk_eq(m, args[0], args[1]),
                    "mk-not" => rewriter.mk_not(m, args[0]),
                    "mk-or" => rewriter.mk_or(m, &args),
                    "mk-and" => rewriter.mk_and(m, &args),
                    "mk-add" => rewriter.mk_add(m, &args),
                    _ => rewriter.mk_sub(m, args[0], args[1]),
                })
            }
            other => panic!("unknown operation {other}"),
        }
    }
}

fn read_fixture(file: &str) -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../../../tests/fixtures/smt")
        .join(file);
    fs::read_to_string(path).unwrap()
}

#[test]
fn th_rewriter_rewrites_as_the_typescript_does() {
    let table = include_str!("tables/th-rewriter.txt");
    let mut state = State::new(None);
    // After a canceled operation, the rest of its episode is skipped.
    let mut is_skipping = false;
    for (line_index, line) in table.lines().enumerate() {
        let (operation, expected) = line.split_once(" => ").unwrap();
        let fields: Vec<&str> = operation.split(' ').collect();
        if is_skipping && fields[0] != "episode" && fields[0] != "fixture" {
            continue;
        }
        is_skipping = false;
        let mut owned = -1;
        let result = match fields[0] {
            "episode" => {
                state = State::new(Some(number(fields[1])));
                "-".into()
            }
            "fixture" => {
                state = State::new(None);
                let problem =
                    parse_smtlib(&read_fixture(fields[1]), &mut state.m, |_, _| Ok(())).unwrap();
                state.assertions = problem.assertions;
                state.assertions.len().to_string()
            }
            "sort" => state.m.mk_sort(fields[1]).to_string(),
            "decl" => state
                .m
                .mk_func_decl(
                    SmtSymbol::Name(fields[1].into()),
                    &list::<Sort>(fields[2]),
                    number(fields[3]),
                    false,
                )
                .to_string(),
            "app" => {
                let expr = state
                    .m
                    .mk_app(number(fields[1]), &list(fields[2]), number(fields[3]))
                    .unwrap();
                describe(&state.m, expr)
            }
            "var" => {
                let expr = state.m.mk_var(number(fields[1]), number(fields[2]));
                describe(&state.m, expr)
            }
            "int" => {
                let expr = state.m.mk_numeral(&number::<Int>(fields[1]));
                describe(&state.m, expr)
            }
            "real" => {
                let value = Rational::of(number(fields[1]), number(fields[2]));
                let expr = state.m.mk_real_numeral(&value);
                describe(&state.m, expr)
            }
            "model-value" => {
                let expr = state.m.mk_model_value(number(fields[1]), number(fields[2]));
                describe(&state.m, expr)
            }
            "pattern" => {
                let expr = state.m.mk_pattern(&list(fields[1])).unwrap();
                describe(&state.m, expr)
            }
            "quant" => {
                let names: Vec<SmtSymbol> = if fields[3] == "-" {
                    Vec::new()
                } else {
                    fields[3].split(',').map(symbol).collect()
                };
                let expr = state
                    .m
                    .mk_quantifier(QuantifierData {
                        is_forall: fields[1] == "1",
                        sorts: list(fields[2]),
                        names,
                        body: number(fields[4]),
                        patterns: list(fields[5]),
                        weight: 0,
                        qid: "q".into(),
                    })
                    .unwrap();
                describe(&state.m, expr)
            }
            "hold" => {
                let expr: Expr = number(fields[1]);
                state.m.inc_ref(expr);
                state.held.push(expr);
                state.m.get_ref_count(expr).to_string()
            }
            "begin" => state.m.begin_temporaries().to_string(),
            "end" => {
                state.m.end_temporaries(number(fields[1])).unwrap();
                "-".into()
            }
            "refs" => state.dump_refs(),
            "set-subst" => {
                let mut substitution = OrderedMap::new();
                if fields[2] != "-" {
                    for pair in fields[2].split(',') {
                        let (key, value) = pair.split_once(':').unwrap();
                        substitution.insert(number::<Expr>(key), number::<Expr>(value));
                    }
                }
                let State { m, rewriters, .. } = &mut state;
                let index = NAMES.iter().position(|item| *item == fields[1]).unwrap();
                rewriters[index].set_substitution(m, substitution).unwrap();
                "-".into()
            }
            "reset" | "cleanup" => {
                let State { m, rewriters, .. } = &mut state;
                let index = NAMES.iter().position(|item| *item == fields[1]).unwrap();
                if fields[0] == "cleanup" {
                    rewriters[index].cleanup(m).unwrap();
                } else {
                    rewriters[index].reset(m).unwrap();
                }
                "-".into()
            }
            "elim-and" => {
                let State { m, rewriters, .. } = &mut state;
                let index = NAMES.iter().position(|item| *item == fields[1]).unwrap();
                rewriters[index].set_eliminating_and(fields[2] == "1");
                rewriters[index].reset(m).unwrap();
                "-".into()
            }
            "release" => {
                let State { m, rewriters, .. } = &mut state;
                let index = NAMES.iter().position(|item| *item == fields[1]).unwrap();
                rewriters[index].release(m).unwrap();
                "-".into()
            }
            "release-der" => {
                state.der.release(&mut state.m).unwrap();
                "-".into()
            }
            "frelease" => {
                state.release();
                "-".into()
            }
            "canceled" => {
                let error = state.run_owned_expr(&fields[1..]).unwrap_err();
                assert!(
                    matches!(error, SmtError::Canceled),
                    "line {}: {error:?}",
                    line_index + 1
                );
                is_skipping = true;
                "-".into()
            }
            _ => {
                owned = state
                    .run_owned_expr(&fields)
                    .unwrap_or_else(|error| panic!("line {}: {error:?}", line_index + 1));
                describe(&state.m, owned)
            }
        };
        let actual = format!(
            "{result} steps={} asts={}",
            state.m.limit.count(),
            state.m.get_num_asts()
        );
        assert_eq!(actual, expected, "line {}: {operation}", line_index + 1);
        if owned != -1 {
            state.m.dec_ref(owned).unwrap();
        }
    }
}
