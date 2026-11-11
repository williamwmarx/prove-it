//! The kernel's preprocessing against the TypeScript it ports: `scripts/smt-tactics-tables.ts`
//! runs every script of `tests/fixtures/smt` and seeded random quantified scripts through
//! `quant-tactics.ts` as `solver.ts` runs it, through `propagate-values.ts`, `ctx-simplify.ts` and
//! `qe-lite.ts` one after the other, and through `asserted-formulas.ts` with a pushed scope, and
//! records what each stage returned, the resource limit's step count, the number of ASTs, and
//! digests of the ids and reference counts of every expression. This replays each run on
//! quant_tactics.rs, propagate_values.rs, ctx_simplify.rs, qe_lite.rs, qe_lite_der.rs and
//! asserted_formulas.rs, and compares the lines.

use std::fs;
use std::path::Path;

use prove_decide::Limits;
use prove_smt::core::asserted_formulas::AssertedFormulas;
use prove_smt::core::ast::{AstManager, Expr, OP_NOT, SORT_BOOL};
use prove_smt::core::ctx_simplify::ctx_simplify;
use prove_smt::core::goal::Goal;
use prove_smt::core::propagate_values::propagate_values;
use prove_smt::core::qe_lite::apply_qe_lite;
use prove_smt::core::quant_tactics::apply_ufnia_tactic;
use prove_smt::core::smtlib_parser::parse_smtlib;
use prove_smt::util::error::SmtError;
use prove_smt::util::rlimit::ResourceLimit;

// A text longer than this is recorded as its length and hash.
const MAX_TEXT_LENGTH: usize = 160;
// The step budget of each run: a fixture's, and a random script's.
const FIXTURE_STEP_LIMIT: u64 = 3_000_000;
const RANDOM_STEP_LIMIT: u64 = 300_000;

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

// A run's manager and the lines it records.
struct Run {
    m: AstManager,
    lines: Vec<String>,
    // The stage being run, which the table records when the step budget cancels it.
    pending: &'static str,
}

impl Run {
    fn new(step_limit: u64) -> Run {
        let limits = Limits::new(f64::INFINITY, Some(step_limit), None);
        Run {
            m: AstManager::new(ResourceLimit::new(&limits)),
            lines: Vec::new(),
            pending: "",
        }
    }

    fn record(&mut self, operation: &str, result: &str) {
        let line = format!(
            "{operation} => {result} steps={} asts={}",
            self.m.limit.count(),
            self.m.get_num_asts()
        );
        self.lines.push(line);
    }

    // A list of expressions: their number, a hash of their handles, ids and hashes, and their
    // text.
    fn describe_list(&self, exprs: &[Expr]) -> String {
        let m = &self.m;
        let keys: Vec<String> = exprs
            .iter()
            .map(|expr| {
                let index = *expr as usize;
                format!("{expr}:{}:{}", m.ids[index], m.hashes[index])
            })
            .collect();
        let texts: Vec<String> = exprs.iter().map(|expr| m.to_string(*expr)).collect();
        format!(
            "n={} ids={} | {}",
            exprs.len(),
            get_text_hash(&keys.join(",")),
            get_short_text(&texts.join(" ; "))
        )
    }

    fn describe_goal(&self, goal: &Goal) -> String {
        format!(
            "inconsistent={} {}",
            u8::from(goal.is_inconsistent),
            self.describe_list(&goal.forms.items)
        )
    }

    fn describe_reduced(&mut self, formulas: &mut AssertedFormulas) -> Result<String, SmtError> {
        let reduced = formulas.reduce(&mut self.m)?;
        Ok(format!(
            "inconsistent={} {}",
            u8::from(formulas.is_inconsistent),
            self.describe_list(&reduced)
        ))
    }

    // The ids and reference counts of every expression, as two hashes.
    fn dump_refs(&mut self) {
        let num_nodes = self.m.kinds.len();
        let ids: Vec<String> = (0..num_nodes)
            .map(|handle| self.m.ids[handle].to_string())
            .collect();
        let ref_counts: Vec<String> = (0..num_nodes)
            .map(|handle| self.m.get_ref_count(handle as Expr).to_string())
            .collect();
        let result = format!(
            "{num_nodes} {} {}",
            get_text_hash(&ids.join(",")),
            get_text_hash(&ref_counts.join(","))
        );
        self.record("refs", &result);
    }

    fn stage(
        &mut self,
        name: &'static str,
        run: impl FnOnce(&mut Run) -> Result<String, SmtError>,
    ) -> Result<(), SmtError> {
        self.pending = name;
        let result = run(self)?;
        self.record(name, &result);
        Ok(())
    }

    fn pipeline(&mut self, text: &str) -> Result<(), SmtError> {
        // solver.ts's checkSmt up to search.
        let mut incremental = AssertedFormulas::new(&self.m);
        self.m.limit.inc();
        self.pending = "parse";
        let problem = parse_smtlib(text, &mut self.m, |m, assertion| {
            m.limit.inc();
            incremental.assert_expr(m, assertion)
        })?;
        let result = format!(
            "check-sat={} incremental={} {}",
            u8::from(problem.has_check_sat),
            incremental.get_num_formulas(),
            self.describe_list(&problem.assertions)
        );
        self.record("parse", &result);
        if !problem.has_check_sat {
            return Ok(());
        }
        let mut goal = Goal::new();
        self.stage("ufnia", |run| {
            goal = apply_ufnia_tactic(&mut run.m, &problem.assertions)?;
            Ok(run.describe_goal(&goal))
        })?;
        if goal.is_inconsistent || goal.forms.is_empty() {
            return Ok(());
        }
        let mut asserted = AssertedFormulas::new(&self.m);
        self.stage("assert-goal", |run| {
            for assertion in goal.forms.items.iter().copied() {
                asserted.assert_expr(&mut run.m, assertion)?;
            }
            Ok(asserted.get_num_formulas().to_string())
        })?;
        self.stage("reduce", |run| run.describe_reduced(&mut asserted))
    }

    fn stages(&mut self, text: &str) -> Result<(), SmtError> {
        self.pending = "parse";
        let problem = parse_smtlib(text, &mut self.m, |_, _| Ok(()))?;
        let result = self.describe_list(&problem.assertions);
        self.record("parse", &result);
        let mut goal = Goal::new();
        for assertion in problem.assertions.iter().copied() {
            goal.assert(&mut self.m, assertion)?;
        }
        let result = self.describe_goal(&goal);
        self.record("goal", &result);
        self.stage("propagate-values", |run| {
            propagate_values(&mut run.m, &mut goal)?;
            Ok(run.describe_goal(&goal))
        })?;
        self.stage("ctx-simplify", |run| {
            ctx_simplify(&mut run.m, &mut goal)?;
            Ok(run.describe_goal(&goal))
        })?;
        self.stage("qe-lite", |run| {
            apply_qe_lite(&mut run.m, &mut goal)?;
            Ok(run.describe_goal(&goal))
        })?;
        goal.forms.reset(&mut self.m)?;
        self.record("release-goal", "-");
        Ok(())
    }

    fn asserted(&mut self, text: &str) -> Result<(), SmtError> {
        self.pending = "parse";
        let problem = parse_smtlib(text, &mut self.m, |_, _| Ok(()))?;
        let result = self.describe_list(&problem.assertions);
        self.record("parse", &result);
        let assertions = problem.assertions;
        let mut formulas = AssertedFormulas::new(&self.m);
        self.stage("assert", |run| {
            for assertion in assertions.iter().copied() {
                formulas.assert_expr(&mut run.m, assertion)?;
            }
            Ok(formulas.get_num_formulas().to_string())
        })?;
        self.stage("reduce", |run| run.describe_reduced(&mut formulas))?;
        let (Some(first), Some(last)) = (assertions.first().copied(), assertions.last().copied())
        else {
            return Ok(());
        };
        formulas.push();
        self.stage("push-assert", |run| {
            let negation = run.m.mk_app(OP_NOT, &[first], SORT_BOOL)?;
            run.m.inc_ref(negation);
            formulas.assert_expr(&mut run.m, negation)?;
            run.m.dec_ref(negation)?;
            Ok(formulas.get_num_formulas().to_string())
        })?;
        self.stage("push-reduce", |run| run.describe_reduced(&mut formulas))?;
        self.stage("pop", |run| {
            formulas.pop(&mut run.m)?;
            Ok(format!(
                "{} inconsistent={}",
                formulas.get_num_formulas(),
                u8::from(formulas.is_inconsistent)
            ))
        })?;
        self.stage("reassert", |run| {
            formulas.assert_expr(&mut run.m, last)?;
            Ok(formulas.get_num_formulas().to_string())
        })?;
        self.stage("rereduce", |run| run.describe_reduced(&mut formulas))
    }
}

// The lines of the three runs of a script.
fn run_problem(text: &str, step_limit: u64) -> Vec<String> {
    let mut lines = Vec::new();
    for name in ["pipeline", "stages", "asserted"] {
        let mut run = Run::new(step_limit);
        run.record(&format!("run {name}"), "-");
        let result = match name {
            "pipeline" => run.pipeline(text),
            "stages" => run.stages(text),
            _ => run.asserted(text),
        };
        match result {
            Ok(()) => run.dump_refs(),
            Err(SmtError::Canceled) => {
                let operation = format!("canceled {}", run.pending);
                run.record(&operation, "-");
            }
            Err(error) => panic!("{name}: {error:?}"),
        }
        lines.extend(run.lines);
    }
    lines
}

fn read_fixture(file: &str) -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../../../tests/fixtures/smt")
        .join(file);
    fs::read_to_string(path).unwrap()
}

#[test]
fn preprocesses_as_the_typescript_does() {
    let table = include_str!("tables/tactics.txt");
    let expected: Vec<&str> = table.lines().collect();
    let mut actual: Vec<String> = Vec::new();
    for line in &expected {
        let lines = if let Some(file) = line.strip_prefix("fixture ") {
            run_problem(&read_fixture(file), FIXTURE_STEP_LIMIT)
        } else if let Some(text) = line.strip_prefix("random ") {
            run_problem(text, RANDOM_STEP_LIMIT)
        } else if let Some(rest) = line.strip_prefix("budget ") {
            let (budget, file) = rest.split_once(' ').unwrap();
            run_problem(&read_fixture(file), budget.parse().unwrap())
        } else {
            continue;
        };
        actual.push((*line).into());
        actual.extend(lines);
    }
    for (index, line) in expected.iter().enumerate() {
        assert_eq!(
            actual.get(index).map(String::as_str),
            Some(*line),
            "line {}",
            index + 1
        );
    }
    assert_eq!(actual.len(), expected.len());
}
