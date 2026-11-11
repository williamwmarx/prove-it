//! Ported from Z3 (src/smt/theory_lra.cpp, src/smt/arith_eq_adapter.cpp, src/math/lp/lp_api.h),
//! MIT license, see z3-license.txt, through `theory-lra.ts`. Linear integer and real arithmetic,
//! as the theory_lra solver that Z3's default configuration uses for UFNIA. Terms become columns of
//! the lp solver, integer or not by their sort, atoms become bounds on them, propagation makes the
//! tableau feasible and propagates implied bounds and equalities, and the final check runs the
//! integer solver and assumes equalities between shared terms with equal values. Nonlinear
//! products and divisions go to nla (src/math/lp/nla_core.cpp), which refines the model with
//! lemmas, and runs nlsat on what they leave open. This module adds the scopes to the parts that
//! theory_lra_state.rs starts (design/smt-core.md, "The context": the theory's state is
//! `TheoryLra`, held by the context as `theory`, and its methods are `impl Context` methods).

pub use crate::core::theory_lra_state::TheoryLra;

use crate::core::context::Context;
use crate::core::theory_lra_state::Scope;
use crate::util::error::SmtError;

impl Context {
    pub fn theory_push_scope_eh(&mut self) -> Result<(), SmtError> {
        let Some(theory) = self.theory.as_mut() else {
            return Ok(());
        };
        theory.scopes.push(Scope {
            bounds_limit: theory.bounds_trail.len(),
            asserted_qhead: theory.asserted_qhead,
            asserted_atoms_limit: theory.asserted_atoms.len(),
            num_vars: theory.get_num_vars(),
        });
        theory.solver.push();
        self.lra_with_nla(|nla| nla.push());
        Ok(())
    }

    pub fn theory_pop_scope_eh(&mut self, num_scopes: u32) -> Result<(), SmtError> {
        let Some(theory) = self.theory.as_mut() else {
            return Ok(());
        };
        if num_scopes == 0 {
            return Ok(());
        }
        let old_size = theory.scopes.len() - num_scopes as usize;
        let scope = theory.scopes[old_size];
        for index in (scope.bounds_limit..theory.bounds_trail.len()).rev() {
            theory.bounds[theory.bounds_trail[index]].pop();
        }
        theory.bounds_trail.truncate(scope.bounds_limit);
        theory.asserted_atoms.truncate(scope.asserted_atoms_limit);
        theory.asserted_qhead = scope.asserted_qhead;
        theory.scopes.truncate(old_size);
        theory.solver.pop(num_scopes as usize);
        let num_constraints = theory.solver.constraints.constraints.len();
        if theory.constraint_sources.len() > num_constraints {
            theory.constraint_sources.truncate(num_constraints);
        }
        theory.new_bounds = Vec::new();
        self.lra_with_nla(|nla| nla.pop(num_scopes as usize));
        self.lra_mut().var_enodes.truncate(scope.num_vars);
        Ok(())
    }

    pub fn theory_restart_eh(&mut self) -> Result<(), SmtError> {
        let Some(theory) = self.theory.as_mut() else {
            return Ok(());
        };
        let pairs = std::mem::take(&mut theory.restart_pairs);
        for pair in pairs {
            if self.is_inconsistent() {
                break;
            }
            self.lra_mk_eq_axioms(pair.0, pair.1)?;
        }
        Ok(())
    }

    pub fn theory_init_search_eh(&mut self) -> Result<(), SmtError> {
        let Some(theory) = self.theory.as_mut() else {
            return Ok(());
        };
        theory.num_conflicts = 0;
        theory.restart_pairs = Vec::new();
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    //! The arithmetic problems and the fixtures of `scripts/smt-lra-reference.ts`, against the
    //! table it printed (`tests/tables/lra.txt`): the TypeScript kernel with its arithmetic theory
    //! on each problem (whose text the table gives), handed to the kernel as solver.ts hands it a
    //! goal, and solver.ts's checkSmt on each script of `tests/fixtures/smt`, run here the same
    //! way: the result, the conflicts, the steps, the instances and the number of ASTs, the model
    //! of a satisfiable problem, and why a run stopped early.

    use std::fs;
    use std::path::Path;

    use prove_decide::Limits;

    use crate::core::asserted_formulas::AssertedFormulas;
    use crate::core::ast::AstManager;
    use crate::core::context::{Context, SmtParams};
    use crate::core::proto_model::tests::print_model;
    use crate::core::quant_tactics::apply_ufnia_tactic;
    use crate::core::smtlib_parser::parse_smtlib;
    use crate::util::error::SmtError;
    use crate::util::lbool::LBool;
    use crate::util::rlimit::ResourceLimit;

    const TABLE: &str = include_str!("../../tests/tables/lra.txt");
    const PROBLEM_STEP_LIMIT: u64 = 1_000_000;
    const FIXTURE_STEP_LIMIT: u64 = 2_000_000;
    const PARAMS: SmtParams = SmtParams {
        is_mbqi: true,
        relevancy_level: 2,
    };

    /// The sections of the table, by name, in order.
    fn get_sections() -> Vec<(String, Vec<String>)> {
        let mut sections: Vec<(String, Vec<String>)> = Vec::new();
        for line in TABLE.lines() {
            if let Some(name) = line
                .strip_prefix("== ")
                .and_then(|rest| rest.strip_suffix(" =="))
            {
                sections.push((name.to_string(), Vec::new()));
            } else if let Some(section) = sections.last_mut() {
                section.1.push(line.to_string());
            }
        }
        sections
    }

    fn mk_manager(step_limit: u64) -> AstManager {
        AstManager::new(ResourceLimit::new(&Limits::new(
            f64::INFINITY,
            Some(step_limit),
            None,
        )))
    }

    fn get_stop(error: &SmtError) -> &'static str {
        match error {
            SmtError::Canceled => "canceled",
            SmtError::Unsupported(_) => "unsupported",
            _ => panic!("the run failed: {error:?}"),
        }
    }

    /// The kernel on the assertions as they are parsed, as solver.ts hands it a goal.
    fn run_problem(text: &str) -> Vec<String> {
        let mut out = Vec::new();
        let mut m = mk_manager(PROBLEM_STEP_LIMIT);
        let problem = parse_smtlib(text, &mut m, |_, _| Ok(())).unwrap();
        let mut asserted = AssertedFormulas::new(&m);
        let mut context = Context::new(m, PARAMS).unwrap();
        let mut run = |context: &mut Context, out: &mut Vec<String>| -> Result<(), SmtError> {
            for assertion in &problem.assertions {
                asserted.assert_expr(&mut context.m, *assertion)?;
            }
            context.setup_context()?;
            context.internalize_assertions(&mut asserted)?;
            let result = context.search()?;
            out.push(format!(
                "result={} conflicts={} steps={} instances={} asts={}",
                result.to_i8(),
                context.get_num_conflicts(),
                context.m.limit.count(),
                context.qmanager.get_num_instances(),
                context.m.get_num_asts()
            ));
            if result != LBool::True {
                return Ok(());
            }
            let model = context.get_model()?;
            print_model(out, &context.m, &model.borrow(), &[]);
            out.push(format!(
                "modeled: steps={} asts={}",
                context.m.limit.count(),
                context.m.get_num_asts()
            ));
            Ok(())
        };
        if let Err(error) = run(&mut context, &mut out) {
            out.push(format!(
                "stop={} conflicts={} steps={}",
                get_stop(&error),
                context.get_num_conflicts(),
                context.m.limit.count()
            ));
        }
        out
    }

    /// The part of checkSmt before the kernel, which keeps the manager.
    enum Prepared {
        Done(String),
        Kernel(Vec<crate::core::ast::Expr>),
    }

    fn prepare_fixture(m: &mut AstManager, text: &str) -> Result<Prepared, SmtError> {
        let mut incremental = AssertedFormulas::new(m);
        m.limit.inc();
        let problem = parse_smtlib(text, m, |m, assertion| {
            m.limit.inc();
            incremental.assert_expr(m, assertion)
        })?;
        if !problem.has_check_sat {
            return Ok(Prepared::Done(format!(
                "result=none steps={}",
                m.limit.count()
            )));
        }
        let goal = apply_ufnia_tactic(m, &problem.assertions)?;
        if goal.is_inconsistent || goal.forms.is_empty() {
            return Ok(Prepared::Done(format!(
                "goal={} steps={}",
                if goal.is_inconsistent { "unsat" } else { "sat" },
                m.limit.count()
            )));
        }
        Ok(Prepared::Kernel(goal.forms.items.clone()))
    }

    /// solver.ts's checkSmt.
    fn run_fixture(text: &str) -> Vec<String> {
        let mut m = mk_manager(FIXTURE_STEP_LIMIT);
        let forms = match prepare_fixture(&mut m, text) {
            Ok(Prepared::Done(line)) => return vec![line],
            Ok(Prepared::Kernel(forms)) => forms,
            Err(error) => {
                return vec![format!(
                    "stop={} steps={}",
                    get_stop(&error),
                    m.limit.count()
                )];
            }
        };
        let mut asserted = AssertedFormulas::new(&m);
        let mut context = Context::new(m, PARAMS).unwrap();
        let mut run = |context: &mut Context| -> Result<String, SmtError> {
            for assertion in &forms {
                asserted.assert_expr(&mut context.m, *assertion)?;
            }
            context.setup_context()?;
            context.internalize_assertions(&mut asserted)?;
            let result = context.search()?;
            Ok(format!(
                "result={} conflicts={} steps={} instances={}",
                result.to_i8(),
                context.get_num_conflicts(),
                context.m.limit.count(),
                context.qmanager.get_num_instances()
            ))
        };
        let line = run(&mut context).unwrap_or_else(|error| {
            format!(
                "stop={} steps={}",
                get_stop(&error),
                context.m.limit.count()
            )
        });
        vec![line]
    }

    #[test]
    fn decides_arithmetic_problems_as_the_typescript() {
        let mut count = 0;
        for (name, lines) in get_sections() {
            let Some(text) = lines.first().and_then(|line| line.strip_prefix("text ")) else {
                continue;
            };
            assert_eq!(run_problem(text), lines[1..], "{name}");
            count += 1;
        }
        assert!(count > 0);
    }

    #[test]
    fn decides_the_fixtures_as_the_typescript() {
        let directory =
            Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../../tests/fixtures/smt");
        let mut count = 0;
        for (name, expected) in get_sections() {
            if !name.ends_with(".smt") {
                continue;
            }
            let text = fs::read_to_string(directory.join(&name)).unwrap();
            assert_eq!(run_fixture(&text), expected, "{name}");
            count += 1;
        }
        assert_eq!(count, 45);
    }
}
