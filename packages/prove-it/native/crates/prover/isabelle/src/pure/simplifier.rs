//! Ported from Isabelle2025's Pure/simplifier.ML and the PREFER_GOAL of Pure/goal.ML, the
//! simplification tactics. Copyright (c) 1986-2025 University of Cambridge, Technische Universitaet
//! Muenchen, and contributors, see LICENSE.
//!
//! (`pure/simplifier.ts`.) The simplifier recurses through its prover: proving a premise of a
//! conditional rule simplifies it with the subgoaler, which rewrites again, so the prover enters a
//! level of `check_stack`.

use std::rc::Rc;

use crate::error::Res;

use super::conv::fconv_rule;
use super::drule::{gen_all, is_norm_hhf, norm_hhf_eq};
use super::goal::prefer_goal;
use super::interrupt::check_stack;
use super::raw_simplifier::{SimpContext, Simpset, Solver, add_simps, empty_simpset};
use super::rewriter::{Prover, RewriteMode, generic_rewrite_goal_tac, rewrite_conv, simple_prover};
use super::tactical::{
    GoalTactic, Tactic, depth_solve, first_goal, no_tac, or_else, then_all_new, then_tac, try_tac,
};
use super::thm::Thm;

fn with_solvers(context: &SimpContext, solvers: &Rc<[Solver]>) -> SimpContext {
    SimpContext {
        simpset: Simpset {
            unsafe_solvers: solvers.clone(),
            safe_solvers: solvers.clone(),
            ..context.simpset.clone()
        },
        ..context.clone()
    }
}

/// solve_all_tac: solves goal 1 completely with the subgoaler.
fn solve_all_tac(solvers: &Rc<[Solver]>, context: &SimpContext) -> Tactic {
    let inner = with_solvers(context, solvers);
    let solve_tac = then_all_new((inner.simpset.subgoal_tac)(&inner), Rc::new(|_| no_tac()));
    depth_solve(solve_tac(1))
}

fn loop_tac(context: &SimpContext) -> GoalTactic {
    first_goal(
        context
            .simpset
            .loop_tacs
            .iter()
            .rev()
            .map(|looper| (looper.tactic)(context))
            .collect(),
    )
}

fn single_prover(solvers: Rc<[Solver]>) -> Prover {
    Rc::new(move |context, thm| {
        let _depth = check_stack()?;
        Ok(solve_all_tac(&solvers, context)(thm.clone())?
            .pull()?
            .map(|(result, _)| result))
    })
}

/// What generic_simp_tac's loop shares.
struct SimpLoop {
    mode: RewriteMode,
    context: SimpContext,
    prover: Prover,
    solve_tac: GoalTactic,
    looper: GoalTactic,
}

fn simp_loop_tac(shared: Rc<SimpLoop>) -> GoalTactic {
    Rc::new(move |goal| {
        then_tac(
            generic_rewrite_goal_tac(shared.mode, shared.prover.clone(), &shared.context, goal),
            or_else(
                (shared.solve_tac)(goal),
                try_tac(then_all_new(
                    shared.looper.clone(),
                    simp_loop_tac(shared.clone()),
                )(goal)),
            ),
        )
    })
}

/// generic_simp_tac
fn generic_simp_tac(is_safe: bool, mode: RewriteMode, context: &SimpContext) -> GoalTactic {
    let context = context.clone();
    Rc::new(move |index| {
        let looper = loop_tac(&context);
        let solvers = if is_safe {
            &context.simpset.safe_solvers
        } else {
            &context.simpset.unsafe_solvers
        };
        let solve_tac = first_goal(
            solvers
                .iter()
                .rev()
                .map(|solver| (solver.tactic)(&context))
                .collect(),
        );
        let shared = Rc::new(SimpLoop {
            mode,
            context: context.clone(),
            prover: single_prover(context.simpset.unsafe_solvers.clone()),
            solve_tac,
            looper,
        });
        prefer_goal(simp_loop_tac(shared)(1))(index)
    })
}

pub fn asm_simp_tac(context: &SimpContext) -> GoalTactic {
    generic_simp_tac(
        false,
        RewriteMode {
            simprem: false,
            useprem: true,
            mutsimp: false,
        },
        context,
    )
}

pub fn asm_lr_simp_tac(context: &SimpContext) -> GoalTactic {
    generic_simp_tac(
        false,
        RewriteMode {
            simprem: true,
            useprem: true,
            mutsimp: false,
        },
        context,
    )
}

pub fn asm_full_simp_tac(context: &SimpContext) -> GoalTactic {
    generic_simp_tac(
        false,
        RewriteMode {
            simprem: true,
            useprem: true,
            mutsimp: true,
        },
        context,
    )
}

pub fn safe_asm_full_simp_tac(context: &SimpContext) -> GoalTactic {
    generic_simp_tac(
        true,
        RewriteMode {
            simprem: true,
            useprem: true,
            mutsimp: true,
        },
        context,
    )
}

/// Simplifier.simp_thm: simplifies a theorem's proposition.
fn simp_thm(mode: RewriteMode, context: &SimpContext, thm: &Thm) -> Res<Thm> {
    let prover = single_prover(
        context
            .simpset
            .unsafe_solvers
            .iter()
            .rev()
            .cloned()
            .collect(),
    );
    fconv_rule(&rewrite_conv(mode, prover, context.clone()), thm)
}

pub fn simplify(context: &SimpContext, thm: &Thm) -> Res<Thm> {
    simp_thm(
        RewriteMode {
            simprem: false,
            useprem: false,
            mutsimp: false,
        },
        context,
        thm,
    )
}

/// Raw_Simplifier.norm_hhf: moves the quantifiers of a theorem left of its implications, then makes
/// the outermost ones schematic. Drule.sort_constraint_eq, the other rule of hhf_ss, never applies:
/// tlapm's terms carry no sort constraints.
pub fn norm_hhf(thm: &Thm) -> Res<Thm> {
    if is_norm_hhf(false, &thm.prop) {
        return gen_all(thm);
    }
    let empty = SimpContext {
        simpset: empty_simpset(),
        bounds: 0,
    };
    let context = SimpContext {
        simpset: add_simps(&empty, &[norm_hhf_eq()])?,
        ..empty
    };
    gen_all(&fconv_rule(
        &rewrite_conv(
            RewriteMode {
                simprem: true,
                useprem: false,
                mutsimp: false,
            },
            Rc::new(simple_prover),
            context,
        ),
        thm,
    )?)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pure::interrupt::with_limits;
    use crate::pure::logic::{dest_equals, is_equals, strip_imp_concl, strip_imp_prems};
    use crate::pure::object_logic::atomize_prems_tac;
    use crate::pure::raw_simplifier::{add_prems, extract_safe_rrules, insert_rrule, mk_procrule};
    use crate::pure::rewriter::rewrite_cterm;
    use crate::pure::simp_testing::fixture_goal;
    use crate::pure::term::{Term, maxidx_of_term};
    use crate::pure::testing::{attempt, check_problems, parse_term};
    use crate::pure::thm::tests::{digest, many, one, show_thm};
    use crate::pure::thm::{assume, axiom_thm, trivial};
    use crate::tla::classical_setup::get_fact;
    use crate::tla::context::ATOMIZE_RULES;
    use crate::tla::logic::{TlaLogic, load_logic};
    use crate::tla::simpdata::get_simpset;
    use prove_decide::Limits;

    fn mode_of(code: &str) -> RewriteMode {
        let bits = code.as_bytes();
        RewriteMode {
            simprem: bits[0] == b'1',
            useprem: bits[1] == b'1',
            mutsimp: bits[2] == b'1',
        }
    }

    fn limits_of(field: &str) -> Limits {
        let limit = (field != "Infinity").then(|| field.parse().unwrap());
        Limits::new(f64::INFINITY, limit, None)
    }

    /// A term's text, or `@name`: the statement of a fixture.
    fn read_goal(field: &str) -> Term {
        match field.strip_prefix('@') {
            Some(name) => fixture_goal(name),
            None => parse_term(field),
        }
    }

    struct Problems {
        logic: Rc<TlaLogic>,
        simpset: Simpset,
    }

    impl Problems {
        fn context(&self) -> SimpContext {
            SimpContext {
                simpset: self.simpset.clone(),
                bounds: 0,
            }
        }

        /// Runs a problem under its limits, and adds the steps it took.
        fn run(&self, limit: &str, solve: impl FnOnce(&mut Vec<String>)) -> Vec<String> {
            let limits = limits_of(limit);
            let mut lines = Vec::new();
            with_limits(&limits, || solve(&mut lines));
            lines.push(format!("steps {}", limits.steps()));
            lines
        }

        fn solve(&self, kind: &str, fields: &[&str]) -> Vec<String> {
            match kind {
                "rewrite" => self.run(fields[1], |lines| {
                    one(lines, "result", || {
                        rewrite_cterm(
                            mode_of(fields[0]),
                            Rc::new(simple_prover),
                            &self.context(),
                            &read_goal(fields[2]),
                        )
                    })
                }),
                "prems" => self.run(fields[1], |lines| {
                    one(lines, "result", || {
                        let parsed = read_goal(fields[2]);
                        let empty = self.context();
                        let asms = strip_imp_prems(&parsed)
                            .into_iter()
                            .filter(|prem| maxidx_of_term(prem, -1) == -1)
                            .map(assume)
                            .collect::<Res<Vec<_>>>()?;
                        let mut extended = self.simpset.clone();
                        for asm in &asms {
                            for raw in extract_safe_rrules(&empty, asm)? {
                                extended = insert_rrule(&raw, &extended);
                            }
                        }
                        let context = SimpContext {
                            simpset: add_prems(&asms, &extended),
                            ..empty
                        };
                        rewrite_cterm(
                            mode_of(fields[0]),
                            Rc::new(simple_prover),
                            &context,
                            strip_imp_concl(&parsed),
                        )
                    })
                }),
                "simplify" => self.run(fields[0], |lines| {
                    one(lines, "result", || {
                        simplify(&self.context(), &axiom_thm(parse_term(fields[1])))
                    })
                }),
                "rrules" => self.run(fields[0], |lines| self.rrules(lines, fields[1])),
                "norm_hhf" => self.run("Infinity", |lines| {
                    one(lines, "result", || {
                        norm_hhf(&axiom_thm(parse_term(fields[0])))
                    })
                }),
                "tactic" => self.run(fields[2], |lines| {
                    let tactic = match fields[0] {
                        "asm_simp" => asm_simp_tac,
                        "asm_lr_simp" => asm_lr_simp_tac,
                        "asm_full_simp" => asm_full_simp_tac,
                        "safe_asm_full_simp" => safe_asm_full_simp_tac,
                        name => panic!("unknown tactic {name}"),
                    };
                    many(lines, "results", fields[1].parse().unwrap(), || {
                        tactic(&self.context())(1)(trivial(&read_goal(fields[3]))?)
                    })
                }),
                "atomize" => self.run("Infinity", |lines| {
                    let rules: Vec<Thm> = ATOMIZE_RULES
                        .iter()
                        .map(|name| get_fact(&self.logic, name).unwrap())
                        .collect();
                    many(lines, "results", fields[0].parse().unwrap(), || {
                        atomize_prems_tac(&rules)?(1)(trivial(&read_goal(fields[1]))?)
                    })
                }),
                _ => panic!("unknown problem {kind}"),
            }
        }

        /// How a theorem becomes rewrite rules: mk, extract_safe_rrules, add_simps and
        /// mk_procrule.
        fn rrules(&self, lines: &mut Vec<String>, text: &str) {
            let thm = axiom_thm(parse_term(text));
            let context = self.context();
            lines.push("mk".into());
            attempt(lines, |lines| {
                for rew in (self.simpset.mk_rews.mk)(&thm, &context)? {
                    lines.extend(show_thm(&rew));
                }
                Ok(())
            });
            lines.push("extract_safe_rrules".into());
            attempt(lines, |lines| {
                for raw in extract_safe_rrules(&context, &thm)? {
                    lines.push(format!(
                        "rrule {} {} {}",
                        raw.perm,
                        digest(&raw.lhs),
                        digest(&raw.elhs)
                    ));
                    lines.extend(show_thm(&raw.thm));
                }
                Ok(())
            });
            lines.push("mk_procrule".into());
            attempt(lines, |lines| {
                for rrule in mk_procrule(&thm)? {
                    lines.push(format!(
                        "rrule {} {} {} {} {}",
                        rrule.perm,
                        rrule.extra,
                        rrule.fo,
                        digest(&rrule.lhs),
                        digest(&rrule.elhs)
                    ));
                    lines.extend(show_thm(&rrule.thm));
                }
                Ok(())
            });
            one(lines, "add_simps", || {
                let empty = SimpContext {
                    simpset: empty_simpset(),
                    bounds: 0,
                };
                let added = SimpContext {
                    simpset: add_simps(&empty, std::slice::from_ref(&thm))?,
                    ..empty
                };
                let concl = strip_imp_concl(&thm.prop);
                let lhs = if is_equals(concl) {
                    dest_equals(concl)?.0
                } else {
                    thm.prop.clone()
                };
                rewrite_cterm(mode_of("111"), Rc::new(simple_prover), &added, &lhs)
            });
        }
    }

    /// Checks a file of problems on a thread with room for the simplifier's recursion.
    fn check_file(text: &'static str) {
        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(move || {
                let logic = load_logic();
                let simpset = get_simpset(&logic).unwrap();
                let problems = Problems { logic, simpset };
                check_problems(text, |kind, fields| problems.solve(kind, fields));
            })
            .unwrap()
            .join()
            .unwrap();
    }

    // The expectations are recorded from raw-simplifier.ts, rewriter.ts and simplifier.ts, with
    // simpdata.ts's simpset.
    #[test]
    fn rewriting_matches_the_typescript() {
        check_file(include_str!("../../testdata/kernel/simp.txt"));
    }

    // The expectations are recorded from simplifier.ts and object-logic.ts.
    #[test]
    fn simp_tactics_match_the_typescript() {
        check_file(include_str!("../../testdata/kernel/simp-tac.txt"));
    }
}
