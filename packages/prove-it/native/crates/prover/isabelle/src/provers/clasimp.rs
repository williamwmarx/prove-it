//! Ported from Isabelle2025's Provers/clasimp.ML and the prune_params_tac of Pure/tactic.ML.
//! Copyright (c) 1986-2025 University of Cambridge, Technische Universitaet Muenchen, and
//! contributors, see LICENSE.
//!
//! The classical reasoner combined with the simplifier: auto, clarsimp and force.
//!
//! (`provers/clasimp.ts`.) The tactics that build a simpset (prune_params_tac) or atomize_prems_tac
//! (force's best-first search, blast) raise where those do, when the tactic is built.

use std::rc::Rc;

use crate::error::Res;
use crate::pure::conv::{Conversion, gconv_rule};
use crate::pure::drule::triv_forall_equality;
use crate::pure::goal::select_goal;
use crate::pure::raw_simplifier::{SimpContext, add_simps, empty_simpset};
use crate::pure::rewriter::{RewriteMode, rewrite_cterm, simple_prover};
use crate::pure::simplifier::{asm_full_simp_tac, safe_asm_full_simp_tac};
use crate::pure::tactical::{
    GoalTactic, Tactic, all_goals, all_tac, append_tac, changed, depth_solve, determ, every,
    first_goal_tac, no_tac, or_else_goal, primitive, repeat_determ, then_all_new, then_else,
    then_tac, try_tac,
};
use crate::pure::thm::{Thm, nprems};

use super::classical::{
    ClassicalContext, add_safter, addbefore, app_wrappers, clarify_tac, first_best_tac,
    inst0_step_tac, instp_step_tac, safe_steps_tac, safe_tac, unsafe_step_tac, with_claset,
};

/// Blast.depth_tac, the Blast argument of the Clasimp functor.
pub type BlastDepthTac = Rc<dyn Fn(&ClassicalContext, i32) -> Res<GoalTactic>>;

#[derive(Clone)]
pub struct ClasimpContext {
    pub classical: ClassicalContext,
    pub simp: SimpContext,
    pub blast_depth_tac: BlastDepthTac,
}

/// addss: the simplifier as an unsafe wrapper.
fn addss(context: &ClasimpContext) -> ClassicalContext {
    let simp = context.simp.clone();
    with_claset(
        &context.classical,
        addbefore(
            &context.classical.claset,
            "asm_full_simp_tac",
            Rc::new(move |index| changed(asm_full_simp_tac(&simp)(index))),
        ),
    )
}

/// addSss: the simplifier as a safe wrapper.
fn add_sss(context: &ClasimpContext) -> ClassicalContext {
    let simp = context.simp.clone();
    with_claset(
        &context.classical,
        add_safter(
            &context.classical.claset,
            "safe_asm_full_simp_tac",
            Rc::new(move |index| changed(safe_asm_full_simp_tac(&simp)(index))),
        ),
    )
}

pub fn clarsimp_tac(context: &ClasimpContext) -> GoalTactic {
    then_all_new(
        safe_asm_full_simp_tac(&context.simp),
        clarify_tac(&add_sss(context)),
    )
}

/// A variant of Classical.depth_tac that keeps the simplifier from interfering with dup_step_tac.
fn nodup_depth_tac(context: &ClassicalContext, limit: i32) -> GoalTactic {
    let context = context.clone();
    Rc::new(move |index| {
        let context = context.clone();
        Rc::new(move |state| {
            let unsafe_steps = if limit == 0 {
                no_tac()
            } else {
                let inner = context.clone();
                then_tac(
                    app_wrappers(
                        &context,
                        Rc::new(move |goal| {
                            append_tac(instp_step_tac(&inner)(goal), unsafe_step_tac(&inner)(goal))
                        }),
                    )(1),
                    depth_solve(nodup_depth_tac(&context, limit - 1)(1)),
                )
            };
            select_goal(then_else(
                safe_steps_tac(&context)(1),
                depth_solve(nodup_depth_tac(&context, limit)(1)),
                append_tac(inst0_step_tac(&context)(1), unsafe_steps),
            ))(index)(state)
        })
    })
}

/// prune_params_tac: drops the parameters that no goal uses.
fn prune_params_tac(simp: &SimpContext) -> Res<Tactic> {
    let empty = SimpContext {
        simpset: empty_simpset(),
        ..simp.clone()
    };
    let context = SimpContext {
        simpset: add_simps(&empty, &[triv_forall_equality()])?,
        ..empty
    };
    let convert: Conversion = Rc::new(move |term| {
        rewrite_cterm(
            RewriteMode {
                simprem: true,
                useprem: true,
                mutsimp: true,
            },
            Rc::new(simple_prover),
            &context,
            term,
        )
    });
    Ok(primitive(move |state: Thm| {
        (1..=nprems(&state) as i32).try_fold(state.clone(), |current, index| {
            gconv_rule(&convert, index, &current)
        })
    }))
}

fn mk_auto_tac(context: &ClasimpContext, depth: i32, nodup_depth: i32) -> Res<Tactic> {
    let nodup_context = context.clone();
    let main_tac = or_else_goal(
        (context.blast_depth_tac)(&context.classical, depth)?,
        Rc::new(move |index| changed(nodup_depth_tac(&addss(&nodup_context), nodup_depth)(index))),
    );
    Ok(every(vec![
        // PARALLEL_ALLGOALS simplifies each goal on its own only when no goal has schematic
        // variables, which gives the same result as simplifying them in turn.
        determ(all_goals(asm_full_simp_tac(&context.simp))),
        try_tac(safe_tac(&context.classical)),
        repeat_determ(first_goal_tac(main_tac)),
        try_tac(safe_tac(&add_sss(context))),
        prune_params_tac(&context.simp)?,
    ]))
}

pub fn auto_tac(context: &ClasimpContext) -> Res<Tactic> {
    mk_auto_tac(context, 4, 2)
}

/// force_tac: aims to solve the goal outright, with clarify, the simplifier and best-first search.
pub fn force_tac(context: &ClasimpContext, atomize_rules: &[Thm]) -> Res<GoalTactic> {
    let classical = addss(context);
    let simp = context.simp.clone();
    Ok(select_goal(every(vec![
        clarify_tac(&classical)(1),
        Rc::new(move |state: Thm| {
            if nprems(&state) == 0 {
                all_tac()(state)
            } else {
                asm_full_simp_tac(&simp)(1)(state)
            }
        }),
        all_goals(first_best_tac(&classical, atomize_rules)?),
    ])))
}
