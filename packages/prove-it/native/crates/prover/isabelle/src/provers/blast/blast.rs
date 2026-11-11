//! Ported from Isabelle2025's Provers/blast.ML. Copyright (c) 1986-2025 University of Cambridge,
//! Technische Universitaet Muenchen, and contributors, see LICENSE.
//!
//! Paulson's generic tableau prover with proof reconstruction. It converts subgoal 1 to
//! prototerms, Skolemizing its parameters, searches for a tableau proof with the claset's rules,
//! and replays the proof with Isabelle tactics, so the kernel checks every result. Blast ignores
//! the claset's wrappers and the elimination rules whose conclusion is not a formula variable.

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use crate::error::{Error, Exception, Res, error_exn};
use crate::pure::goal::select_goal;
use crate::pure::logic::{dest_implies, strip_params};
use crate::pure::name::make_name_context;
use crate::pure::object_logic::atomize_prems_tac;
use crate::pure::seq::{self, Seq, empty_seq, make_seq, of_cell};
use crate::pure::tactical::{GoalTactic, Tactic, eq_thm, or_else, then_tac};
use crate::pure::term::{Name, Term, TermNode, add_free_names, strip_comb};
use crate::pure::thm::{Thm, nprems};

use super::prove::{Tactics, prove};
use super::state::{BlastContext, BlastState, Branch, Choices, Formula, Level, backtrack, gensym};
use super::term::{
    BlastTerm, FALSE_NAME, GOAL_NAME, VarEntry, VarRef, add_terms_vars, blast_subst_bound,
    from_const, list_blast_comb, mk_blast_abs, mk_blast_bound, mk_blast_free, mk_blast_skolem,
    mk_blast_var, mk_goal, strip_blast_imp_concl, strip_blast_imp_prems,
};

/// Blast's depth_limit configuration option.
const DEPTH_LIMIT: i32 = 20;

/// TRANS: the subgoal has no translation, such as one applying an unknown to a non-parameter.
fn trans(message: &str) -> Error {
    Error::Trans(message.into())
}

fn initialize(context: &Rc<BlastContext>, state: &Thm) -> Res<BlastState> {
    for name in [GOAL_NAME, FALSE_NAME] {
        if context.logic.consts.contains_key(name) {
            return Err(error_exn(format!(
                "blast: theory contains reserved constant \"{name}\""
            )));
        }
    }
    Ok(BlastState {
        context: context.clone(),
        names: RefCell::new(make_name_context(&add_free_names(&state.prop, Vec::new()))),
        trail: RefCell::new(Vec::new()),
        tokens: Cell::new(0),
    })
}

fn discard_foralls(term: &Term) -> &Term {
    if let TermNode::App { fun, arg, .. } = &**term
        && fun.is_const_named("Pure.all")
        && let TermNode::Abs { body, .. } = &**arg
    {
        return discard_foralls(body);
    }
    term
}

struct SubgoalVar {
    name: Name,
    index: i32,
    var_ref: VarRef,
    /// The parameters the variable is applied to.
    bounds: Vec<i32>,
}

/// Translates a subgoal, Skolemizing all its parameters.
fn from_subgoal(state: &BlastState, term: &Term) -> Res<BlastTerm> {
    struct Translation<'a> {
        state: &'a BlastState,
        vars: Vec<SubgoalVar>,
        tvars: Vec<VarEntry>,
    }

    impl Translation<'_> {
        fn bounds(level: i32, args: &[Term]) -> Res<Vec<i32>> {
            args.iter()
                .map(|arg| {
                    let TermNode::Bound { index } = &**arg else {
                        return Err(trans("Function unknown's argument not a bound variable"));
                    };
                    if *index < level {
                        return Err(trans("Function unknown's argument not a parameter"));
                    }
                    Ok(index - level)
                })
                .collect()
        }

        fn apply(&mut self, level: i32, head: BlastTerm, args: &[Term]) -> Res<BlastTerm> {
            let args = args
                .iter()
                .map(|arg| self.from(level, arg))
                .collect::<Res<Vec<_>>>()?;
            Ok(list_blast_comb(head, args))
        }

        fn from(&mut self, level: i32, current: &Term) -> Res<BlastTerm> {
            let (head, args) = strip_comb(current);
            match &*head {
                TermNode::Const { name, ty } => {
                    let blast_head =
                        from_const(&self.state.context.logic.consts, &mut self.tvars, name, ty)?;
                    self.apply(level, blast_head, &args)
                }
                TermNode::Free { name, .. } => {
                    self.apply(level, mk_blast_free(name.clone()), &args)
                }
                TermNode::Bound { index } => self.apply(level, mk_blast_bound(*index), &args),
                TermNode::Var { name, index, .. } => {
                    let known = self
                        .vars
                        .iter()
                        .position(|entry| entry.name == *name && entry.index == *index);
                    let Some(known) = known else {
                        let var_ref = VarRef::new(None);
                        let bounds = Self::bounds(level, &args)?;
                        self.vars.insert(
                            0,
                            SubgoalVar {
                                name: name.clone(),
                                index: *index,
                                var_ref: var_ref.clone(),
                                bounds,
                            },
                        );
                        return Ok(mk_blast_var(var_ref));
                    };
                    let arg_bounds = Self::bounds(level, &args)?;
                    if self.vars[known].bounds == arg_bounds {
                        return Ok(mk_blast_var(self.vars[known].var_ref.clone()));
                    }
                    Err(trans(&format!("Discrepancy among occurrences of ?{name}")))
                }
                TermNode::Abs { name, body, .. } => {
                    if !args.is_empty() {
                        return Err(trans("argument not in normal form"));
                    }
                    Ok(mk_blast_abs(name.clone(), self.from(level + 1, body)?))
                }
                TermNode::App { .. } => Err(trans("strip_comb")),
            }
        }
    }

    let npars = strip_params(term).len();
    let mut translation = Translation {
        state,
        vars: Vec::new(),
        tvars: Vec::new(),
    };
    let mut result = translation.from(0, discard_foralls(term))?;
    for index in 0..npars as i32 {
        let args: Rc<[VarRef]> = translation
            .vars
            .iter()
            .filter(|entry| !entry.bounds.contains(&index))
            .map(|entry| entry.var_ref.clone())
            .collect();
        result = blast_subst_bound(&mk_blast_skolem(gensym(state, "T"), args), &result);
    }
    Ok(result)
}

struct EveryTrail {
    state: Thm,
    rest: Seq<Thm>,
    position: usize,
    next: Option<Rc<EveryTrail>>,
}

fn advance(
    tactics: &Rc<[Tactic]>,
    initial_trail: Option<Rc<EveryTrail>>,
    initial_position: usize,
    initial_state: Option<Thm>,
) -> Res<seq::Cell<Thm>> {
    let mut trail = initial_trail;
    let mut position = initial_position;
    let mut state = initial_state;
    loop {
        match state {
            None => {
                let Some(top) = trail else {
                    return Ok(None);
                };
                match top.rest.pull()? {
                    None => trail = top.next.clone(),
                    Some((result, rest)) if eq_thm(&top.state, &result) => {
                        trail = Some(Rc::new(EveryTrail {
                            state: top.state.clone(),
                            rest,
                            position: top.position,
                            next: top.next.clone(),
                        }));
                    }
                    Some((result, rest)) => {
                        position = top.position;
                        trail = Some(Rc::new(EveryTrail {
                            state: result.clone(),
                            rest,
                            position: top.position,
                            next: top.next.clone(),
                        }));
                        state = Some(result);
                    }
                }
            }
            Some(current) if position == tactics.len() => {
                let saved = trail;
                let tactics = tactics.clone();
                return Ok(Some((
                    current,
                    make_seq(move || advance(&tactics, saved.clone(), 0, None)),
                )));
            }
            Some(current) => match tactics[position](current)?.pull()? {
                None => state = None,
                Some((result, rest)) => {
                    trail = Some(Rc::new(EveryTrail {
                        state: result.clone(),
                        rest,
                        position: position + 1,
                        next: trail,
                    }));
                    position += 1;
                    state = Some(result);
                }
            },
        }
    }
}

/// EVERY, as a loop: Isabelle's EVY and evyBack call each other in tail position, so backtracking
/// over a long reconstruction must not grow the stack.
fn every_tac(tactics: Vec<Tactic>) -> Tactic {
    let tactics: Rc<[Tactic]> = tactics.into();
    Rc::new(move |start| {
        let tactics = tactics.clone();
        Ok(make_seq(move || {
            advance(&tactics, None, 0, Some(start.clone()))
        }))
    })
}

fn init_branch(terms: Vec<BlastTerm>, lim: i32) -> Branch {
    Branch {
        vars: add_terms_vars(&terms, Vec::new()),
        pairs: vec![Level {
            safe: terms
                .into_iter()
                .map(|term| Formula { term, md: true })
                .collect(),
            r#unsafe: Vec::new(),
        }],
        lits: Vec::new(),
        lim,
    }
}

/// The tableau engine and proof reconstruction on subgoal 1, with depth limit lim.
fn raw_blast(context: Rc<BlastContext>, lim: i32) -> Tactic {
    Rc::new(move |goal_state: Thm| {
        let state = initialize(&context, &goal_state)?;
        let cont = |tactics: Tactics, choices: Choices| -> Res<Seq<Thm>> {
            let cell = (|| {
                let mut replay = Vec::new();
                let mut current = &tactics;
                while let Some(cell) = current {
                    replay.push((cell.head)(1)?);
                    current = &cell.tail;
                }
                replay.reverse();
                every_tac(replay)(goal_state.clone())?.pull()
            })();
            match cell {
                Err(error) if error.is(Exception::Term) => Err(backtrack(&choices)),
                Err(error) => Err(error),
                Ok(None) => Err(backtrack(&choices)),
                Ok(cell) => Ok(of_cell(cell)),
            }
        };
        let result = (|| {
            let skoprem = from_subgoal(&state, &dest_implies(&goal_state.prop)?.0)?;
            let trueprop = &*context.data.trueprop;
            let mut terms = vec![mk_goal(strip_blast_imp_concl(trueprop, &skoprem))];
            terms.extend(strip_blast_imp_prems(trueprop, &skoprem));
            prove(&state, vec![init_branch(terms, lim)], &cont)
        })();
        match result {
            Err(Error::Backtrack(None) | Error::Trans(_)) => Ok(empty_seq()),
            result => result,
        }
    })
}

/// Blast.depth_tac: blast with a fixed depth limit. The TypeScript builds atomize_prems_tac each
/// time it is given a goal index; this builds it once, raising where it raises.
pub fn blast_depth_tac(context: Rc<BlastContext>, limit: i32) -> Res<GoalTactic> {
    let atomize = atomize_prems_tac(&context.data.atomize)?;
    Ok(Rc::new(move |index| {
        select_goal(then_tac(atomize(1), raw_blast(context.clone(), limit)))(index)
    }))
}

/// Search.DEEPEN (1, lim) from depth m on goal 1.
fn deepen(context: Rc<BlastContext>, limit: i32, depth: i32) -> Tactic {
    Rc::new(move |state: Thm| {
        if nprems(&state) < 1 || depth > limit {
            return Ok(empty_seq());
        }
        or_else(
            raw_blast(context.clone(), depth),
            deepen(context.clone(), limit, depth + 1),
        )(state)
    })
}

/// Blast.blast_tac: iterative deepening up to the depth limit. Builds atomize_prems_tac once, as
/// blast_depth_tac does.
pub fn blast_tac(context: Rc<BlastContext>) -> Res<GoalTactic> {
    let atomize = atomize_prems_tac(&context.data.atomize)?;
    Ok(Rc::new(move |index| {
        select_goal(then_tac(
            atomize(1),
            deepen(context.clone(), DEPTH_LIMIT, 0),
        ))(index)
    }))
}

#[cfg(test)]
mod tests {
    use crate::provers::testing::check_provers;

    // The expectations are recorded from the TypeScript on the fixture theories' statements and on
    // facts and rules of the logic, under a step limit.
    #[test]
    fn blast_matches_the_typescript() {
        check_provers(include_str!("../../../testdata/provers/blast.txt"));
    }
}
