//! Ported from Isabelle2025's Provers/blast.ML. Copyright (c) 1986-2025 University of Cambridge,
//! Technische Universitaet Muenchen, and contributors, see LICENSE.
//!
//! The tableau prover, based on leanTaP. It works on a list of branches, each with its unexpanded
//! formulae, its literals and a bound on unsafe expansions. Every inference records the tactic
//! that replays it; once all branches close, the continuation reconstructs the proof. Each
//! recursion level that can be backtracked to owns a token, and a choice point raises it.
//!
//! (`provers/blast/prove.ts`.) Each level of the search enters `check_stack`, as JavaScript's
//! stack would bound it.

use crate::error::{Error, Res};
use crate::pure::interrupt::{check_interrupt, check_stack};
use crate::pure::list::{List, cons};
use crate::pure::seq::Seq;
use crate::pure::tactic::{NetPair, TaggedRule};
use crate::pure::thm::Thm;

use super::branch::{
    add_lit, equal_subst, join_md, log4, r#match, neg_of_goal, neg_of_goals, next_vars, prune,
    try_close,
};
use super::rules::{ReplayTactic, TableauRule, neg_of_goal_tac, net_mk_rules, replay_tactic};
use super::state::{
    BlastState, Branch, Choice, Choices, Formula, Level, backtrack, clear_to, is_backtrack_to,
    unify,
};
use super::term::{
    BlastTerm, VarRef, add_term_vars, add_terms_vars, is_goal, norm, same_vars, vars_in_vars,
};

/// The tactics that replay the inferences so far, latest first.
pub type Tactics = List<ReplayTactic>;

pub type Continuation<'a> = &'a dyn Fn(Tactics, Choices) -> Res<Seq<Thm>>;

/// A step either finishes the search or continues the same branches without a choice point, which
/// blast.ML does by a tail call. prv loops on the latter, so a long search can't exhaust the stack.
enum Step {
    Done(Seq<Thm>),
    Next {
        tactics: Tactics,
        choices: Choices,
        brs: Vec<Branch>,
    },
}

fn add_prems_vars(prems: &[Vec<BlastTerm>], vars: Vec<VarRef>) -> Vec<VarRef> {
    prems
        .iter()
        .rev()
        .fold(vars, |result, prem| add_terms_vars(prem, result))
}

/// Whether the error backtracks to the choice point of token; any other error propagates.
fn catch_backtrack(error: Error, token: u64) -> Res<()> {
    if is_backtrack_to(&error, Some(token)) {
        Ok(())
    } else {
        Err(error)
    }
}

struct Prover<'a> {
    state: &'a BlastState,
    cont: Continuation<'a>,
    safe_list: [&'a NetPair<TaggedRule>; 2],
    unsafe_list: [&'a NetPair<TaggedRule>; 1],
}

impl Prover<'_> {
    /// Applies a safe rule only, possibly allowing instantiation; defers any unsafe formulae.
    fn safe_step(&self, tactics: Tactics, choices: Choices, brs: &[Branch]) -> Res<Step> {
        let state = self.state;
        let token = state.new_token();
        let branch = &brs[0];
        let rest = &brs[1..];
        let head = &branch.pairs[0];
        let md = head.safe[0].md;
        let queued = Level {
            safe: head.safe[1..].to_vec(),
            r#unsafe: head.r#unsafe.clone(),
        };
        let mut pairs = vec![queued.clone()];
        pairs.extend(branch.pairs[1..].iter().cloned());
        let ntrl = state.trail_len();
        let nbrs = brs.len();
        let nxt_vars = next_vars(rest);
        let formula = norm(&head.safe[0].term);
        let rules = net_mk_rules(state, &formula, &branch.vars, &self.safe_list)?;
        // Makes the new branches, decrementing lim if instantiations occur.
        let new_br = |vars: &[VarRef], lim: i32, prems: &[Vec<BlastTerm>]| -> Vec<Branch> {
            let mut result: Vec<Branch> = prems
                .iter()
                .map(|prem| {
                    let level = Level {
                        safe: join_md(md, prem),
                        r#unsafe: Vec::new(),
                    };
                    if prem.iter().any(is_goal) {
                        let mut new_pairs = vec![level];
                        new_pairs.extend(neg_of_goals(state, &pairs));
                        Branch {
                            pairs: new_pairs,
                            lits: branch
                                .lits
                                .iter()
                                .map(|lit| neg_of_goal(state, lit))
                                .collect(),
                            vars: vars.to_vec(),
                            lim,
                        }
                    } else {
                        let mut new_pairs = vec![level];
                        new_pairs.extend(pairs.iter().cloned());
                        Branch {
                            pairs: new_pairs,
                            lits: branch.lits.clone(),
                            vars: vars.to_vec(),
                            lim,
                        }
                    }
                })
                .collect();
            result.extend(rest.iter().cloned());
            result
        };
        // Seeks a matching rule; if unifiable, adds its premises to the branch. None is
        // NEWBRANCHES.
        let deeper = |rules: &[TableauRule]| -> Res<Option<Seq<Thm>>> {
            for rule in rules {
                let major = rule.major();
                if !unify(state, &add_term_vars(&major, Vec::new()), &major, &formula) {
                    continue;
                }
                let is_updated = ntrl < state.trail_len();
                // Discourages branching updates.
                let lim = if is_updated {
                    branch.lim - (1 + log4(rules.len()))
                } else {
                    branch.lim
                };
                let prems = rule.prems();
                let vars = add_prems_vars(&prems, vars_in_vars(&branch.vars));
                let next_choices = cons(
                    Choice {
                        ntrl,
                        nbrs,
                        token: Some(token),
                    },
                    choices.clone(),
                );
                let next_tactics = cons(rule.tactic(is_updated, false, true), tactics.clone());
                let result = if prems.is_empty() {
                    self.prv(
                        next_tactics,
                        prune(state, nbrs, &nxt_vars, next_choices),
                        rest.to_vec(),
                    )
                } else if lim < 0 {
                    // Faster to kill all the alternatives.
                    clear_to(state, ntrl);
                    return Ok(None);
                } else {
                    self.prv(next_tactics, next_choices, new_br(&vars, lim, &prems))
                };
                match result {
                    Ok(seq) => return Ok(Some(seq)),
                    Err(error) => catch_backtrack(error, token)?,
                }
                // Backtracks at this level, resetting variables and trying another rule, or to
                // the previous level.
                if !is_updated {
                    return Err(backtrack(&choices));
                }
                clear_to(state, ntrl);
            }
            Ok(None)
        };
        // Tries to close the branch by unifying the formula with a literal. None is CLOSEF.
        let close_f = |literals: &[BlastTerm]| -> Res<Option<Seq<Thm>>> {
            for literal in literals {
                let Some(tactic) = try_close(state, &formula, literal) else {
                    continue;
                };
                let next_choices = prune(
                    state,
                    nbrs,
                    &nxt_vars,
                    cons(
                        Choice {
                            ntrl,
                            nbrs,
                            token: Some(token),
                        },
                        choices.clone(),
                    ),
                );
                match self.prv(
                    cons(replay_tactic(tactic), tactics.clone()),
                    next_choices,
                    rest.to_vec(),
                ) {
                    Ok(seq) => return Ok(Some(seq)),
                    Err(error) => catch_backtrack(error, token)?,
                }
                clear_to(state, ntrl);
            }
            Ok(None)
        };
        // Tries to unify a queued formula, safe or unsafe, with the formula.
        let close_fl = |levels: &[Level]| -> Res<Option<Seq<Thm>>> {
            for level in levels {
                let safe: Vec<BlastTerm> = level
                    .safe
                    .iter()
                    .map(|queued| queued.term.clone())
                    .collect();
                if let Some(closed) = close_f(&safe)? {
                    return Ok(Some(closed));
                }
                let r#unsafe: Vec<BlastTerm> = level
                    .r#unsafe
                    .iter()
                    .map(|queued| queued.term.clone())
                    .collect();
                if let Some(closed) = close_f(&r#unsafe)? {
                    return Ok(Some(closed));
                }
            }
            Ok(None)
        };
        if branch.lim < 0 {
            return Err(backtrack(&choices));
        }
        let substituted = equal_subst(
            state,
            &formula,
            &Branch {
                pairs: pairs.clone(),
                ..branch.clone()
            },
        );
        if let Some(substituted) = substituted {
            let mut next_brs = vec![substituted];
            next_brs.extend(rest.iter().cloned());
            return Ok(Step::Next {
                tactics: cons(
                    replay_tactic(state.context.data.hyp_subst_tac.clone()),
                    tactics,
                ),
                choices,
                brs: next_brs,
            });
        }
        if let Some(closed) = close_f(&branch.lits)? {
            return Ok(Step::Done(closed));
        }
        if let Some(closed) = close_fl(&pairs)? {
            return Ok(Step::Done(closed));
        }
        if let Some(closed) = deeper(&rules)? {
            return Ok(Step::Done(closed));
        }
        if net_mk_rules(state, &formula, &branch.vars, &self.unsafe_list)?.is_empty() {
            // There are no plausible unsafe rules: the formula becomes a literal.
            let mut next_brs = vec![Branch {
                lits: add_lit(state, &formula, &branch.lits),
                pairs,
                vars: branch.vars.clone(),
                lim: branch.lim,
            }];
            next_brs.extend(rest.iter().cloned());
            return Ok(Step::Next {
                tactics,
                choices,
                brs: next_brs,
            });
        }
        // The formula admits some unsafe rules: try them later.
        let deferred = Formula {
            term: neg_of_goal(state, &formula),
            md,
        };
        let mut queued_unsafe = queued.r#unsafe;
        queued_unsafe.push(deferred);
        let mut next_pairs = vec![Level {
            safe: queued.safe,
            r#unsafe: queued_unsafe,
        }];
        next_pairs.extend(pairs[1..].iter().cloned());
        let mut next_brs = vec![Branch {
            pairs: next_pairs,
            lits: branch.lits.clone(),
            vars: branch.vars.clone(),
            lim: branch.lim,
        }];
        next_brs.extend(rest.iter().cloned());
        Ok(Step::Next {
            tactics: if is_goal(&formula) {
                cons(replay_tactic(neg_of_goal_tac(state)), tactics)
            } else {
                tactics
            },
            choices,
            brs: next_brs,
        })
    }

    /// No safe steps are possible at any level: applies an unsafe rule.
    fn unsafe_step(&self, tactics: Tactics, choices: Choices, brs: &[Branch]) -> Res<Step> {
        let state = self.state;
        let token = state.new_token();
        let branch = &brs[0];
        let rest = &brs[1..];
        let queued = &branch.pairs[0].r#unsafe;
        let md = queued[0].md;
        let others = &queued[1..];
        let formula = norm(&queued[0].term);
        let ntrl = state.trail_len();
        let rules = net_mk_rules(state, &formula, &branch.vars, &self.unsafe_list)?;
        // The new premises of unsafe rules may not be duplicated.
        let new_prem = |vars: &[VarRef],
                        pattern: &BlastTerm,
                        is_dup: bool,
                        lim: i32,
                        prem: &[BlastTerm]|
         -> Branch {
            let safe: Vec<Formula> = prem
                .iter()
                .map(|term| Formula {
                    term: term.clone(),
                    md: false,
                })
                .collect();
            let mut r#unsafe = others.to_vec();
            if is_dup {
                r#unsafe.push(Formula {
                    term: neg_of_goal(state, &formula),
                    md,
                });
            }
            Branch {
                // A premise recursive in the rule makes no new stack frame: its unsafe premises
                // end up at the back of the queue, preventing the exclusion of others.
                pairs: if prem.iter().any(|term| r#match(state, pattern, term)) {
                    vec![Level { safe, r#unsafe }]
                } else {
                    vec![
                        Level {
                            safe,
                            r#unsafe: Vec::new(),
                        },
                        Level {
                            safe: Vec::new(),
                            r#unsafe,
                        },
                    ]
                },
                lits: if prem.iter().any(is_goal) {
                    branch
                        .lits
                        .iter()
                        .map(|lit| neg_of_goal(state, lit))
                        .collect()
                } else {
                    branch.lits.clone()
                },
                vars: vars.to_vec(),
                lim,
            }
        };
        let deeper = || -> Res<Option<Seq<Thm>>> {
            for (position, rule) in rules.iter().enumerate() {
                let major = rule.major();
                if !unify(state, &add_term_vars(&major, Vec::new()), &major, &formula) {
                    continue;
                }
                let is_updated = ntrl < state.trail_len();
                let vars = vars_in_vars(&branch.vars);
                let prems = rule.prems();
                let new_vars = add_prems_vars(&prems, vars.clone());
                // Duplicates the formula if md permits.
                let is_dup = md;
                // Decrements lim extra if updates occur.
                let lim = if is_updated {
                    branch.lim - (1 + log4(rules.len()))
                } else {
                    branch.lim - 1
                };
                // Allows backtracking from a rule application if other matching rules exist, if
                // the rule updated variables, or if it introduced no new variables, so that it is
                // not a standard gamma-rule. This emulates fast_tac, which allows all unsafe steps
                // to be undone.
                let may_undo =
                    position + 1 < rules.len() || is_updated || same_vars(&vars, &new_vars);
                let tactic = rule.tactic(is_updated, is_dup, true);
                // Faster to kill all the alternatives.
                if lim < 0 && !prems.is_empty() {
                    clear_to(state, ntrl);
                    return Ok(None);
                }
                let mut next_brs: Vec<Branch> = prems
                    .iter()
                    .map(|prem| new_prem(&new_vars, &major, is_dup, lim, prem))
                    .collect();
                next_brs.extend(rest.iter().cloned());
                match self.prv(
                    cons(tactic, tactics.clone()),
                    cons(
                        Choice {
                            ntrl,
                            nbrs: brs.len(),
                            token: Some(token),
                        },
                        choices.clone(),
                    ),
                    next_brs,
                ) {
                    Ok(seq) => return Ok(Some(seq)),
                    Err(error) => catch_backtrack(error, token)?,
                }
                if !may_undo {
                    return Err(backtrack(&choices));
                }
                clear_to(state, ntrl);
            }
            Ok(None)
        };
        if branch.lim < 1 {
            return Err(backtrack(&choices));
        }
        if let Some(closed) = deeper()? {
            return Ok(Step::Done(closed));
        }
        // If no rule closes the branch, the formula becomes a literal.
        let mut lits = vec![formula.clone()];
        lits.extend(branch.lits.iter().cloned());
        let mut next_brs = vec![Branch {
            pairs: vec![Level {
                safe: Vec::new(),
                r#unsafe: others.to_vec(),
            }],
            lits,
            vars: branch.vars.clone(),
            lim: branch.lim,
        }];
        next_brs.extend(rest.iter().cloned());
        Ok(Step::Next {
            tactics,
            choices,
            brs: next_brs,
        })
    }

    fn prv(&self, tactics: Tactics, choices: Choices, branches: Vec<Branch>) -> Res<Seq<Thm>> {
        let _depth = check_stack()?;
        let mut tactics = tactics;
        let mut choices = choices;
        let mut brs = branches;
        loop {
            check_interrupt()?;
            // All branches closed.
            let Some(branch) = brs.first() else {
                return (self.cont)(tactics, choices);
            };
            let Some(head) = branch.pairs.first() else {
                return Err(backtrack(&choices));
            };
            let step = if !head.safe.is_empty() {
                Some(self.safe_step(tactics.clone(), choices.clone(), &brs)?)
            } else if branch.pairs.len() == 1 && !head.r#unsafe.is_empty() {
                Some(self.unsafe_step(tactics.clone(), choices.clone(), &brs)?)
            } else {
                None
            };
            match step {
                Some(Step::Done(result)) => return Ok(result),
                Some(Step::Next {
                    tactics: next_tactics,
                    choices: next_choices,
                    brs: next_brs,
                }) => {
                    tactics = next_tactics;
                    choices = next_choices;
                    brs = next_brs;
                    continue;
                }
                None => {}
            }
            if branch.pairs.len() > 1 {
                // No more safe formulae: transfers the unsafe ones down a level.
                let below = &branch.pairs[1];
                let mut r#unsafe = head.r#unsafe.clone();
                r#unsafe.extend(below.r#unsafe.iter().cloned());
                let mut pairs = vec![Level {
                    safe: below.safe.clone(),
                    r#unsafe,
                }];
                pairs.extend(branch.pairs[2..].iter().cloned());
                let mut next_brs = vec![Branch {
                    pairs,
                    lits: branch.lits.clone(),
                    vars: branch.vars.clone(),
                    lim: branch.lim,
                }];
                next_brs.extend(brs[1..].iter().cloned());
                brs = next_brs;
                continue;
            }
            return Err(backtrack(&choices));
        }
    }
}

pub fn prove(state: &BlastState, initial: Vec<Branch>, cont: Continuation<'_>) -> Res<Seq<Thm>> {
    let claset = &state.context.claset;
    let prover = Prover {
        state,
        cont,
        safe_list: [&claset.safe0, &claset.safep],
        unsafe_list: [&claset.r#unsafe],
    };
    let choices = cons(
        Choice {
            ntrl: state.trail_len(),
            nbrs: initial.len(),
            token: None,
        },
        None,
    );
    prover.prv(None, choices, initial)
}
