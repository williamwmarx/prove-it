//! Ported from Isabelle2025's Pure/tactic.ML, the basic resolution tactics. Copyright (c)
//! 1986-2025 University of Cambridge, Technische Universitaet Muenchen, and contributors, see
//! LICENSE.
//!
//! (`pure/tactic.ts`.) The tactics check for an interrupt where the TypeScript does, against the
//! limits installed for the thread.

use std::rc::Rc;

use crate::error::Res;

use super::drule::make_elim;
use super::interrupt::check_interrupt;
use super::logic::{strip_assums_concl, strip_assums_hyp};
use super::net::{Net, insert_term_net, unify_term_net};
use super::tactical::{GoalTactic, Tactic, all_tac, prim_seq, primitive, subgoal};
use super::thm::{
    BiresRule, ComposeFlags, ComposeRule, Thm, assumption, bicompose, biresolution, concl_of,
    eq_assumption, flexflex_rule, major_prem_of, nprems, rotate_rule,
};

pub fn assume_tac() -> GoalTactic {
    Rc::new(|index| {
        prim_seq(move |state| {
            check_interrupt()?;
            assumption(index, &state)
        })
    })
}

pub fn eq_assume_tac() -> GoalTactic {
    Rc::new(|index| primitive(move |state| eq_assumption(index, &state)))
}

pub fn compose_tac(is_elim: bool, rule: Thm, subgoals: usize) -> GoalTactic {
    Rc::new(move |index| {
        let rule = rule.clone();
        prim_seq(move |state| {
            bicompose(
                ComposeFlags {
                    flatten: true,
                    is_match: false,
                    incremented: false,
                },
                ComposeRule {
                    is_elim,
                    rule: rule.clone(),
                    subgoals,
                },
                index,
                &state,
            )
        })
    })
}

fn biresolve_tac(rules: Vec<BiresRule>) -> GoalTactic {
    let rules: Rc<[BiresRule]> = rules.into();
    Rc::new(move |index| {
        let rules = rules.clone();
        prim_seq(move |state| {
            check_interrupt()?;
            biresolution(false, &rules, index, &state)
        })
    })
}

fn brules(is_elim: bool, rules: &[Thm]) -> Vec<BiresRule> {
    rules
        .iter()
        .map(|rule| BiresRule {
            is_elim,
            rule: rule.clone(),
        })
        .collect()
}

pub fn resolve_tac(rules: &[Thm]) -> GoalTactic {
    biresolve_tac(brules(false, rules))
}

pub fn eresolve_tac(rules: &[Thm]) -> GoalTactic {
    biresolve_tac(brules(true, rules))
}

/// Raises where make_elim does, when the tactic is built.
pub fn dresolve_tac(rules: &[Thm]) -> Res<GoalTactic> {
    Ok(eresolve_tac(
        &rules.iter().map(make_elim).collect::<Res<Vec<_>>>()?,
    ))
}

fn bimatch_tac(rules: Vec<BiresRule>) -> GoalTactic {
    let rules: Rc<[BiresRule]> = rules.into();
    Rc::new(move |index| {
        let rules = rules.clone();
        prim_seq(move |state| {
            check_interrupt()?;
            biresolution(true, &rules, index, &state)
        })
    })
}

pub fn match_tac(rules: &[Thm]) -> GoalTactic {
    bimatch_tac(brules(false, rules))
}

pub fn ematch_tac(rules: &[Thm]) -> GoalTactic {
    bimatch_tac(brules(true, rules))
}

pub fn flexflex_tac() -> Tactic {
    prim_seq(|state| flexflex_rule(&state))
}

/// What the TypeScript's `{ isElim: boolean; rule: Thm }` bound asks of the items of a net.
pub trait Brl {
    fn is_elim(&self) -> bool;
    fn rule(&self) -> &Thm;
}

impl Brl for BiresRule {
    fn is_elim(&self) -> bool {
        self.is_elim
    }
    fn rule(&self) -> &Thm {
        &self.rule
    }
}

#[derive(Clone)]
pub struct TaggedRule {
    pub tag: i64,
    pub is_elim: bool,
    pub rule: Thm,
}

impl Brl for TaggedRule {
    fn is_elim(&self) -> bool {
        self.is_elim
    }
    fn rule(&self) -> &Thm {
        &self.rule
    }
}

pub struct NetPair<Tagged> {
    pub intro: Net<Tagged>,
    pub elim: Net<Tagged>,
}

impl<Tagged> Clone for NetPair<Tagged> {
    fn clone(&self) -> Self {
        NetPair {
            intro: self.intro.clone(),
            elim: self.elim.clone(),
        }
    }
}

/// Tactic.insert_tagged_brl
pub fn insert_tagged_brl<Tagged: Brl + Clone>(
    tagged: Tagged,
    netpair: &NetPair<Tagged>,
) -> Res<NetPair<Tagged>> {
    Ok(if tagged.is_elim() {
        NetPair {
            intro: netpair.intro.clone(),
            elim: insert_term_net(&major_prem_of(tagged.rule())?, tagged, &netpair.elim),
        }
    } else {
        NetPair {
            intro: insert_term_net(&concl_of(tagged.rule()).clone(), tagged, &netpair.intro),
            elim: netpair.elim.clone(),
        }
    })
}

/// Library.order_list: by tag, dropping all but the last item with each tag. The lists are short,
/// so this sorts them by insertion, which keeps items with equal tags in order as Isabelle's sort.
pub fn order_list<Item: Clone>(items: &[(i64, Item)]) -> Vec<Item> {
    let mut sorted = items.to_vec();
    for index in 1..sorted.len() {
        let entry = sorted[index].clone();
        let mut position = index;
        while position > 0 && sorted[position - 1].0 > entry.0 {
            sorted[position] = sorted[position - 1].clone();
            position -= 1;
        }
        sorted[position] = entry;
    }
    let mut result = Vec::new();
    for index in 0..sorted.len() {
        if index + 1 == sorted.len() || sorted[index + 1].0 != sorted[index].0 {
            result.push(sorted[index].1.clone());
        }
    }
    result
}

/// Tactic.biresolution_from_nets_tac
pub fn biresolution_from_nets_tac<Tagged: Brl + Clone + 'static>(
    order: impl Fn(Vec<Tagged>) -> Vec<BiresRule> + 'static,
    is_match: bool,
    netpair: NetPair<Tagged>,
) -> GoalTactic {
    let order = Rc::new(order);
    subgoal(move |goal, index| {
        let hyps = strip_assums_hyp(goal);
        let concl = strip_assums_concl(goal);
        let mut rules = unify_term_net(&netpair.intro, concl);
        for hyp in &hyps {
            rules.extend(unify_term_net(&netpair.elim, hyp));
        }
        let order = order.clone();
        Ok(prim_seq(move |state| {
            check_interrupt()?;
            biresolution(is_match, &order(rules.clone()), index, &state)
        }))
    })
}

pub fn order_tagged(rules: Vec<TaggedRule>) -> Vec<BiresRule> {
    order_list(
        &rules
            .into_iter()
            .map(|rule| {
                (
                    rule.tag,
                    BiresRule {
                        is_elim: rule.is_elim,
                        rule: rule.rule,
                    },
                )
            })
            .collect::<Vec<_>>(),
    )
}

pub fn biresolve_from_nets_tac(netpair: NetPair<TaggedRule>) -> GoalTactic {
    biresolution_from_nets_tac(order_tagged, false, netpair)
}

pub fn bimatch_from_nets_tac(netpair: NetPair<TaggedRule>) -> GoalTactic {
    biresolution_from_nets_tac(order_tagged, true, netpair)
}

/// The number of new subgoals of a rule.
pub fn subgoals_of_brl(brule: &impl Brl) -> i32 {
    let count = nprems(brule.rule()) as i32;
    if brule.is_elim() { count - 1 } else { count }
}

pub fn rotate_tac(count: i32) -> GoalTactic {
    Rc::new(move |index| {
        if count == 0 {
            all_tac()
        } else {
            primitive(move |state| rotate_rule(count, index, &state))
        }
    })
}

#[cfg(test)]
mod tests {
    use prove_decide::Limits;

    use super::*;
    use crate::pure::goal::{prefer_goal, select_goal};
    use crate::pure::interrupt::with_limits;
    use crate::pure::net::empty_net;
    use crate::pure::search::{best_first, deepen};
    use crate::pure::tactical::{
        all_goals, all_tac, append_goal, append_tac, changed, changed_prop, depth_solve, determ,
        every, first, first_goal, first_goal_tac, has_fewer_prems, no_tac, or_else, or_else_goal,
        repeat_all_new, repeat_determ, repeat_determ_n, repeat_determ1, then_all_new, then_else,
        then_goal, then_tac, try_tac,
    };
    use crate::pure::term::size_of_term;
    use crate::pure::testing::{check_problems, parse_term};
    use crate::pure::thm::tests::{many, rule_of};
    use crate::pure::thm::trivial;

    struct Rule {
        tag: i64,
        kind: String,
        thm: Thm,
    }

    fn size_of_thm(thm: &Thm) -> usize {
        thm.tpairs
            .iter()
            .fold(size_of_term(&thm.prop), |size, pair| {
                size + 2 + size_of_term(&pair.0) + size_of_term(&pair.1)
            })
    }

    /// Builds the tactic a tactic expression of the test file names: the same grammar as the
    /// script's (`(then T T)`, `(at N G)`, `rtac`, …).
    struct Builder<'a> {
        tokens: Vec<String>,
        position: usize,
        rules: &'a [Rule],
        netpair: NetPair<TaggedRule>,
    }

    impl Builder<'_> {
        fn next(&mut self) -> String {
            self.position += 1;
            self.tokens[self.position - 1].clone()
        }

        fn number<T: std::str::FromStr>(&mut self) -> T
        where
            T::Err: std::fmt::Debug,
        {
            self.next().parse().unwrap()
        }

        fn close(&mut self) {
            assert_eq!(self.next(), ")");
        }

        fn of(&self, kind: &str) -> Vec<Thm> {
            self.rules
                .iter()
                .filter(|rule| rule.kind == kind)
                .map(|rule| rule.thm.clone())
                .collect()
        }

        fn list<Item>(&mut self, parse: fn(&mut Self) -> Res<Item>) -> Res<Vec<Item>> {
            let mut items = Vec::new();
            while self.tokens[self.position] != ")" {
                items.push(parse(self)?);
            }
            Ok(items)
        }

        fn tactic(&mut self) -> Res<Tactic> {
            let token = self.next();
            match token.as_str() {
                "all" => return Ok(all_tac()),
                "no" => return Ok(no_tac()),
                "flex" => return Ok(flexflex_tac()),
                "(" => {}
                _ => panic!("bad tactic {token}"),
            }
            let head = self.next();
            let result = match head.as_str() {
                "then" => then_tac(self.tactic()?, self.tactic()?),
                "orelse" => or_else(self.tactic()?, self.tactic()?),
                "append" => append_tac(self.tactic()?, self.tactic()?),
                "thenelse" => then_else(self.tactic()?, self.tactic()?, self.tactic()?),
                "determ" => determ(self.tactic()?),
                "try" => try_tac(self.tactic()?),
                "every" => every(self.list(Self::tactic)?),
                "first" => first(self.list(Self::tactic)?),
                "repeat" => repeat_determ(self.tactic()?),
                "repeat1" => repeat_determ1(self.tactic()?),
                "repeatn" => repeat_determ_n(self.number(), self.tactic()?),
                "changed" => changed(self.tactic()?),
                "changedprop" => changed_prop(self.tactic()?),
                "allgoals" => all_goals(self.goal()?),
                "firstgoal" => first_goal_tac(self.goal()?),
                "depthsolve" => depth_solve(self.tactic()?),
                "bestfirst" => best_first(has_fewer_prems(1), size_of_thm, self.tactic()?),
                "at" => {
                    let index = self.number();
                    self.goal()?(index)
                }
                _ => panic!("bad tactic {head}"),
            };
            self.close();
            Ok(result)
        }

        fn goal(&mut self) -> Res<GoalTactic> {
            let token = self.next();
            match token.as_str() {
                "rtac" => return Ok(resolve_tac(&self.of("i"))),
                "etac" => return Ok(eresolve_tac(&self.of("e"))),
                "dtac" => return dresolve_tac(&self.of("d")),
                "mtac" => return Ok(match_tac(&self.of("i"))),
                "ematch" => return Ok(ematch_tac(&self.of("e"))),
                "atac" => return Ok(assume_tac()),
                "eqatac" => return Ok(eq_assume_tac()),
                "net" => return Ok(biresolve_from_nets_tac(self.netpair.clone())),
                "bimatchnet" => return Ok(bimatch_from_nets_tac(self.netpair.clone())),
                "(" => {}
                _ => panic!("bad goal tactic {token}"),
            }
            let head = self.next();
            let result = match head.as_str() {
                "rtacn" => {
                    let index: usize = self.number();
                    resolve_tac(&[self.rules[index].thm.clone()])
                }
                "compose" | "ecompose" => {
                    let index: usize = self.number();
                    let subgoals = self.number();
                    compose_tac(head == "ecompose", self.rules[index].thm.clone(), subgoals)
                }
                "rot" => rotate_tac(self.number()),
                "thenG" => then_goal(self.goal()?, self.goal()?),
                "orelseG" => or_else_goal(self.goal()?, self.goal()?),
                "appendG" => append_goal(self.goal()?, self.goal()?),
                "firstG" => first_goal(self.list(Self::goal)?),
                "thenallnew" => then_all_new(self.goal()?, self.goal()?),
                "repeatallnew" => repeat_all_new(self.goal()?),
                "select" => select_goal(self.tactic()?),
                "prefer" => prefer_goal(self.tactic()?),
                "deepen" => {
                    let increment = self.number();
                    let limit = self.number();
                    let start = self.number();
                    let inner = self.goal()?;
                    deepen(
                        increment,
                        limit,
                        Rc::new(move |depth| {
                            let inner = inner.clone();
                            Rc::new(move |index| repeat_determ_n(depth, inner(index)))
                        }),
                        start,
                    )
                }
                _ => panic!("bad goal tactic {head}"),
            };
            self.close();
            Ok(result)
        }
    }

    fn build_tactic(rules: &[Rule], text: &str) -> Res<Tactic> {
        let netpair = rules
            .iter()
            .filter(|rule| rule.kind != "d")
            .rev()
            .try_fold(
                NetPair {
                    intro: empty_net(),
                    elim: empty_net(),
                },
                |result, rule| {
                    insert_tagged_brl(
                        TaggedRule {
                            tag: rule.tag,
                            is_elim: rule.kind == "e",
                            rule: rule.thm.clone(),
                        },
                        &result,
                    )
                },
            )?;
        let mut builder = Builder {
            tokens: text
                .replace('(', " ( ")
                .replace(')', " ) ")
                .split(' ')
                .filter(|token| !token.is_empty())
                .map(String::from)
                .collect(),
            position: 0,
            rules,
            netpair,
        };
        let tactic = builder.tactic()?;
        assert_eq!(builder.position, builder.tokens.len(), "trailing tokens");
        Ok(tactic)
    }

    fn tactic_problem(fields: &[&str]) -> Vec<String> {
        let count: usize = fields[0].parse().unwrap();
        let limits = Limits::new(f64::INFINITY, Some(fields[1].parse().unwrap()), None);
        let rules: Vec<Rule> = fields[4..]
            .iter()
            .map(|field| {
                let parts: Vec<&str> = field.split('|').collect();
                Rule {
                    tag: parts[0].parse().unwrap(),
                    kind: parts[1].into(),
                    thm: rule_of(parts[2]),
                }
            })
            .collect();
        let mut lines = Vec::new();
        with_limits(&limits, || {
            many(&mut lines, "results", count, || {
                build_tactic(&rules, fields[2])?(trivial(&parse_term(fields[3]))?)
            });
        });
        lines.push(format!("steps {}", limits.steps()));
        lines
    }

    // The expectations are recorded from tactic.ts, tactical.ts, goal.ts and search.ts.
    #[test]
    fn tactics_match_the_typescript() {
        check_problems(
            include_str!("../../testdata/kernel/tactic.txt"),
            |kind, fields| match kind {
                "tactic" => tactic_problem(fields),
                _ => panic!("unknown problem {kind}"),
            },
        );
    }

    #[test]
    fn orders_tagged_items_keeping_the_last_of_each_tag() {
        assert_eq!(
            order_list(&[(3, 'a'), (1, 'b'), (3, 'c'), (2, 'd'), (1, 'e')]),
            vec!['e', 'd', 'c']
        );
    }
}
