//! Ported from Z3 (src/tactic/goal.cpp), MIT license, through `goal.ts`. The formulas that a tactic
//! transforms, kept split into conjuncts. Like Z3's goal, it holds a reference to each formula.
//!
//! The goal keeps no manager, so its methods take it; its owner calls `forms.reset` where Z3's
//! destructor would run.

use std::collections::HashSet;

use crate::core::ast::{AstManager, Expr, OP_AND, OP_NOT, OP_OR, SORT_BOOL};
use crate::core::ref_vector::RefVector;
use crate::util::error::SmtError;

struct Polarized {
    expr: Expr,
    is_positive: bool,
}

#[derive(Debug, Default)]
pub struct Goal {
    pub forms: RefVector,
    pub is_inconsistent: bool,
}

impl Goal {
    pub fn new() -> Goal {
        Goal::default()
    }

    // push_back: a false formula replaces the whole goal.
    fn push_back(&mut self, m: &mut AstManager, form: Expr) -> Result<(), SmtError> {
        if m.is_true(form) {
            return Ok(());
        }
        if m.is_false(form) {
            self.forms.reset(m)?;
            self.is_inconsistent = true;
        }
        self.forms.push(m, form);
        m.limit.check_time()?;
        m.limit.check_size(m.get_num_nodes() + self.forms.len())
    }

    // quick_process: splits conjunctions and negated disjunctions in order. With is_saving_first,
    // the first conjunct is returned instead of added. The formula comes with a reference, and so
    // does the result. The negations it creates are held until it returns.
    fn quick_process(
        &mut self,
        m: &mut AstManager,
        form: Expr,
        is_saving_first: bool,
    ) -> Result<Expr, SmtError> {
        let op = m.get_op(form);
        if op != OP_AND && !(m.is_not(form) && m.get_op(m.get_arg(form, 0)) == OP_OR) {
            if !is_saving_first {
                self.push_back(m, form)?;
            }
            return Ok(form);
        }
        let mut first = form;
        let mut is_saving = is_saving_first;
        let mut created = RefVector::new();
        let mut todo = vec![Polarized {
            expr: form,
            is_positive: true,
        }];
        while !self.is_inconsistent {
            let Some(item) = todo.pop() else {
                break;
            };
            let item_op = m.get_op(item.expr);
            if (item.is_positive && item_op == OP_AND) || (!item.is_positive && item_op == OP_OR) {
                for index in (0..m.get_num_args(item.expr)).rev() {
                    todo.push(Polarized {
                        expr: m.get_arg(item.expr, index),
                        is_positive: item.is_positive,
                    });
                }
            } else if m.is_not(item.expr) {
                todo.push(Polarized {
                    expr: m.get_arg(item.expr, 0),
                    is_positive: !item.is_positive,
                });
            } else {
                let leaf = if item.is_positive {
                    item.expr
                } else {
                    m.mk_app(OP_NOT, &[item.expr], SORT_BOOL)?
                };
                if !item.is_positive {
                    created.push(m, leaf);
                }
                if is_saving {
                    m.inc_ref(leaf);
                    m.dec_ref(first)?;
                    first = leaf;
                    is_saving = false;
                } else {
                    self.push_back(m, leaf)?;
                }
            }
        }
        created.reset(m)?;
        Ok(first)
    }

    /// assert_expr.
    pub fn assert(&mut self, m: &mut AstManager, form: Expr) -> Result<(), SmtError> {
        m.inc_ref(form);
        if !self.is_inconsistent {
            m.inc_ref(form);
            let first = self.quick_process(m, form, false)?;
            m.dec_ref(first)?;
        }
        m.dec_ref(form)
    }

    /// update: the first conjunct replaces the formula and the others are added at the end. When the
    /// first conjunct is false, Z3 adds the whole formula (goal.cpp:312), and this adds false, so the
    /// goal becomes inconsistent.
    pub fn update(&mut self, m: &mut AstManager, index: usize, form: Expr) -> Result<(), SmtError> {
        if self.is_inconsistent {
            return Ok(());
        }
        m.inc_ref(form);
        let first = self.quick_process(m, form, true)?;
        if !self.is_inconsistent {
            if m.is_false(first) {
                self.push_back(m, first)?;
            } else {
                self.forms.set(m, index, first)?;
            }
        }
        m.dec_ref(first)
    }

    // shrink: drops the formulas from size on, the last one first.
    fn shrink(&mut self, m: &mut AstManager, size: usize) -> Result<(), SmtError> {
        while self.forms.len() > size {
            self.forms.pop(m)?;
        }
        Ok(())
    }

    /// elim_true.
    pub fn elim_true(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        let mut kept = 0;
        for (index, form) in self.forms.items.clone().into_iter().enumerate() {
            if m.is_true(form) {
                continue;
            }
            if index != kept {
                self.forms.set(m, kept, form)?;
            }
            kept += 1;
        }
        self.shrink(m, kept)
    }

    /// elim_redundancies: drops true and repeated literals, and finds a complementary pair. The
    /// marks hold the literals until it returns.
    pub fn elim_redundancies(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        if self.is_inconsistent {
            return Ok(());
        }
        let mut negatives = RefVector::new();
        let mut positives = RefVector::new();
        let mut negative_set = HashSet::new();
        let mut positive_set = HashSet::new();
        let mut kept = 0;
        for (index, form) in self.forms.items.clone().into_iter().enumerate() {
            m.limit.check_time()?;
            if m.is_true(form) {
                continue;
            }
            let is_negated = m.is_not(form);
            let atom = if is_negated { m.get_arg(form, 0) } else { form };
            let (same, same_set, other_set) = if is_negated {
                (&mut negatives, &mut negative_set, &positive_set)
            } else {
                (&mut positives, &mut positive_set, &negative_set)
            };
            if !same_set.insert(atom) {
                continue;
            }
            if other_set.contains(&atom) {
                let false_expr = m.false_expr;
                self.push_back(m, false_expr)?;
                break;
            }
            same.push(m, atom);
            if index != kept {
                self.forms.set(m, kept, form)?;
            }
            kept += 1;
        }
        if !self.is_inconsistent {
            self.shrink(m, kept)?;
        }
        positives.reset(m)?;
        negatives.reset(m)
    }
}

#[cfg(test)]
mod tests {
    use prove_decide::Limits;

    use super::Goal;
    use crate::core::ast::{AstManager, Expr, OP_AND, OP_NOT, OP_OR, SORT_BOOL};
    use crate::util::rlimit::ResourceLimit;

    fn mk_manager() -> AstManager {
        let limits = Limits::new(f64::INFINITY, None, None);
        AstManager::new(ResourceLimit::new(&limits))
    }

    fn mk_consts(manager: &mut AstManager, count: usize) -> Vec<Expr> {
        (0..count)
            .map(|_| manager.mk_fresh_const(None, SORT_BOOL).unwrap())
            .collect()
    }

    fn mk_not(manager: &mut AstManager, expr: Expr) -> Expr {
        manager.mk_app(OP_NOT, &[expr], SORT_BOOL).unwrap()
    }

    #[test]
    fn splits_conjunctions_and_negated_disjunctions_in_order() {
        let mut manager = mk_manager();
        let consts = mk_consts(&mut manager, 4);
        let (p, q, r, s) = (consts[0], consts[1], consts[2], consts[3]);
        let or = manager.mk_app(OP_OR, &[q, r], SORT_BOOL).unwrap();
        let not_or = mk_not(&mut manager, or);
        let not_s = mk_not(&mut manager, s);
        let not_not_s = mk_not(&mut manager, not_s);
        let form = manager
            .mk_app(OP_AND, &[p, not_or, not_not_s], SORT_BOOL)
            .unwrap();
        let mut goal = Goal::new();
        goal.assert(&mut manager, form).unwrap();
        let not_q = mk_not(&mut manager, q);
        let not_r = mk_not(&mut manager, r);
        assert_eq!(goal.forms.items, [p, not_q, not_r, s]);
        assert!(!goal.is_inconsistent);
        // The goal holds the negations it created, and released the formula.
        assert_eq!(manager.get_ref_count(not_q), 1);
        assert_eq!(manager.ids[form as usize], -1);
        goal.forms.reset(&mut manager).unwrap();
        assert_eq!(manager.ids[not_q as usize], -1);
    }

    #[test]
    fn drops_true_and_becomes_inconsistent_on_false() {
        let mut manager = mk_manager();
        let p = mk_consts(&mut manager, 1)[0];
        let mut goal = Goal::new();
        let (true_expr, false_expr) = (manager.true_expr, manager.false_expr);
        goal.assert(&mut manager, true_expr).unwrap();
        goal.assert(&mut manager, p).unwrap();
        assert_eq!(goal.forms.items, [p]);
        let form = manager.mk_app(OP_AND, &[p, false_expr], SORT_BOOL).unwrap();
        goal.assert(&mut manager, form).unwrap();
        assert!(goal.is_inconsistent);
        assert_eq!(goal.forms.items, [false_expr]);
        goal.assert(&mut manager, p).unwrap();
        goal.update(&mut manager, 0, p).unwrap();
        assert_eq!(goal.forms.items, [false_expr]);
    }

    #[test]
    fn updates_with_the_first_conjunct_and_appends_the_others() {
        let mut manager = mk_manager();
        let consts = mk_consts(&mut manager, 4);
        let (p, q, r, s) = (consts[0], consts[1], consts[2], consts[3]);
        let mut goal = Goal::new();
        goal.assert(&mut manager, p).unwrap();
        goal.assert(&mut manager, q).unwrap();
        let form = manager.mk_app(OP_AND, &[r, s], SORT_BOOL).unwrap();
        goal.update(&mut manager, 0, form).unwrap();
        assert_eq!(goal.forms.items, [r, q, s]);
        assert_eq!(manager.ids[p as usize], -1);
        // A false first conjunct makes the goal inconsistent.
        let false_expr = manager.false_expr;
        let form = manager.mk_app(OP_AND, &[false_expr, q], SORT_BOOL).unwrap();
        goal.update(&mut manager, 1, form).unwrap();
        assert!(goal.is_inconsistent);
        assert_eq!(goal.forms.items, [false_expr]);
    }

    #[test]
    fn eliminates_true_and_redundant_literals() {
        let mut manager = mk_manager();
        let consts = mk_consts(&mut manager, 2);
        let (p, q) = (consts[0], consts[1]);
        let true_expr = manager.true_expr;
        let mut goal = Goal::new();
        for form in [p, q, p] {
            goal.assert(&mut manager, form).unwrap();
        }
        goal.forms.push(&mut manager, true_expr);
        goal.forms.push(&mut manager, q);
        goal.elim_true(&mut manager).unwrap();
        assert_eq!(goal.forms.items, [p, q, p, q]);
        goal.forms.push(&mut manager, true_expr);
        goal.elim_redundancies(&mut manager).unwrap();
        assert_eq!(goal.forms.items, [p, q]);
        assert!(!goal.is_inconsistent);
        let not_p = mk_not(&mut manager, p);
        goal.assert(&mut manager, not_p).unwrap();
        goal.elim_redundancies(&mut manager).unwrap();
        assert!(goal.is_inconsistent);
        assert_eq!(goal.forms.items, [manager.false_expr]);
    }
}
