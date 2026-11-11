//! Ported from Z3 (src/util/ref_vector.h), MIT license, through `ref-vector.ts`. expr_ref_vector: a
//! vector that holds a reference to each expression in it, with -1 for Z3's null pointer.
//!
//! The vector keeps no manager, so each method that counts a reference takes it, and nothing is
//! released on drop: its owner calls `reset` where Z3's destructor would run.

use crate::core::ast::{AstManager, Expr};
use crate::util::error::SmtError;

#[derive(Clone, Debug, Default)]
pub struct RefVector {
    pub items: Vec<Expr>,
}

fn inc_ref(manager: &mut AstManager, expr: Expr) {
    if expr != -1 {
        manager.inc_ref(expr);
    }
}

fn dec_ref(manager: &mut AstManager, expr: Expr) -> Result<(), SmtError> {
    if expr != -1 {
        manager.dec_ref(expr)?;
    }
    Ok(())
}

impl RefVector {
    pub fn new() -> RefVector {
        RefVector::default()
    }

    /// `size`.
    pub fn len(&self) -> usize {
        self.items.len()
    }

    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    pub fn push(&mut self, manager: &mut AstManager, expr: Expr) {
        inc_ref(manager, expr);
        self.items.push(expr);
    }

    /// push_back(expr_ref&&): takes over a reference the caller owns.
    pub fn push_owned(&mut self, expr: Expr) {
        self.items.push(expr);
    }

    pub fn set(
        &mut self,
        manager: &mut AstManager,
        index: usize,
        expr: Expr,
    ) -> Result<(), SmtError> {
        inc_ref(manager, expr);
        dec_ref(manager, self.items[index])?;
        self.items[index] = expr;
        Ok(())
    }

    /// operator=(expr_ref&&): takes over a reference the caller owns.
    pub fn set_owned(
        &mut self,
        manager: &mut AstManager,
        index: usize,
        expr: Expr,
    ) -> Result<(), SmtError> {
        dec_ref(manager, self.items[index])?;
        self.items[index] = expr;
        Ok(())
    }

    pub fn pop(&mut self, manager: &mut AstManager) -> Result<(), SmtError> {
        match self.items.pop() {
            Some(expr) => dec_ref(manager, expr),
            None => Ok(()),
        }
    }

    /// shrink: releases the removed expressions in order.
    pub fn shrink(&mut self, manager: &mut AstManager, size: usize) -> Result<(), SmtError> {
        if size >= self.items.len() {
            return Ok(());
        }
        for expr in self.items.split_off(size) {
            dec_ref(manager, expr)?;
        }
        Ok(())
    }

    /// resize: a larger vector is filled with null pointers.
    pub fn resize(&mut self, manager: &mut AstManager, size: usize) -> Result<(), SmtError> {
        if size < self.items.len() {
            self.shrink(manager, size)?;
        }
        self.items.resize(size.max(self.items.len()), -1);
        Ok(())
    }

    pub fn reset(&mut self, manager: &mut AstManager) -> Result<(), SmtError> {
        self.shrink(manager, 0)
    }
}

#[cfg(test)]
mod tests {
    use prove_decide::Limits;

    use super::RefVector;
    use crate::core::ast::{AstManager, SORT_INT};
    use crate::util::rlimit::ResourceLimit;

    #[test]
    fn holds_a_reference_to_each_item_until_it_is_removed() {
        let limits = Limits::new(f64::INFINITY, None, None);
        let mut manager = AstManager::new(ResourceLimit::new(&limits));
        let first = manager.mk_fresh_const(None, SORT_INT).unwrap();
        let second = manager.mk_fresh_const(None, SORT_INT).unwrap();
        let mut vector = RefVector::new();
        vector.push(&mut manager, first);
        vector.push(&mut manager, second);
        vector.resize(&mut manager, 4).unwrap();
        assert_eq!(vector.items, [first, second, -1, -1]);
        assert_eq!(manager.get_ref_count(first), 1);
        vector.set(&mut manager, 2, first).unwrap();
        assert_eq!(manager.get_ref_count(first), 2);
        vector.shrink(&mut manager, 2).unwrap();
        assert_eq!(manager.get_ref_count(first), 1);
        let asts = manager.get_num_asts();
        vector.set(&mut manager, 1, first).unwrap();
        // second lost its only reference, so it and its declaration are deleted.
        assert_eq!(manager.ids[second as usize], -1);
        assert_eq!(manager.get_num_asts(), asts - 2);
        vector.reset(&mut manager).unwrap();
        assert_eq!(manager.ids[first as usize], -1);
        assert!(vector.is_empty());
    }
}
