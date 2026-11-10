//! Ported from Z3 (src/ast/rewriter/bool_rewriter.cpp), MIT license, through `flat-literals.ts`.
//! The literals of a flattened conjunction or disjunction, without duplicates. Like the
//! expr_fast_mark1 and expr_fast_mark2 of mk_nflat_and_core, it marks the literals and the negated
//! atoms it holds, here with a stamp for each use, so it finds a complementary pair without
//! creating each negation. Its manager owns the one instance that its rewriters share: a list is
//! filled and read before any other starts, so like Z3's ptr_buffer it reuses one array.
//!
//! The manager holds it as `flat_literals`, so `add`, which reads the manager, is the manager's
//! `flat_literals_add`.

use crate::core::ast::{AstManager, Expr};

pub struct FlatLiterals {
    pub list: Vec<Expr>,
    stamp: i32,
    literal_stamps: Vec<i32>,
    negated_atom_stamps: Vec<i32>,
}

impl Default for FlatLiterals {
    fn default() -> Self {
        FlatLiterals::new()
    }
}

impl FlatLiterals {
    pub fn new() -> FlatLiterals {
        FlatLiterals {
            list: Vec::new(),
            stamp: 0,
            literal_stamps: vec![0; 1024],
            negated_atom_stamps: vec![0; 1024],
        }
    }

    /// Starts a new, empty list.
    pub fn clear(&mut self) {
        self.list.clear();
        self.stamp = self.stamp.wrapping_add(1);
    }
}

impl AstManager<'_> {
    /// `flatLiterals.add`: adds a literal, and returns whether its complement is already there. An
    /// expression's arguments are older than it, so their handles are smaller.
    pub fn flat_literals_add(&mut self, literal: Expr) -> bool {
        let is_negated = self.is_not(literal);
        let atom = if is_negated {
            self.get_arg(literal, 0)
        } else {
            literal
        } as usize;
        let flat_literals = &mut self.flat_literals;
        let index = literal as usize;
        if index >= flat_literals.literal_stamps.len() {
            let size = (2 * flat_literals.literal_stamps.len()).max(index + 1);
            flat_literals.literal_stamps.resize(size, 0);
            flat_literals.negated_atom_stamps.resize(size, 0);
        }
        let stamp = flat_literals.stamp;
        if flat_literals.literal_stamps[index] == stamp {
            return false;
        }
        let complement_stamp = if is_negated {
            flat_literals.literal_stamps[atom]
        } else {
            flat_literals.negated_atom_stamps[atom]
        };
        if complement_stamp == stamp {
            return true;
        }
        flat_literals.list.push(literal);
        flat_literals.literal_stamps[index] = stamp;
        if is_negated {
            flat_literals.negated_atom_stamps[atom] = stamp;
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use prove_decide::Limits;

    use crate::core::ast::{AstManager, SORT_BOOL, SmtSymbol};
    use crate::util::rlimit::ResourceLimit;

    #[test]
    fn finds_a_complementary_pair_and_drops_duplicates() {
        let limits = Limits::new(f64::INFINITY, None, None);
        let mut manager = AstManager::new(ResourceLimit::new(&limits));
        let decl = manager.mk_func_decl(SmtSymbol::Name("p".into()), &[], SORT_BOOL, false);
        let atom = manager.mk_app(decl, &[], SORT_BOOL).unwrap();
        let other = manager.mk_fresh_const(None, SORT_BOOL).unwrap();
        let negated = manager.mk_not(atom).unwrap();
        manager.flat_literals.clear();
        assert!(!manager.flat_literals_add(atom));
        assert!(!manager.flat_literals_add(other));
        assert!(!manager.flat_literals_add(atom));
        assert!(manager.flat_literals_add(negated));
        assert_eq!(manager.flat_literals.list, [atom, other]);
        manager.flat_literals.clear();
        assert!(!manager.flat_literals_add(negated));
        assert!(manager.flat_literals_add(atom));
        assert_eq!(manager.flat_literals.list, [negated]);
    }
}
