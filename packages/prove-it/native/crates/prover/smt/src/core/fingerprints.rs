//! Ported from Z3 (src/smt/fingerprints.cpp), MIT license, see z3-license.txt, through
//! `fingerprints.ts`. The set of quantifier instances already found, so a match on equal terms is
//! not instantiated twice. Scopes undo the insertions.

use crate::core::ast::{AstManager, Expr};
use crate::core::enode::{EnodeId, Enodes};
use crate::util::hash::get_composite_hash;

#[derive(Clone, Debug)]
pub struct FingerprintSet {
    // The quantifier, hash and roots of each fingerprint, in the order of insertion.
    quantifiers: Vec<Expr>,
    hashes: Vec<u32>,
    roots: Vec<Vec<EnodeId>>,
    // Open addressing with linear probing over the indices of the fingerprints, -1 for an empty
    // slot. Scopes remove the newest fingerprints first, and the table grows by inserting them in
    // order, so emptying the slot of a removed fingerprint never cuts the probe of one that remains.
    slots: Vec<i32>,
    scopes: Vec<usize>,
    // The hashes and the roots of the bindings of the instance being inserted.
    binding_hashes: Vec<u32>,
    binding_roots: Vec<EnodeId>,
}

impl Default for FingerprintSet {
    fn default() -> Self {
        FingerprintSet::new()
    }
}

impl FingerprintSet {
    pub fn new() -> FingerprintSet {
        FingerprintSet {
            quantifiers: Vec::new(),
            hashes: Vec::new(),
            roots: Vec::new(),
            slots: vec![-1; 1024],
            scopes: Vec::new(),
            binding_hashes: Vec::new(),
            binding_roots: Vec::new(),
        }
    }

    /// fingerprint_set::insert: the roots of the bindings, which a new fingerprint keeps, or `None`
    /// when the instance is already in the set. The hash comes from the bindings themselves, and
    /// the set is searched with the bindings and then with their roots.
    pub fn insert(
        &mut self,
        m: &AstManager,
        enodes: &Enodes,
        quantifier: Expr,
        bindings: &[EnodeId],
    ) -> Option<Vec<EnodeId>> {
        self.binding_hashes.clear();
        for binding in bindings {
            self.binding_hashes
                .push(m.hashes[enodes.get(*binding).owner as usize]);
        }
        let hash = get_composite_hash(&self.binding_hashes, m.ids[quantifier as usize] as u32);
        self.find(quantifier, hash, bindings)?;
        self.binding_roots.clear();
        for binding in bindings {
            self.binding_roots.push(enodes.get(*binding).root);
        }
        let binding_roots = std::mem::take(&mut self.binding_roots);
        let slot = self.find(quantifier, hash, &binding_roots);
        self.binding_roots = binding_roots;
        let slot = slot?;
        let roots = self.binding_roots.clone();
        self.quantifiers.push(quantifier);
        self.hashes.push(hash);
        self.roots.push(roots.clone());
        if 2 * self.quantifiers.len() <= self.slots.len() {
            self.slots[slot] = (self.quantifiers.len() - 1) as i32;
        } else {
            self.slots = vec![-1; 2 * self.slots.len()];
            for index in 0..self.quantifiers.len() {
                self.place(index);
            }
        }
        Some(roots)
    }

    // The empty slot that ends the probe for the fingerprint, or None when the set has it.
    fn find(&self, quantifier: Expr, hash: u32, args: &[EnodeId]) -> Option<usize> {
        let mask = self.slots.len() - 1;
        let mut slot = hash as usize & mask;
        while self.slots[slot] != -1 {
            let index = self.slots[slot] as usize;
            if self.hashes[index] == hash && self.quantifiers[index] == quantifier {
                let existing = &self.roots[index];
                let mut position = 0;
                while position < args.len() && existing.get(position) == Some(&args[position]) {
                    position += 1;
                }
                if position == args.len() {
                    return None;
                }
            }
            slot = (slot + 1) & mask;
        }
        Some(slot)
    }

    fn place(&mut self, index: usize) {
        let mask = self.slots.len() - 1;
        let mut slot = self.hashes[index] as usize & mask;
        while self.slots[slot] != -1 {
            slot = (slot + 1) & mask;
        }
        self.slots[slot] = index as i32;
    }

    pub fn push(&mut self) {
        self.scopes.push(self.quantifiers.len());
    }

    pub fn pop(&mut self, num_scopes: u32) {
        let limit = self.scopes[self.scopes.len() - num_scopes as usize];
        let mask = self.slots.len() - 1;
        for index in (limit..self.quantifiers.len()).rev() {
            let mut slot = self.hashes[index] as usize & mask;
            while self.slots[slot] != index as i32 {
                slot = (slot + 1) & mask;
            }
            self.slots[slot] = -1;
        }
        self.quantifiers.truncate(limit);
        self.hashes.truncate(limit);
        self.roots.truncate(limit);
        self.scopes
            .truncate(self.scopes.len() - num_scopes as usize);
    }

    pub fn len(&self) -> usize {
        self.quantifiers.len()
    }

    pub fn is_empty(&self) -> bool {
        self.quantifiers.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use prove_decide::Limits;

    use super::FingerprintSet;
    use crate::core::ast::{AstManager, SmtSymbol};
    use crate::core::enode::{EnodeId, Enodes};
    use crate::util::rlimit::ResourceLimit;

    #[test]
    fn finds_instances_by_their_bindings_and_forgets_popped_ones() {
        let limits = Limits::new(f64::INFINITY, None, None);
        let mut m = AstManager::new(ResourceLimit::new(&limits));
        let sort = m.mk_sort("U");
        let mut enodes = Enodes::new();
        let nodes: Vec<EnodeId> = (0..700)
            .map(|index| {
                let decl = m.mk_func_decl(SmtSymbol::Name(format!("c{index}")), &[], sort, false);
                let expr = m.mk_app(decl, &[], sort).unwrap();
                enodes.mk(
                    expr,
                    decl,
                    0,
                    None,
                    None,
                    Vec::new(),
                    0,
                    false,
                    false,
                    false,
                    true,
                    0,
                )
            })
            .collect();
        let quantifier = m.true_expr;
        let mut set = FingerprintSet::new();
        assert_eq!(
            set.insert(&m, &enodes, quantifier, &[nodes[0], nodes[1]]),
            Some(vec![nodes[0], nodes[1]])
        );
        assert_eq!(
            set.insert(&m, &enodes, quantifier, &[nodes[0], nodes[1]]),
            None
        );
        // The hash is the bindings', so equal roots are found only under the same hash: Z3 keeps
        // a second fingerprint with the roots of the first.
        enodes.get_mut(nodes[2]).root = nodes[0];
        assert_eq!(
            set.insert(&m, &enodes, quantifier, &[nodes[2], nodes[1]]),
            Some(vec![nodes[0], nodes[1]])
        );
        assert_eq!(
            set.insert(&m, &enodes, quantifier, &[nodes[2], nodes[1]]),
            None
        );
        set.push();
        // Past half of the 1024 slots, the table doubles.
        for node in &nodes[3..] {
            assert_eq!(
                set.insert(&m, &enodes, quantifier, &[*node]),
                Some(vec![*node])
            );
        }
        assert_eq!(set.len(), 699);
        assert_eq!(set.insert(&m, &enodes, quantifier, &[nodes[500]]), None);
        set.pop(1);
        assert_eq!(set.len(), 2);
        assert_eq!(
            set.insert(&m, &enodes, quantifier, &[nodes[500]]),
            Some(vec![nodes[500]])
        );
    }
}
