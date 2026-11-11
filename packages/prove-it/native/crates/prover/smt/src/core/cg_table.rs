//! Ported from Z3 (src/smt/smt_cg_table.h, src/smt/smt_cg_table.cpp), MIT license, see
//! z3-license.txt, through `cg-table.ts`. The congruence table maps a declaration and the roots of
//! its arguments to the congruence root, so f(a) and f(b) meet when a and b are merged. Equalities
//! are commutative.

use super::enode::{CONGRUENCE_JUSTIFICATIONS, EnodeId, Enodes, EqJustification};
use crate::core::ast::{Decl, Expr};

const GOLDEN: i32 = 0x9e37_79b1_u32 as i32;
const MIX: i32 = 0x85eb_ca6b_u32 as i32;

/// The hash of an equality between the classes of first and second, in either order.
fn get_eq_hash(decl: Decl, first: Expr, second: Expr) -> i32 {
    let (lower, upper) = if first < second {
        (first, second)
    } else {
        (second, first)
    };
    decl.wrapping_mul(GOLDEN)
        .wrapping_add(lower)
        .wrapping_mul(MIX)
        .wrapping_add(upper)
}

fn get_root_owner(enodes: &Enodes, node: EnodeId) -> Expr {
    enodes.get(enodes.get(node).root).owner
}

fn get_hash(enodes: &Enodes, decl: Decl, args: &[EnodeId], is_eq: bool) -> i32 {
    if is_eq {
        return get_eq_hash(
            decl,
            get_root_owner(enodes, args[0]),
            get_root_owner(enodes, args[1]),
        );
    }
    let mut hash = decl;
    for arg in args {
        hash = hash
            .wrapping_mul(GOLDEN)
            .wrapping_add(get_root_owner(enodes, *arg));
    }
    hash
}

fn get_node_hash(enodes: &Enodes, node: EnodeId) -> i32 {
    let enode = enodes.get(node);
    if enode.is_eq() {
        return get_eq_hash(
            enode.decl,
            get_root_owner(enodes, enode.get_arg(0)),
            get_root_owner(enodes, enode.get_arg(1)),
        );
    }
    let mut hash = enode.decl;
    for index in 0..enode.num_args() {
        hash = hash
            .wrapping_mul(GOLDEN)
            .wrapping_add(get_root_owner(enodes, enode.get_arg(index)));
    }
    hash
}

/// Whether node is decl applied to nodes equal to first and second, in either order for an
/// equality.
fn is_pair_congruent_to(
    enodes: &Enodes,
    node: EnodeId,
    first: EnodeId,
    second: EnodeId,
    is_eq: bool,
) -> bool {
    let node_first = enodes.get_arg_root(node, 0);
    let node_second = enodes.get_arg_root(node, 1);
    let first_root = enodes.get(first).root;
    let second_root = enodes.get(second).root;
    (node_first == first_root && node_second == second_root)
        || (is_eq && node_first == second_root && node_second == first_root)
}

fn is_congruent_to(
    enodes: &Enodes,
    node: EnodeId,
    decl: Decl,
    args: &[EnodeId],
    is_eq: bool,
) -> bool {
    let enode = enodes.get(node);
    if enode.decl != decl || enode.num_args() as usize != args.len() {
        return false;
    }
    if is_eq {
        return is_pair_congruent_to(enodes, node, args[0], args[1], true);
    }
    for (index, arg) in args.iter().enumerate() {
        if enodes.get_arg_root(node, index as u32) != enodes.get(*arg).root {
            return false;
        }
    }
    true
}

/// congruent: whether two nodes apply one declaration to equal arguments. Only equalities are
/// commutative.
pub fn is_congruent(enodes: &Enodes, first: EnodeId, second: EnodeId) -> bool {
    let first_node = enodes.get(first);
    let second_node = enodes.get(second);
    if first_node.decl != second_node.decl || first_node.num_args() != second_node.num_args() {
        return false;
    }
    if first_node.num_args() == 2 {
        return is_pair_congruent_to(
            enodes,
            first,
            second_node.get_arg(0),
            second_node.get_arg(1),
            first_node.is_eq(),
        );
    }
    for index in 0..first_node.num_args() {
        if enodes.get_arg_root(first, index) != enodes.get_arg_root(second, index) {
            return false;
        }
    }
    true
}

/// The justification of a node's equality with the congruent node that the table returned for it.
pub fn get_congruence_justification(
    enodes: &Enodes,
    node: EnodeId,
    congruent: EnodeId,
) -> EqJustification {
    let is_commutative = enodes.get(node).is_eq()
        && enodes.get_arg_root(congruent, 0) != enodes.get_arg_root(node, 0);
    CONGRUENCE_JUSTIFICATIONS[usize::from(is_commutative)]
}

const EMPTY: u8 = 0;
const FULL: u8 = 1;
const DELETED: u8 = 2;

/// Open addressing with linear probing. An erased node leaves a deleted slot, which probes pass
/// over, until the table is rebuilt.
#[derive(Clone, Debug)]
pub struct CgTable {
    nodes: Vec<Option<EnodeId>>,
    hashes: Vec<i32>,
    states: Vec<u8>,
    num_full: usize,
    num_deleted: usize,
}

impl Default for CgTable {
    fn default() -> Self {
        CgTable {
            nodes: vec![None; 1024],
            hashes: vec![0; 1024],
            states: vec![EMPTY; 1024],
            num_full: 0,
            num_deleted: 0,
        }
    }
}

impl CgTable {
    pub fn new() -> Self {
        Self::default()
    }

    fn get_mask(&self) -> i32 {
        self.states.len() as i32 - 1
    }

    fn find(
        &self,
        enodes: &Enodes,
        decl: Decl,
        args: &[EnodeId],
        is_eq: bool,
        hash: i32,
    ) -> Option<EnodeId> {
        let mask = self.get_mask();
        let mut slot = (hash & mask) as usize;
        while self.states[slot] != EMPTY {
            if let Some(node) = self.nodes[slot]
                && self.states[slot] == FULL
                && self.hashes[slot] == hash
                && is_congruent_to(enodes, node, decl, args, is_eq)
            {
                return Some(node);
            }
            slot = ((slot as i32 + 1) & mask) as usize;
        }
        None
    }

    fn find_node(&self, enodes: &Enodes, node: EnodeId, hash: i32) -> Option<EnodeId> {
        let mask = self.get_mask();
        let mut slot = (hash & mask) as usize;
        while self.states[slot] != EMPTY {
            if let Some(candidate) = self.nodes[slot]
                && self.states[slot] == FULL
                && self.hashes[slot] == hash
                && is_congruent(enodes, candidate, node)
            {
                return Some(candidate);
            }
            slot = ((slot as i32 + 1) & mask) as usize;
        }
        None
    }

    /// Returns the congruence root for node, which is node itself when it is new.
    pub fn insert(&mut self, enodes: &Enodes, node: EnodeId) -> EnodeId {
        let hash = get_node_hash(enodes, node);
        if let Some(existing) = self.find_node(enodes, node, hash) {
            return existing;
        }
        if 2 * (self.num_full + self.num_deleted + 1) > self.states.len() {
            self.rebuild();
        }
        let mask = self.get_mask();
        let mut slot = (hash & mask) as usize;
        while self.states[slot] == FULL {
            slot = ((slot as i32 + 1) & mask) as usize;
        }
        if self.states[slot] == DELETED {
            self.num_deleted -= 1;
        }
        self.place(slot, node, hash);
        node
    }

    fn place(&mut self, slot: usize, node: EnodeId, hash: i32) {
        self.nodes[slot] = Some(node);
        self.hashes[slot] = hash;
        self.states[slot] = FULL;
        self.num_full += 1;
    }

    /// Drops the deleted slots, and doubles the table when it is more than a quarter full.
    fn rebuild(&mut self) {
        let size = if 4 * self.num_full > self.states.len() {
            2 * self.states.len()
        } else {
            self.states.len()
        };
        let nodes = std::mem::replace(&mut self.nodes, vec![None; size]);
        let hashes = std::mem::replace(&mut self.hashes, vec![0; size]);
        let states = std::mem::replace(&mut self.states, vec![EMPTY; size]);
        self.num_full = 0;
        self.num_deleted = 0;
        let mask = size as i32 - 1;
        for index in 0..states.len() {
            let Some(node) = nodes[index] else { continue };
            if states[index] != FULL {
                continue;
            }
            let mut slot = (hashes[index] & mask) as usize;
            while self.states[slot] == FULL {
                slot = ((slot as i32 + 1) & mask) as usize;
            }
            self.place(slot, node, hashes[index]);
        }
    }

    /// get_enode_eq_to: the congruence root of decl applied to nodes equal to args, if any.
    pub fn find_for(
        &self,
        enodes: &Enodes,
        decl: Decl,
        args: &[EnodeId],
        is_eq: bool,
    ) -> Option<EnodeId> {
        self.find(
            enodes,
            decl,
            args,
            is_eq,
            get_hash(enodes, decl, args, is_eq),
        )
    }

    /// The congruence root of a node congruent to node.
    pub fn find_congruent(&self, enodes: &Enodes, node: EnodeId) -> Option<EnodeId> {
        self.find_node(enodes, node, get_node_hash(enodes, node))
    }

    fn get_slot(&self, enodes: &Enodes, node: EnodeId) -> Option<usize> {
        let mask = self.get_mask();
        let mut slot = (get_node_hash(enodes, node) & mask) as usize;
        while self.states[slot] != EMPTY {
            if self.nodes[slot] == Some(node) {
                return Some(slot);
            }
            slot = ((slot as i32 + 1) & mask) as usize;
        }
        None
    }

    pub fn erase(&mut self, enodes: &Enodes, node: EnodeId) {
        let Some(slot) = self.get_slot(enodes, node) else {
            return;
        };
        self.nodes[slot] = None;
        self.states[slot] = DELETED;
        self.num_full -= 1;
        self.num_deleted += 1;
    }

    pub fn contains(&self, enodes: &Enodes, node: EnodeId) -> bool {
        self.get_slot(enodes, node).is_some()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const F: Decl = 1000;
    const EQ: Decl = 1001;

    fn mk_leaf(enodes: &mut Enodes, owner: Expr) -> EnodeId {
        enodes.mk(
            owner,
            owner,
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
    }

    fn mk_app(enodes: &mut Enodes, owner: Expr, decl: Decl, args: &[EnodeId]) -> EnodeId {
        enodes.mk(
            owner,
            decl,
            args.len() as u32,
            args.first().copied(),
            args.get(1).copied(),
            args.iter().skip(2).copied().collect(),
            0,
            decl == EQ,
            decl == EQ,
            false,
            true,
            0,
        )
    }

    // Merges the class of node into the class of root, as far as the table reads it.
    fn set_root(enodes: &mut Enodes, node: EnodeId, root: EnodeId) {
        enodes.get_mut(node).root = root;
    }

    #[test]
    fn meets_applications_whose_arguments_are_merged() {
        let mut enodes = Enodes::new();
        let a = mk_leaf(&mut enodes, 1);
        let b = mk_leaf(&mut enodes, 2);
        let fa = mk_app(&mut enodes, 3, F, &[a]);
        let fb = mk_app(&mut enodes, 4, F, &[b]);
        let mut table = CgTable::new();
        assert_eq!(table.insert(&enodes, fa), fa);
        assert_eq!(table.insert(&enodes, fb), fb);
        assert!(table.contains(&enodes, fa) && table.contains(&enodes, fb));
        assert_eq!(table.find_for(&enodes, F, &[b], false), Some(fb));
        // Merging b into a moves f(b)'s hash, so the context erases f(b) first and reinserts it.
        table.erase(&enodes, fb);
        assert!(!table.contains(&enodes, fb));
        set_root(&mut enodes, b, a);
        assert!(is_congruent(&enodes, fa, fb));
        assert_eq!(table.find_congruent(&enodes, fb), Some(fa));
        assert_eq!(table.insert(&enodes, fb), fa);
        assert_eq!(table.find_for(&enodes, F, &[b], false), Some(fa));
        assert_eq!(
            get_congruence_justification(&enodes, fb, fa),
            CONGRUENCE_JUSTIFICATIONS[0]
        );
    }

    #[test]
    fn equalities_are_commutative() {
        let mut enodes = Enodes::new();
        let a = mk_leaf(&mut enodes, 1);
        let b = mk_leaf(&mut enodes, 2);
        let ab = mk_app(&mut enodes, 3, EQ, &[a, b]);
        let ba = mk_app(&mut enodes, 4, EQ, &[b, a]);
        let fab = mk_app(&mut enodes, 5, F, &[a, b]);
        let fba = mk_app(&mut enodes, 6, F, &[b, a]);
        let mut table = CgTable::new();
        assert_eq!(table.insert(&enodes, ab), ab);
        assert_eq!(table.insert(&enodes, ba), ab);
        assert_eq!(
            get_congruence_justification(&enodes, ba, ab),
            CONGRUENCE_JUSTIFICATIONS[1]
        );
        assert_eq!(table.find_for(&enodes, EQ, &[b, a], true), Some(ab));
        assert_eq!(table.insert(&enodes, fab), fab);
        assert_eq!(table.insert(&enodes, fba), fba);
        assert!(!is_congruent(&enodes, fab, fba));
    }

    #[test]
    fn keeps_its_nodes_across_rebuilds() {
        let mut enodes = Enodes::new();
        let leaves: Vec<EnodeId> = (0..1500).map(|owner| mk_leaf(&mut enodes, owner)).collect();
        let apps: Vec<EnodeId> = leaves
            .iter()
            .enumerate()
            .map(|(index, leaf)| mk_app(&mut enodes, 2000 + index as i32, F, &[*leaf]))
            .collect();
        let mut table = CgTable::new();
        for app in &apps {
            assert_eq!(table.insert(&enodes, *app), *app);
        }
        for app in apps.iter().step_by(2) {
            table.erase(&enodes, *app);
        }
        for (index, app) in apps.iter().enumerate() {
            assert_eq!(table.contains(&enodes, *app), index % 2 == 1);
            let found = table.find_for(&enodes, F, &[leaves[index]], false);
            assert_eq!(found, (index % 2 == 1).then_some(*app));
        }
        for app in apps.iter().step_by(2) {
            assert_eq!(table.insert(&enodes, *app), *app);
        }
        assert!(apps.iter().all(|app| table.contains(&enodes, *app)));
    }
}
