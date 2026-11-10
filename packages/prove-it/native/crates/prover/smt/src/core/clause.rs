//! Ported from Z3 (src/smt/smt_clause.h, src/smt/smt_b_justification.h,
//! src/util/small_object_allocator.cpp), MIT license, see z3-license.txt, through `clause.ts`.
//! Disjunctions of literals, and the reasons a literal is assigned.

use super::enode::JustificationId;
use super::literal::Literal;
use crate::util::error::SmtError;

/// A clause is the offset of its block in the `ClauseStore`.
pub type Clause = u32;

pub const CLS_AUX: u32 = 0;
pub const CLS_LEARNED: u32 = 1;
pub const CLS_TH_AXIOM: u32 = 2;
pub const CLS_TH_LEMMA: u32 = 3;

/// b_justification: a clause, a binary clause, a theory justification, an axiom, or a decision
/// (the TypeScript's `null`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BJustification {
    Clause(Clause),
    /// `BinJustification`: b_justification(l) of BIN_CLAUSE kind, a binary clause propagated
    /// because the literal l became true.
    BinClause(Literal),
    Justification(JustificationId),
    Axiom,
    Decision,
}

/// The deletion handlers a clause keeps, the closures the TypeScript passes to `mkClause`, with
/// what they capture.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DelEh {
    /// dyn-ack.ts's `() => this.instantiated.delete(pair.key)`: the pair of applications whose
    /// congruence lemma the clause is, so that it can be instantiated again.
    DynAckInstantiated { first: u32, second: u32 },
}

/// The second header word packs Z3's bit fields: m_capacity:24, m_kind:2, m_reinit,
/// m_reinternalize_atoms, m_has_atoms, m_has_del_eh, m_has_justification and m_deleted.
const CAPACITY_MASK: u32 = 0xff_ffff;
const KIND_SHIFT: u32 = 24;
const IS_REINIT: u32 = 1 << 26;
const IS_REINTERNALIZE_ATOMS: u32 = 1 << 27;
const HAS_ATOMS: u32 = 1 << 28;
const HAS_DEL_EH: u32 = 1 << 29;
const HAS_JUSTIFICATION: u32 = 1 << 30;
const IS_DELETED: u32 = 1 << 31;
/// The words before the literals: m_num_literals and the bit fields.
pub const HEADER_SIZE: u32 = 2;
/// An atom word of a clause whose atoms were released.
const NO_ATOM: i32 = -1;

fn is_lemma_kind(kind: u32) -> bool {
    kind == CLS_LEARNED || kind == CLS_TH_LEMMA
}

/// mk_slot: the value in the last freed slot, or in a new one.
fn mk_slot<T>(values: &mut Vec<Option<T>>, free_slots: &mut Vec<i32>, value: T) -> i32 {
    let slot = free_slots.pop().unwrap_or(values.len() as i32);
    if slot as usize >= values.len() {
        values.resize_with(slot as usize + 1, || None);
    }
    values[slot as usize] = Some(value);
    slot
}

/// The clauses live in one `Vec<i32>`, and a clause is the offset of its block, as a clause is the
/// address of its memory in Z3. A block holds the header, the literals, then the activity of a
/// lemma, the slots of the deletion handler and the justification, and the atoms with their signs,
/// each present only when used. Like small_object_allocator, a freed block goes on the free list of
/// its size for the next clause of that size, and the array never shrinks. A freed block keeps the
/// next free block in its first word and 0 in its second, which no clause has.
#[derive(Clone, Debug)]
pub struct ClauseStore {
    /// Literal i of clause c is `data[c + 2 + i]`.
    pub data: Vec<i32>,
    top: usize,
    /// The first free block of each size, or -1.
    free_lists: Vec<i32>,
    /// The deletion handlers and justifications, which a block refers to by slot.
    del_ehs: Vec<Option<DelEh>>,
    free_del_eh_slots: Vec<i32>,
    justifications: Vec<Option<JustificationId>>,
    free_justification_slots: Vec<i32>,
}

impl Default for ClauseStore {
    fn default() -> Self {
        ClauseStore {
            data: vec![0; 1 << 16],
            top: 0,
            free_lists: Vec::new(),
            del_ehs: Vec::new(),
            free_del_eh_slots: Vec::new(),
            justifications: Vec::new(),
            free_justification_slots: Vec::new(),
        }
    }
}

impl ClauseStore {
    pub fn new() -> Self {
        Self::default()
    }

    fn get_flags(&self, clause: Clause) -> u32 {
        self.data[clause as usize + 1] as u32
    }

    /// get_obj_size, in words.
    fn get_size(flags: u32) -> usize {
        let capacity = (flags & CAPACITY_MASK) as usize;
        HEADER_SIZE as usize
            + capacity
            + usize::from(is_lemma_kind((flags >> KIND_SHIFT) & 3))
            + usize::from(flags & HAS_DEL_EH != 0)
            + usize::from(flags & HAS_JUSTIFICATION != 0)
            + if flags & HAS_ATOMS != 0 { capacity } else { 0 }
    }

    fn allocate(&mut self, size: usize) -> usize {
        let head = self.free_lists.get(size).copied().unwrap_or(-1);
        if head != -1 {
            self.free_lists[size] = self.data[head as usize];
            return head as usize;
        }
        let block = self.top;
        self.top += size;
        if self.top > self.data.len() {
            let length = (2 * self.data.len()).max(self.top);
            self.data.resize(length, 0);
        }
        block
    }

    /// clause::mk. The atoms are the atom of each literal, which the clause keeps with the literal's
    /// sign.
    pub fn mk(
        &mut self,
        literals: &[Literal],
        kind: u32,
        justification: Option<JustificationId>,
        del_eh: Option<DelEh>,
        atoms: Option<&[u32]>,
    ) -> Clause {
        let num_literals = literals.len();
        let flags = num_literals as u32
            | (kind << KIND_SHIFT)
            | if atoms.is_some() { HAS_ATOMS } else { 0 }
            | if del_eh.is_some() { HAS_DEL_EH } else { 0 }
            | if justification.is_some() {
                HAS_JUSTIFICATION
            } else {
                0
            };
        let clause = self.allocate(Self::get_size(flags));
        self.data[clause] = num_literals as i32;
        self.data[clause + 1] = flags as i32;
        let start = clause + HEADER_SIZE as usize;
        for (index, literal) in literals.iter().enumerate() {
            self.data[start + index] = *literal as i32;
        }
        let mut extra = start + num_literals;
        if is_lemma_kind(kind) {
            self.data[extra] = 1;
            extra += 1;
        }
        if let Some(del_eh) = del_eh {
            self.data[extra] = mk_slot(&mut self.del_ehs, &mut self.free_del_eh_slots, del_eh);
            extra += 1;
        }
        if let Some(justification) = justification {
            self.data[extra] = mk_slot(
                &mut self.justifications,
                &mut self.free_justification_slots,
                justification,
            );
            extra += 1;
        }
        if let Some(atoms) = atoms {
            for index in 0..num_literals {
                self.data[extra + index] = atoms[index]
                    .wrapping_mul(2)
                    .wrapping_add(literals[index] & 1)
                    as i32;
            }
        }
        clause as Clause
    }

    /// deallocate: the block goes on its free list. The atoms must be released first.
    pub fn free(&mut self, clause: Clause) {
        let flags = self.get_flags(clause);
        if flags & HAS_DEL_EH != 0 {
            let slot = self.data[self.get_slot_address(clause, HAS_DEL_EH)];
            self.del_ehs[slot as usize] = None;
            self.free_del_eh_slots.push(slot);
        }
        if flags & HAS_JUSTIFICATION != 0 {
            let slot = self.data[self.get_slot_address(clause, HAS_JUSTIFICATION)];
            self.justifications[slot as usize] = None;
            self.free_justification_slots.push(slot);
        }
        let size = Self::get_size(flags);
        let head = self.free_lists.get(size).copied().unwrap_or(-1);
        self.data[clause as usize] = head;
        self.data[clause as usize + 1] = 0;
        if size >= self.free_lists.len() {
            self.free_lists.resize(size + 1, -1);
        }
        self.free_lists[size] = clause as i32;
    }

    /// The first word after the literals, where the activity of a lemma is.
    fn get_extra(&self, clause: Clause) -> usize {
        clause as usize + HEADER_SIZE as usize + (self.get_flags(clause) & CAPACITY_MASK) as usize
    }

    /// A clause that was freed is not one any more, which the slower paths check.
    pub fn check_live(&self, clause: Clause) -> Result<(), SmtError> {
        if self.get_flags(clause) & CAPACITY_MASK == 0 {
            return Err(SmtError::Invariant("the clause was freed".into()));
        }
        Ok(())
    }

    pub fn get_num_literals(&self, clause: Clause) -> u32 {
        self.data[clause as usize] as u32
    }

    pub fn get_literal(&self, clause: Clause, index: u32) -> Literal {
        self.data[(clause + HEADER_SIZE + index) as usize] as Literal
    }

    pub fn set_literal(&mut self, clause: Clause, index: u32, literal: Literal) {
        self.data[(clause + HEADER_SIZE + index) as usize] = literal as i32;
    }

    pub fn get_literals(&self, clause: Clause) -> Vec<Literal> {
        (0..self.get_num_literals(clause))
            .map(|index| self.get_literal(clause, index))
            .collect()
    }

    pub fn swap_literals(&mut self, clause: Clause, first: u32, second: u32) {
        self.data.swap(
            (clause + HEADER_SIZE + first) as usize,
            (clause + HEADER_SIZE + second) as usize,
        );
    }

    pub fn get_kind(&self, clause: Clause) -> u32 {
        (self.get_flags(clause) >> KIND_SHIFT) & 3
    }

    pub fn is_lemma(&self, clause: Clause) -> bool {
        is_lemma_kind(self.get_kind(clause))
    }

    fn set_flag(&mut self, clause: Clause, flag: u32, value: bool) {
        let flags = self.get_flags(clause);
        self.data[clause as usize + 1] = (if value { flags | flag } else { flags & !flag }) as i32;
    }

    pub fn is_deleted(&self, clause: Clause) -> bool {
        self.get_flags(clause) & IS_DELETED != 0
    }

    pub fn mark_as_deleted(&mut self, clause: Clause) {
        self.set_flag(clause, IS_DELETED, true);
    }

    pub fn is_reinit(&self, clause: Clause) -> bool {
        self.get_flags(clause) & IS_REINIT != 0
    }

    pub fn set_reinit(&mut self, clause: Clause, value: bool) {
        self.set_flag(clause, IS_REINIT, value);
    }

    pub fn is_reinternalize_atoms(&self, clause: Clause) -> bool {
        self.get_flags(clause) & IS_REINTERNALIZE_ATOMS != 0
    }

    pub fn set_reinternalize_atoms(&mut self, clause: Clause, value: bool) {
        self.set_flag(clause, IS_REINTERNALIZE_ATOMS, value);
    }

    pub fn get_activity(&self, clause: Clause) -> i32 {
        self.data[self.get_extra(clause)]
    }

    pub fn inc_activity(&mut self, clause: Clause) {
        let extra = self.get_extra(clause);
        self.data[extra] = self.data[extra].wrapping_add(1);
    }

    fn get_slot_address(&self, clause: Clause, flag: u32) -> usize {
        let flags = self.get_flags(clause);
        self.get_extra(clause)
            + usize::from(is_lemma_kind((flags >> KIND_SHIFT) & 3))
            + usize::from(flag == HAS_JUSTIFICATION && flags & HAS_DEL_EH != 0)
    }

    pub fn get_del_eh(&self, clause: Clause) -> Option<DelEh> {
        if self.get_flags(clause) & HAS_DEL_EH == 0 {
            return None;
        }
        self.del_ehs[self.data[self.get_slot_address(clause, HAS_DEL_EH)] as usize]
    }

    pub fn get_justification(&self, clause: Clause) -> Option<JustificationId> {
        if self.get_flags(clause) & HAS_JUSTIFICATION == 0 {
            return None;
        }
        self.justifications[self.data[self.get_slot_address(clause, HAS_JUSTIFICATION)] as usize]
    }

    fn get_atoms_address(&self, clause: Clause) -> Option<usize> {
        let flags = self.get_flags(clause);
        if flags & HAS_ATOMS == 0 {
            return None;
        }
        Some(
            self.get_slot_address(clause, HAS_JUSTIFICATION)
                + usize::from(flags & HAS_JUSTIFICATION != 0),
        )
    }

    /// The atoms the clause still holds, or none once they are released.
    pub fn get_atoms(&self, clause: Clause) -> Vec<u32> {
        let Some(address) = self.get_atoms_address(clause) else {
            return Vec::new();
        };
        if self.data[address] == NO_ATOM {
            return Vec::new();
        }
        (0..self.get_num_literals(clause) as usize)
            .map(|index| (self.data[address + index] >> 1) as u32)
            .collect()
    }

    /// The sign of the literal of atom i, as the clause was made. The clause has atoms.
    pub fn get_atom_sign(&self, clause: Clause, index: u32) -> bool {
        self.get_atoms_address(clause)
            .is_some_and(|address| self.data[address + index as usize] & 1 == 1)
    }

    /// Marks the atoms released, after their references are dropped.
    pub fn clear_atoms(&mut self, clause: Clause) {
        let Some(address) = self.get_atoms_address(clause) else {
            return;
        };
        let capacity = (self.get_flags(clause) & CAPACITY_MASK) as usize;
        self.data[address..address + capacity].fill(NO_ATOM);
    }
}

#[cfg(test)]
mod tests {
    use super::super::literal::mk_literal;
    use super::*;

    const FIRST: Literal = 10; // mk_literal(5, false)
    const SECOND: Literal = 13; // mk_literal(6, true)
    const THIRD: Literal = 14; // mk_literal(7, false)

    fn mk_del_eh(first: u32) -> DelEh {
        DelEh::DynAckInstantiated { first, second: 0 }
    }

    #[test]
    fn keeps_the_literals_activity_handler_and_atoms_of_a_lemma() {
        assert_eq!(
            [FIRST, SECOND, THIRD],
            [
                mk_literal(5, false),
                mk_literal(6, true),
                mk_literal(7, false)
            ]
        );
        let mut store = ClauseStore::new();
        let del_eh = mk_del_eh(1);
        let clause = store.mk(
            &[FIRST, SECOND, THIRD],
            CLS_TH_LEMMA,
            None,
            Some(del_eh),
            Some(&[10, 11, 12]),
        );
        assert_eq!(store.get_literals(clause), [FIRST, SECOND, THIRD]);
        assert!(store.is_lemma(clause));
        assert_eq!(store.get_activity(clause), 1);
        store.inc_activity(clause);
        assert_eq!(store.get_activity(clause), 2);
        assert_eq!(store.get_del_eh(clause), Some(del_eh));
        assert_eq!(store.get_justification(clause), None);
        store.swap_literals(clause, 0, 2);
        assert_eq!(store.get_literals(clause), [THIRD, SECOND, FIRST]);
        assert_eq!(store.get_atoms(clause), [10, 11, 12]);
        assert_eq!(
            [0, 1, 2].map(|index| store.get_atom_sign(clause, index)),
            [false, true, false]
        );
        store.clear_atoms(clause);
        assert_eq!(store.get_atoms(clause), Vec::<u32>::new());
    }

    #[test]
    fn keeps_the_flags_of_a_clause_apart() {
        let mut store = ClauseStore::new();
        let clause = store.mk(&[FIRST, SECOND], CLS_AUX, None, None, None);
        assert!(!store.is_lemma(clause));
        store.set_reinit(clause, true);
        store.mark_as_deleted(clause);
        assert_eq!(
            [
                store.is_reinit(clause),
                store.is_reinternalize_atoms(clause)
            ],
            [true, false]
        );
        assert!(store.is_deleted(clause));
        assert_eq!(store.get_kind(clause), CLS_AUX);
        assert_eq!(store.get_num_literals(clause), 2);
    }

    #[test]
    fn reuses_a_freed_block_and_its_handler_slot_for_the_next_clause_of_its_size() {
        let mut store = ClauseStore::new();
        let first_eh = mk_del_eh(1);
        let second_eh = mk_del_eh(2);
        let kept = store.mk(&[FIRST, SECOND], CLS_TH_LEMMA, None, Some(first_eh), None);
        let freed = store.mk(&[FIRST, THIRD], CLS_TH_LEMMA, None, Some(second_eh), None);
        store.free(freed);
        assert!(matches!(
            store.check_live(freed),
            Err(SmtError::Invariant(_))
        ));
        let third_eh = mk_del_eh(3);
        let reused = store.mk(&[SECOND, THIRD], CLS_TH_LEMMA, None, Some(third_eh), None);
        assert_eq!(reused, freed);
        assert_eq!(store.get_del_eh(reused), Some(third_eh));
        assert_eq!(store.get_del_eh(kept), Some(first_eh));
        let other = store.mk(&[FIRST, SECOND, THIRD], CLS_LEARNED, None, None, None);
        assert_ne!(other, freed);
        assert_eq!(store.get_literals(kept), [FIRST, SECOND]);
    }

    #[test]
    fn keeps_the_clauses_when_the_store_grows() {
        let mut store = ClauseStore::new();
        let clauses: Vec<Clause> = (0..20_000)
            .map(|index| {
                store.mk(
                    &[mk_literal(index, false), THIRD],
                    CLS_AUX,
                    None,
                    None,
                    None,
                )
            })
            .collect();
        assert_eq!(store.get_literal(clauses[0], 0), mk_literal(0, false));
        assert_eq!(
            store.get_literal(clauses[19_999], 0),
            mk_literal(19_999, false)
        );
    }

    #[test]
    fn reuses_a_justification_slot_after_its_handler() {
        let mut store = ClauseStore::new();
        let clause = store.mk(
            &[FIRST, SECOND],
            CLS_TH_LEMMA,
            Some(7),
            Some(mk_del_eh(1)),
            Some(&[3, 4]),
        );
        assert_eq!(store.get_justification(clause), Some(7));
        assert_eq!(store.get_atoms(clause), [3, 4]);
        store.clear_atoms(clause);
        store.free(clause);
        let reused = store.mk(
            &[THIRD, FIRST],
            CLS_TH_LEMMA,
            Some(8),
            Some(mk_del_eh(2)),
            Some(&[5, 6]),
        );
        assert_eq!(reused, clause);
        assert_eq!(store.get_justification(reused), Some(8));
        assert_eq!(store.get_del_eh(reused), Some(mk_del_eh(2)));
        assert_eq!(store.get_atoms(reused), [5, 6]);
    }
}
