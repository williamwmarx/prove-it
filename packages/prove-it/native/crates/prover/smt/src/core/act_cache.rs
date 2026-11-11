//! Ported from Z3 (src/ast/act_cache.cpp, src/util/chashtable.h), MIT license, through
//! `act-cache.ts`. The rewriter's cache from an expression and a shift to its result. It holds a
//! reference to each key and value, and keeps at most max_unused entries that were never looked up.
//! Z3 releases the entries in the order of its chained hash table, so the table is ported cell for
//! cell.
//!
//! The TypeScript keeps the cells of the tables that reset and expand_table let go, to reuse them
//! for the next table of the same capacity, since V8 allocates typed arrays slowly. No cell of a
//! reused table is read before it is written, so the port allocates each table afresh.

use crate::core::ast::{AstManager, Expr};
use crate::util::error::SmtError;

const INIT_SLOTS: usize = 8;
const INIT_CELLAR: usize = 2;
const MIN_MAX_UNUSED: usize = 1024;
const NO_CELL: i32 = -1;
// m_next of a free cell, which Z3 tags.
const FREE_CELL: i32 = -2;

#[derive(Clone, Debug)]
pub struct ActCache {
    slots: usize,
    capacity: usize,
    keys: Vec<Expr>,
    offsets: Vec<u32>,
    values: Vec<Expr>,
    // Whether client code looked the entry up, the tag of Z3's value pointer.
    is_used: Vec<u8>,
    nexts: Vec<i32>,
    next_cell: usize,
    free_cell: i32,
    size: usize,
    // The entries in insertion order from qhead on, where the oldest unused entry is searched.
    queue_keys: Vec<Expr>,
    queue_offsets: Vec<u32>,
    qhead: usize,
    num_unused: usize,
    max_unused: usize,
}

impl ActCache {
    pub fn new(max_unused: i64) -> ActCache {
        let mut cache = ActCache {
            slots: INIT_SLOTS,
            capacity: INIT_SLOTS + INIT_CELLAR,
            keys: Vec::new(),
            offsets: Vec::new(),
            values: Vec::new(),
            is_used: Vec::new(),
            nexts: Vec::new(),
            next_cell: INIT_SLOTS,
            free_cell: NO_CELL,
            size: 0,
            queue_keys: Vec::new(),
            queue_offsets: Vec::new(),
            qhead: 0,
            num_unused: 0,
            max_unused: usize::try_from(max_unused).unwrap_or(0).max(MIN_MAX_UNUSED),
        };
        cache.init_table(INIT_SLOTS, INIT_CELLAR);
        cache
    }

    fn init_table(&mut self, slots: usize, cellar: usize) {
        self.slots = slots;
        self.capacity = slots + cellar;
        self.keys = vec![0; self.capacity];
        self.offsets = vec![0; self.capacity];
        self.values = vec![0; self.capacity];
        self.is_used = vec![0; self.capacity];
        self.nexts = vec![FREE_CELL; self.capacity];
        self.next_cell = slots;
        self.free_cell = NO_CELL;
        self.size = 0;
    }

    fn get_hash(m: &AstManager, key: Expr, offset: u32) -> u32 {
        m.hashes[key as usize].wrapping_add(offset)
    }

    fn get_slot(&self, m: &AstManager, key: Expr, offset: u32) -> usize {
        (Self::get_hash(m, key, offset) as usize) & (self.slots - 1)
    }

    fn find_cell(&self, m: &AstManager, key: Expr, offset: u32) -> i32 {
        let mut cell = self.get_slot(m, key, offset) as i32;
        if self.nexts[cell as usize] == FREE_CELL {
            return NO_CELL;
        }
        while cell != NO_CELL {
            if self.keys[cell as usize] == key && self.offsets[cell as usize] == offset {
                return cell;
            }
            cell = self.nexts[cell as usize];
        }
        NO_CELL
    }

    fn get_free_cell(&mut self) -> usize {
        if self.free_cell != NO_CELL {
            let cell = self.free_cell as usize;
            self.free_cell = self.nexts[cell];
            return cell;
        }
        let cell = self.next_cell;
        self.next_cell += 1;
        cell
    }

    fn copy_cell(&mut self, target: usize, source: usize) {
        self.keys[target] = self.keys[source];
        self.offsets[target] = self.offsets[source];
        self.values[target] = self.values[source];
        self.is_used[target] = self.is_used[source];
        self.nexts[target] = self.nexts[source];
    }

    // expand_table: copy_table into twice the slots and cellar, doubling the cellar again while it
    // is too small.
    fn expand_table(&mut self, m: &AstManager) {
        let old_slots = self.slots;
        let old_keys = std::mem::take(&mut self.keys);
        let old_offsets = std::mem::take(&mut self.offsets);
        let old_values = std::mem::take(&mut self.values);
        let old_is_used = std::mem::take(&mut self.is_used);
        let old_nexts = std::mem::take(&mut self.nexts);
        let size = self.size;
        let mut cellar = (self.capacity - self.slots) * 2;
        loop {
            self.init_table(old_slots * 2, cellar);
            let mut is_copied = true;
            let mut slot = 0;
            while slot < old_slots && is_copied {
                if old_nexts[slot] != FREE_CELL {
                    let mut cell = slot as i32;
                    while cell != NO_CELL {
                        let source = cell as usize;
                        let target = self.get_slot(m, old_keys[source], old_offsets[source]);
                        if self.nexts[target] != FREE_CELL {
                            if self.next_cell == self.capacity {
                                is_copied = false;
                                break;
                            }
                            self.copy_cell(self.next_cell, target);
                            self.nexts[target] = self.next_cell as i32;
                            self.next_cell += 1;
                        } else {
                            self.nexts[target] = NO_CELL;
                        }
                        self.keys[target] = old_keys[source];
                        self.offsets[target] = old_offsets[source];
                        self.values[target] = old_values[source];
                        self.is_used[target] = old_is_used[source];
                        cell = old_nexts[source];
                    }
                }
                slot += 1;
            }
            if is_copied {
                break;
            }
            cellar *= 2;
        }
        self.size = size;
    }

    // del_unused: deletes the oldest entry that was never looked up.
    fn del_unused(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        while self.qhead < self.queue_keys.len() {
            let key = self.queue_keys[self.qhead];
            let offset = self.queue_offsets[self.qhead];
            self.qhead += 1;
            let cell = self.find_cell(m, key, offset);
            if cell == NO_CELL {
                return Err(SmtError::Invariant(
                    "an entry of the cache's queue is not in its table".into(),
                ));
            }
            if self.is_used[cell as usize] == 0 {
                self.num_unused -= 1;
                let value = self.values[cell as usize];
                self.erase(m, key, offset);
                m.dec_ref(key)?;
                m.dec_ref(value)?;
                break;
            }
        }
        if self.qhead == self.queue_keys.len() {
            self.queue_keys.clear();
            self.queue_offsets.clear();
            self.qhead = 0;
        } else if self.qhead > self.max_unused {
            self.queue_keys.drain(..self.qhead);
            self.queue_offsets.drain(..self.qhead);
            self.qhead = 0;
        }
        Ok(())
    }

    fn erase(&mut self, m: &AstManager, key: Expr, offset: u32) {
        let mut cell = self.get_slot(m, key, offset);
        let mut prev = NO_CELL;
        while self.keys[cell] != key || self.offsets[cell] != offset {
            prev = cell as i32;
            cell = self.nexts[cell] as usize;
        }
        self.size -= 1;
        let next = self.nexts[cell];
        if prev == NO_CELL {
            if next == NO_CELL {
                self.nexts[cell] = FREE_CELL;
            } else {
                self.copy_cell(cell, next as usize);
                self.recycle_cell(next as usize);
            }
        } else {
            self.nexts[prev as usize] = next;
            self.recycle_cell(cell);
        }
    }

    fn recycle_cell(&mut self, cell: usize) {
        self.nexts[cell] = self.free_cell;
        self.free_cell = cell as i32;
    }

    pub fn insert(
        &mut self,
        m: &mut AstManager,
        key: Expr,
        offset: u32,
        value: Expr,
    ) -> Result<(), SmtError> {
        if self.num_unused >= self.max_unused {
            self.del_unused(m)?;
        }
        if self.free_cell == NO_CELL && self.next_cell >= self.capacity {
            self.expand_table(m);
        }
        let slot = self.get_slot(m, key, offset);
        if self.nexts[slot] != FREE_CELL {
            let mut cell = slot as i32;
            while cell != NO_CELL {
                let index = cell as usize;
                if self.keys[index] == key && self.offsets[index] == offset {
                    // A new value replaces the old one and clears the tag, though it is not counted
                    // as unused.
                    if self.values[index] != value {
                        m.inc_ref(value);
                        m.dec_ref(self.values[index])?;
                        self.values[index] = value;
                        self.is_used[index] = 0;
                    }
                    return Ok(());
                }
                cell = self.nexts[index];
            }
            // The new entry takes the slot, and the old head moves to a free cell after it.
            let moved = self.get_free_cell();
            self.copy_cell(moved, slot);
            self.nexts[slot] = moved as i32;
        } else {
            self.nexts[slot] = NO_CELL;
        }
        m.inc_ref(key);
        m.inc_ref(value);
        self.queue_keys.push(key);
        self.queue_offsets.push(offset);
        self.num_unused += 1;
        self.size += 1;
        self.keys[slot] = key;
        self.offsets[slot] = offset;
        self.values[slot] = value;
        self.is_used[slot] = 0;
        Ok(())
    }

    pub fn find(&mut self, m: &AstManager, key: Expr, offset: u32) -> Option<Expr> {
        let cell = self.find_cell(m, key, offset);
        if cell == NO_CELL {
            return None;
        }
        let index = cell as usize;
        if self.is_used[index] == 0 {
            self.is_used[index] = 1;
            self.num_unused -= 1;
        }
        Some(self.values[index])
    }

    /// reset: releases the entries in the table's order.
    pub fn reset(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        let mut slot = 0;
        while slot < self.slots && self.size > 0 {
            if self.nexts[slot] != FREE_CELL {
                let mut cell = slot as i32;
                while cell != NO_CELL {
                    let index = cell as usize;
                    m.dec_ref(self.keys[index])?;
                    m.dec_ref(self.values[index])?;
                    cell = self.nexts[index];
                }
            }
            slot += 1;
        }
        if self.size > 0 {
            self.init_table(INIT_SLOTS, INIT_CELLAR);
        }
        self.queue_keys.clear();
        self.queue_offsets.clear();
        self.qhead = 0;
        self.num_unused = 0;
        Ok(())
    }
}
