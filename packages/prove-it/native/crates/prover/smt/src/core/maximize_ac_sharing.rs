//! Ported from Z3 (src/ast/rewriter/maximize_ac_sharing.cpp), MIT license, through
//! `maximize-ac-sharing.ts`. maximize_bv_sharing_rw: an associative application of more than two
//! arguments becomes a tree of binary applications that reuses the pairs it made before.

use std::collections::{HashMap, HashSet};

use crate::core::ast::{AstManager, Decl, Expr, OP_ADD, OP_OR, Sort};
use crate::core::rewriter_tpl::{LastResult, Reduced, RewriterConfig, RewriterTpl};
use crate::util::error::SmtError;

#[derive(Clone, Copy, Debug)]
struct SharingEntry {
    decl: Decl,
    first: Expr,
    second: Expr,
}

// MAX_NUM_ARGS_FOR_OPT: pairs are reused only for fewer arguments.
const MAX_NUM_ARGS_FOR_OPT: usize = 128;

/// maximize_bv_sharing_rw's configuration.
#[derive(Clone, Debug, Default)]
pub struct MaxBvSharingConfig {
    // Z3 registers the kinds of bvadd, bvmul, bvor and bvand when the first scope is pushed, and
    // compares the kind without the family. bvmul has the kind of or and of +, so those are
    // shared.
    is_init: bool,
    // m_entries and m_cache: the pairs made, which hold their arguments. The cache maps a
    // declaration and the lower of two arguments to the higher ones, so a pair matches in either
    // order.
    entries: Vec<SharingEntry>,
    pair_cache: HashMap<Decl, HashMap<Expr, HashSet<Expr>>>,
    pair_scopes: Vec<usize>,
}

/// rewriter_tpl with maximize_bv_sharing_rw's configuration.
pub type MaxBvSharing = RewriterTpl<MaxBvSharingConfig>;

impl MaxBvSharingConfig {
    pub fn new() -> MaxBvSharingConfig {
        MaxBvSharingConfig::default()
    }

    // The result of reduce_app, which the innermost temporaries hold.
    fn reduce_core(
        &mut self,
        m: &mut AstManager,
        decl: Decl,
        args: &[Expr],
        sort: Sort,
    ) -> Result<Expr, SmtError> {
        let mut pending = args.to_vec();
        // Reuses the pairs made before, the first pair found first. Z3 scans every pair again
        // after each reuse, but no pair is made meanwhile, so before the reused pair only the pairs
        // with the argument it became can match.
        let mut merged = 0;
        while pending.len() > 1 && pending.len() < MAX_NUM_ARGS_FOR_OPT {
            let mut pair: Option<(usize, usize)> = None;
            for first in 0..merged {
                if self.has_pair(decl, pending[first], pending[merged]) {
                    pair = Some((first, merged));
                    break;
                }
            }
            let mut first = merged;
            while pair.is_none() && first + 1 < pending.len() {
                for second in first + 1..pending.len() {
                    if self.has_pair(decl, pending[first], pending[second]) {
                        pair = Some((first, second));
                        break;
                    }
                }
                first += 1;
            }
            let Some((pair_first, pair_second)) = pair else {
                break;
            };
            pending[pair_first] =
                m.mk_app(decl, &[pending[pair_first], pending[pair_second]], sort)?;
            pending.remove(pair_second);
            merged = pair_first;
        }
        while pending.len() > 1 {
            let mut next = Vec::with_capacity(pending.len().div_ceil(2));
            let mut index = 0;
            while index < pending.len() {
                if index == pending.len() - 1 {
                    next.push(pending[index]);
                    index += 2;
                    continue;
                }
                self.insert(m, decl, pending[index], pending[index + 1]);
                next.push(m.mk_app(decl, &[pending[index], pending[index + 1]], sort)?);
                index += 2;
            }
            pending = next;
        }
        Ok(pending[0])
    }

    // entry orders its arguments by id, and pop_scope releases them in that order.
    fn insert(&mut self, m: &mut AstManager, decl: Decl, first: Expr, second: Expr) {
        let is_ordered = m.ids[first as usize] <= m.ids[second as usize];
        self.entries.push(SharingEntry {
            decl,
            first: if is_ordered { first } else { second },
            second: if is_ordered { second } else { first },
        });
        self.pair_cache
            .entry(decl)
            .or_default()
            .entry(first.min(second))
            .or_default()
            .insert(first.max(second));
        m.inc_ref(first);
        m.inc_ref(second);
    }

    fn has_pair(&self, decl: Decl, first: Expr, second: Expr) -> bool {
        self.pair_cache
            .get(&decl)
            .and_then(|by_decl| by_decl.get(&first.min(second)))
            .is_some_and(|highs| highs.contains(&first.max(second)))
    }

    pub fn push_scope(&mut self) {
        self.is_init = true;
        self.pair_scopes.push(self.entries.len());
    }

    /// pop_scope: releases the pairs made since the matching push, the last first.
    pub fn pop_scope(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        let Some(size) = self.pair_scopes.pop() else {
            return Ok(());
        };
        for index in (size..self.entries.len()).rev() {
            let entry = self.entries[index];
            if let Some(highs) = self
                .pair_cache
                .get_mut(&entry.decl)
                .and_then(|by_decl| by_decl.get_mut(&entry.first.min(entry.second)))
            {
                highs.remove(&entry.first.max(entry.second));
            }
            m.dec_ref(entry.first)?;
            m.dec_ref(entry.second)?;
        }
        self.entries.truncate(size);
        Ok(())
    }
}

impl RewriterConfig for MaxBvSharingConfig {
    fn reduce_app(
        &mut self,
        m: &mut AstManager,
        _last_result: &mut LastResult,
        decl: Decl,
        args: &[Expr],
        sort: Sort,
    ) -> Result<Reduced, SmtError> {
        let op = m.func_decls[decl as usize].op;
        if !self.is_init || (op != OP_OR && op != OP_ADD) || args.len() <= 2 {
            return Ok(Reduced::Failed);
        }
        let result = m.with_temporaries(|m| self.reduce_core(m, decl, args, sort))?;
        Ok(Reduced::Done(result))
    }
}
