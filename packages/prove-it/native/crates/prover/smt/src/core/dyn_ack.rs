//! Ported from Z3 (src/smt/dyn_ack.cpp), MIT license, see z3-license.txt, through `dyn-ack.ts`.
//! Dynamic Ackermann reduction with Z3's default DACK_ROOT strategy: a pair of applications whose
//! congruence is the root of conflicts often enough gets the clause f(a) = f(b) or some a_i !=
//! b_i, so the search can learn from it without the E-graph. dack.eq is off by default, so
//! equalities are not tracked.
//!
//! `DynAckManager` keeps the context, so its own fields are this struct, held by the context as
//! `dyn_ack`, and its methods that reach the context are `impl Context` methods named
//! `dyn_ack_<method>`.

use std::cmp::Reverse;
use std::collections::{HashMap, HashSet};

use crate::core::ast::{Expr, OP_EQ};
use crate::core::clause::{CLS_TH_LEMMA, DelEh};
use crate::core::context::Context;
use crate::core::literal::{Literal, negate};
use crate::util::error::SmtError;

// dyn_ack_params defaults: dack.threshold, dack.factor, dack.gc and dack.gc_inv_decay.
const DACK_THRESHOLD: u32 = 10;
const DACK_FACTOR: f64 = 0.1;
const DACK_GC: u32 = 2000;
const DACK_GC_INV_DECAY: f64 = 0.8;

/// A pair of applications; the TypeScript's key `${first},${second}` is the pair itself.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct AppPair {
    first: Expr,
    second: Expr,
}

#[derive(Clone, Debug, Default)]
pub struct DynAckManager {
    app_pair2num_occs: HashMap<AppPair, u32>,
    /// The pairs that hold references to their applications. A pair can appear more than once.
    app_pairs: Vec<AppPair>,
    to_instantiate: Vec<AppPair>,
    qhead: usize,
    num_instances: u32,
    num_propagations_since_last_gc: u32,
    instantiated: HashSet<AppPair>,
}

impl DynAckManager {
    pub fn new() -> Self {
        Self::default()
    }

    /// The Ackermann lemmas of the search so far.
    pub fn get_num_instances(&self) -> u32 {
        self.num_instances
    }

    /// The deletion handler of an instance's clause, `() => this.instantiated.delete(pair.key)`:
    /// the pair can be instantiated again.
    pub(crate) fn remove_instantiated(&mut self, first: Expr, second: Expr) {
        self.instantiated.remove(&AppPair { first, second });
    }
}

impl Context {
    fn dyn_ack_reset_app_pairs(&mut self) -> Result<(), SmtError> {
        for pair in std::mem::take(&mut self.dyn_ack.app_pairs) {
            self.m.dec_ref(pair.first)?;
            self.m.dec_ref(pair.second)?;
        }
        Ok(())
    }

    pub fn dyn_ack_init_search_eh(&mut self) -> Result<(), SmtError> {
        self.dyn_ack.app_pair2num_occs.clear();
        self.dyn_ack_reset_app_pairs()?;
        let dyn_ack = &mut self.dyn_ack;
        dyn_ack.to_instantiate = Vec::new();
        dyn_ack.qhead = 0;
        dyn_ack.num_instances = 0;
        dyn_ack.num_propagations_since_last_gc = 0;
        Ok(())
    }

    /// cg_conflict_eh, which DACK_ROOT turns into cg_eh: the congruence of the two applications is
    /// the root of a conflict.
    pub fn dyn_ack_cg_conflict_eh(&mut self, input_first: Expr, input_second: Expr) {
        if self.m.decls[input_first as usize] == OP_EQ {
            return;
        }
        let is_swapped = self.m.ids[input_first as usize] > self.m.ids[input_second as usize];
        let pair = if is_swapped {
            AppPair {
                first: input_second,
                second: input_first,
            }
        } else {
            AppPair {
                first: input_first,
                second: input_second,
            }
        };
        if self.dyn_ack.instantiated.contains(&pair) {
            return;
        }
        let previous = self.dyn_ack.app_pair2num_occs.get(&pair).copied();
        if previous.is_none() {
            self.m.inc_ref(pair.first);
            self.m.inc_ref(pair.second);
            self.dyn_ack.app_pairs.push(pair);
        }
        let num_occs = previous.unwrap_or(0) + 1;
        self.dyn_ack.app_pair2num_occs.insert(pair, num_occs);
        if num_occs == DACK_THRESHOLD {
            self.dyn_ack.to_instantiate.push(pair);
        }
    }

    /// gc: decays every count, drops the pairs that fall to 1 or below, and queues the frequent
    /// ones, most frequent first.
    fn dyn_ack_gc(&mut self) -> Result<(), SmtError> {
        self.dyn_ack.to_instantiate = Vec::new();
        self.dyn_ack.qhead = 0;
        let mut kept = 0;
        for index in 0..self.dyn_ack.app_pairs.len() {
            let pair = self.dyn_ack.app_pairs[index];
            if self.dyn_ack.instantiated.contains(&pair) {
                self.m.dec_ref(pair.first)?;
                self.m.dec_ref(pair.second)?;
                continue;
            }
            let count = self
                .dyn_ack
                .app_pair2num_occs
                .get(&pair)
                .copied()
                .unwrap_or(0);
            let num_occs = (f64::from(count) * DACK_GC_INV_DECAY).trunc() as u32;
            if num_occs <= 1 {
                self.dyn_ack.app_pair2num_occs.remove(&pair);
                self.m.dec_ref(pair.first)?;
                self.m.dec_ref(pair.second)?;
                continue;
            }
            let dyn_ack = &mut self.dyn_ack;
            dyn_ack.app_pairs[kept] = pair;
            kept += 1;
            dyn_ack.app_pair2num_occs.insert(pair, num_occs);
            if num_occs >= DACK_THRESHOLD {
                dyn_ack.to_instantiate.push(pair);
            }
        }
        let dyn_ack = &mut self.dyn_ack;
        dyn_ack.app_pairs.truncate(kept);
        let num_occs = &dyn_ack.app_pair2num_occs;
        // `(left, right) => getNumOccs(right) - getNumOccs(left)`, a stable sort.
        dyn_ack
            .to_instantiate
            .sort_by_key(|pair| Reverse(num_occs.get(pair).copied().unwrap_or(0)));
        Ok(())
    }

    pub fn dyn_ack_propagate_eh(&mut self) -> Result<(), SmtError> {
        self.dyn_ack.num_propagations_since_last_gc += 1;
        if self.dyn_ack.num_propagations_since_last_gc > DACK_GC {
            self.dyn_ack_gc()?;
            self.dyn_ack.num_propagations_since_last_gc = 0;
        }
        let max_instances = (f64::from(self.get_num_conflicts()) * DACK_FACTOR).trunc() as u32;
        while self.dyn_ack.num_instances < max_instances
            && self.dyn_ack.qhead < self.dyn_ack.to_instantiate.len()
        {
            let pair = self.dyn_ack.to_instantiate[self.dyn_ack.qhead];
            self.dyn_ack.qhead += 1;
            self.dyn_ack.num_instances += 1;
            self.dyn_ack_instantiate(pair)?;
        }
        Ok(())
    }

    fn dyn_ack_mk_eq(&mut self, first: Expr, second: Expr) -> Result<Literal, SmtError> {
        let eq = self.m.mk_eq(first, second)?;
        self.internalize(eq, true)?;
        self.get_literal(eq)
    }

    fn dyn_ack_instantiate(&mut self, pair: AppPair) -> Result<(), SmtError> {
        let mut literals = Vec::new();
        for index in 0..self.m.get_num_args(pair.first) {
            let first_arg = self.m.get_arg(pair.first, index);
            let second_arg = self.m.get_arg(pair.second, index);
            if first_arg != second_arg {
                literals.push(negate(self.dyn_ack_mk_eq(first_arg, second_arg)?));
            }
        }
        self.dyn_ack.app_pair2num_occs.remove(&pair);
        // The pair stays in app_pairs, which still holds its references.
        self.dyn_ack.instantiated.insert(pair);
        literals.push(self.dyn_ack_mk_eq(pair.first, pair.second)?);
        for literal in &literals {
            self.mark_literal_as_relevant(*literal)?;
        }
        self.mk_clause(
            &mut literals,
            None,
            CLS_TH_LEMMA,
            Some(DelEh::DynAckInstantiated {
                first: pair.first as u32,
                second: pair.second as u32,
            }),
        )?;
        Ok(())
    }
}
