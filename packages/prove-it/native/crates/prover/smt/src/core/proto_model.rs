//! Ported from Z3 (src/smt/proto_model/proto_model.cpp, src/model/func_interp.cpp,
//! src/model/value_factory.cpp, src/model/model_core.cpp), MIT license, through `proto-model.ts`.
//! The model that the SMT kernel builds from a satisfying assignment, and that model-based
//! quantifier instantiation completes and checks.
//!
//! # Design
//!
//! - A `FuncInterp` belongs to the model that interprets its declaration: `func_interps` holds it
//!   by value, and the TypeScript's moves of an interpretation between declarations and models
//!   (`reregisterDecl`, `mkModel`) move the value. Neither class keeps the manager: each method that
//!   reaches it takes `m`.
//! - A `ProtoModel` is shared by its holders (the context's model state, the generated model, the
//!   model checker that gets it from `get_model`), which the TypeScript counts with `incRef` and
//!   `decRef`; the last `dec_ref` releases what it holds. So the kernel holds it as a
//!   [`ProtoModelRef`], and keeps the explicit counts at the TypeScript's places.
//! - The model owns its evaluator, which reads and completes the model as it evaluates. `eval`
//!   takes the evaluator out of the model while it runs, and the evaluator's configuration borrows
//!   the model (`model_evaluator.rs`).
//! - The TypeScript's `null` for a missing else expression or interpretation is `None`.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use prove_num::{Int, Rational};

use crate::core::ast::{
    AstManager, Decl, Expr, KIND_APP, KIND_VAR, OP_AND, OP_EQ, OP_ITE, SORT_BOOL, Sort,
    is_arith_sort,
};
use crate::core::model_evaluator::ModelEvaluator;
use crate::core::ref_vector::RefVector;
use crate::core::rewriter::{Rewriter, TACTIC_REWRITER_OPTIONS};
use crate::util::error::SmtError;
use crate::util::hashtable::{ObjHashtable, ObjMap};
use crate::util::ordered_map::OrderedMap;
use crate::util::random_gen::RandomGen;

pub type ProtoModelRef = Rc<RefCell<ProtoModel>>;

/// func_entry: the arguments of an entry and its result.
#[derive(Clone, Debug)]
pub struct FuncEntry {
    pub args: Vec<Expr>,
    pub result: Expr,
}

/// func_interp: a finite table of entries and an else expression over the variables (:var i) for
/// argument i. It holds the arguments and result of each entry, the else expression and the cached
/// interpretation.
#[derive(Clone, Debug, Default)]
pub struct FuncInterp {
    entries: Vec<FuncEntry>,
    // The index of each entry by its arguments; only looked up, never iterated.
    entry_table: HashMap<Vec<Expr>, usize>,
    else_expr: Option<Expr>,
    interp: Option<Expr>,
    arity: usize,
}

impl FuncInterp {
    pub fn new(arity: usize) -> FuncInterp {
        FuncInterp {
            arity,
            ..FuncInterp::default()
        }
    }

    pub fn get_arity(&self) -> usize {
        self.arity
    }

    /// The entries, in the order they were inserted.
    pub fn get_entries(&self) -> &[FuncEntry] {
        &self.entries
    }

    pub fn get_else(&self) -> Option<Expr> {
        self.else_expr
    }

    pub fn is_partial(&self) -> bool {
        self.else_expr.is_none()
    }

    pub fn get_entry(&self, args: &[Expr]) -> Option<&FuncEntry> {
        self.entry_table
            .get(args)
            .map(|index| &self.entries[*index])
    }

    pub fn insert_new_entry(
        &mut self,
        m: &mut AstManager,
        args: &[Expr],
        result: Expr,
    ) -> Result<(), SmtError> {
        self.reset_interp_cache(m)?;
        // func_entry: the result is held first, then the arguments.
        m.inc_ref(result);
        for arg in args {
            m.inc_ref(*arg);
        }
        self.entry_table.insert(args.to_vec(), self.entries.len());
        self.entries.push(FuncEntry {
            args: args.to_vec(),
            result,
        });
        Ok(())
    }

    pub fn insert_entry(
        &mut self,
        m: &mut AstManager,
        args: &[Expr],
        result: Expr,
    ) -> Result<(), SmtError> {
        self.reset_interp_cache(m)?;
        let Some(index) = self.entry_table.get(args).copied() else {
            return self.insert_new_entry(m, args, result);
        };
        // func_entry::set_result.
        m.inc_ref(result);
        m.dec_ref(self.entries[index].result)?;
        self.entries[index].result = result;
        Ok(())
    }

    fn reset_interp_cache(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        if let Some(interp) = self.interp.take() {
            m.dec_ref(interp)?;
        }
        Ok(())
    }

    // func_entry::deallocate.
    fn release_entry(m: &mut AstManager, entry: &FuncEntry) -> Result<(), SmtError> {
        for arg in &entry.args {
            m.dec_ref(*arg)?;
        }
        m.dec_ref(entry.result)
    }

    /// ~func_interp.
    pub fn release(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        for entry in &self.entries {
            FuncInterp::release_entry(m, entry)?;
        }
        if let Some(else_expr) = self.else_expr {
            m.dec_ref(else_expr)?;
        }
        self.reset_interp_cache(m)
    }

    // is_fi_entry_expr: (ite (and (= (:var 0) a0) ...) t e) with a ground t.
    fn get_entry_args(&self, m: &AstManager, expr: Expr) -> Option<Vec<Expr>> {
        if m.get_op(expr) != OP_ITE {
            return None;
        }
        let condition = m.get_arg(expr, 0);
        if !m.is_ground(m.get_arg(expr, 1)) || self.arity == 0 {
            return None;
        }
        if self.arity == 1 && m.get_op(condition) != OP_EQ {
            return None;
        }
        if self.arity > 1
            && (m.get_op(condition) != OP_AND || m.get_num_args(condition) != self.arity)
        {
            return None;
        }
        let mut args = Vec::new();
        for index in 0..self.arity {
            let eq = if self.arity == 1 {
                condition
            } else {
                m.get_arg(condition, index)
            };
            if m.get_op(eq) != OP_EQ {
                return None;
            }
            let left = m.get_arg(eq, 0);
            let right = m.get_arg(eq, 1);
            let is_var_at = |expr: Expr| {
                m.kinds[expr as usize] == KIND_VAR && m.values[expr as usize] == index as i32
            };
            if is_var_at(left) {
                args.push(right);
            } else if is_var_at(right) {
                args.push(left);
            } else {
                return None;
            }
        }
        Some(args)
    }

    pub fn set_else(&mut self, m: &mut AstManager, expr: Expr) -> Result<(), SmtError> {
        if Some(expr) == self.else_expr {
            return Ok(());
        }
        self.reset_interp_cache(m)?;
        let mut current = expr;
        while let Some(args) = self.get_entry_args(m, current) {
            if self.get_entry(&args).is_none() {
                self.insert_entry(m, &args, m.get_arg(current, 1))?;
            }
            current = m.get_arg(current, 2);
        }
        m.inc_ref(current);
        if let Some(else_expr) = self.else_expr {
            m.dec_ref(else_expr)?;
        }
        self.else_expr = Some(current);
        Ok(())
    }

    pub fn is_constant(&self, m: &AstManager) -> bool {
        let Some(else_expr) = self.else_expr else {
            return false;
        };
        if !m.is_ground(else_expr) {
            return false;
        }
        self.entries.iter().all(|entry| entry.result == else_expr)
    }

    pub fn get_max_occ_result(&self) -> Option<Expr> {
        // Only looked up, never iterated.
        let mut counts: HashMap<Expr, usize> = HashMap::new();
        let mut best = None;
        let mut max = 0;
        for entry in &self.entries {
            let count = counts.get(&entry.result).copied().unwrap_or(0) + 1;
            counts.insert(entry.result, count);
            if count > max {
                max = count;
                best = Some(entry.result);
            }
        }
        best
    }

    /// compress: drops the entries whose result is the else value, and recognizes the identity.
    pub fn compress(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        let Some(else_expr) = self.else_expr else {
            return Ok(());
        };
        if self.entries.is_empty() || !m.is_ground(else_expr) {
            return Ok(());
        }
        let mut kept = Vec::new();
        for entry in &self.entries {
            if entry.result != else_expr {
                kept.push(entry.clone());
            } else {
                FuncInterp::release_entry(m, entry)?;
            }
        }
        if kept.len() < self.entries.len() {
            self.reset_interp_cache(m)?;
            self.entries = kept;
            self.entry_table = self
                .entries
                .iter()
                .enumerate()
                .map(|(index, entry)| (entry.args.clone(), index))
                .collect();
        }
        if !self.entries.is_empty() && self.is_identity(m) {
            for entry in &self.entries {
                FuncInterp::release_entry(m, entry)?;
            }
            self.entries = Vec::new();
            self.entry_table.clear();
            self.reset_interp_cache(m)?;
            let identity = m.mk_var(0, m.sorts[else_expr as usize]);
            m.inc_ref(identity);
            m.dec_ref(else_expr)?;
            self.else_expr = Some(identity);
        }
        Ok(())
    }

    // is_identity: only Bool has a finite number of elements among tlapm's sorts.
    fn is_identity(&self, m: &AstManager) -> bool {
        let Some(else_expr) = self.else_expr else {
            return false;
        };
        if self.arity != 1 {
            return false;
        }
        for entry in &self.entries {
            if entry.args[0] != entry.result || entry.result == else_expr {
                return false;
            }
        }
        if m.kinds[else_expr as usize] == KIND_VAR {
            return true;
        }
        if !m.is_unique_value(else_expr) || m.sorts[else_expr as usize] != SORT_BOOL {
            return false;
        }
        self.entries.len() + 1 == 2
    }

    /// get_interp: the interpretation as an expression over the argument variables, which it
    /// caches.
    pub fn get_interp(&mut self, m: &mut AstManager) -> Result<Option<Expr>, SmtError> {
        if self.interp.is_some() {
            return Ok(self.interp);
        }
        let Some(else_expr) = self.else_expr else {
            return Ok(None);
        };
        let mut result = else_expr;
        let mut vars: Vec<Expr> = Vec::new();
        for entry in &self.entries {
            if entry.result == else_expr {
                continue;
            }
            if vars.is_empty() {
                for (index, arg) in entry.args.iter().enumerate() {
                    let sort = m.sorts[*arg as usize];
                    vars.push(m.mk_var(index as i32, sort));
                }
            }
            let mut eqs = Vec::with_capacity(entry.args.len());
            for (index, arg) in entry.args.iter().enumerate() {
                eqs.push(m.mk_eq(vars[index], *arg)?);
            }
            let condition = m.mk_and(&eqs)?;
            if m.is_true(entry.result) {
                result = if m.is_false(result) {
                    condition
                } else {
                    m.mk_or(&[condition, result])?
                };
            } else if m.is_false(entry.result) {
                let negated = m.mk_not(condition)?;
                result = if m.is_true(result) {
                    negated
                } else {
                    m.mk_and(&[negated, result])?
                };
            } else if entry.result != result {
                let sort = m.sorts[result as usize];
                result = m.mk_app(OP_ITE, &[condition, entry.result, result], sort)?;
            }
        }
        m.inc_ref(result);
        self.interp = Some(result);
        Ok(Some(result))
    }
}

pub struct ProtoModel {
    /// m_interp: the value of each constant, keyed by declaration, hashed by
    /// `AstManager::get_decl_hash`.
    pub const_interps: ObjMap<Expr>,
    // m_const_decls: the constants in the order they were registered.
    const_decls: Vec<Decl>,
    /// m_finterp, in Z3's slot order, keyed and hashed like `const_interps`.
    pub func_interps: ObjMap<FuncInterp>,
    // m_func_decls, in the order they were registered.
    func_decls: Vec<Decl>,
    aux_decls: ObjHashtable,
    // user_sort_factory and the arith_factory: the values of each sort, in Z3's hash order (hashed
    // by the expression's hash), and the values each factory holds, in the order it made or
    // registered them.
    values: OrderedMap<Sort, ObjHashtable>,
    user_sort_values: RefVector,
    arith_values: RefVector,
    // Only looked up, never iterated.
    next_value: HashMap<Sort, i32>,
    finite_sorts: HashSet<Sort>,
    bool_random: RandomGen,
    // None while eval runs it.
    evaluator: Option<ModelEvaluator>,
    // m_rewrite: the th_rewriter that cleanup simplifies the interpretations with.
    rewriter: Rewriter,
    // The holders of a proto_model and a model are counted, and the last one releases it.
    ref_count: i32,
}

impl ProtoModel {
    pub fn new(m: &AstManager) -> ProtoModel {
        ProtoModel {
            bool_random: RandomGen::new(m.get_num_asts() as u32),
            const_interps: ObjMap::new(),
            const_decls: Vec::new(),
            func_interps: ObjMap::new(),
            func_decls: Vec::new(),
            user_sort_values: RefVector::new(),
            arith_values: RefVector::new(),
            aux_decls: ObjHashtable::new(),
            values: OrderedMap::new(),
            next_value: HashMap::new(),
            finite_sorts: HashSet::new(),
            evaluator: Some(ModelEvaluator::new(m)),
            rewriter: Rewriter::new(m, TACTIC_REWRITER_OPTIONS, false),
            ref_count: 0,
        }
    }

    /// `constInterps.get(decl)`.
    pub fn get_const_interp(&self, m: &AstManager, decl: Decl) -> Option<Expr> {
        self.const_interps
            .get(decl as u32, m.get_decl_hash(decl))
            .copied()
    }

    /// `funcInterps.get(decl)`.
    pub fn get_func_interp(&self, m: &AstManager, decl: Decl) -> Option<&FuncInterp> {
        self.func_interps.get(decl as u32, m.get_decl_hash(decl))
    }

    pub fn get_func_interp_mut(&mut self, m: &AstManager, decl: Decl) -> Option<&mut FuncInterp> {
        self.func_interps
            .get_mut(decl as u32, m.get_decl_hash(decl))
    }

    /// The constants, in the order they were registered.
    pub fn get_const_decls(&self) -> &[Decl] {
        &self.const_decls
    }

    /// The functions, in the order they were registered.
    pub fn get_func_decls(&self) -> &[Decl] {
        &self.func_decls
    }

    /// model_core::register_decl: the model holds the declaration and the value.
    pub fn register_const(
        &mut self,
        m: &mut AstManager,
        decl: Decl,
        value: Expr,
    ) -> Result<(), SmtError> {
        let hash = m.get_decl_hash(decl);
        let old = self.const_interps.get(decl as u32, hash).copied();
        if old.is_none() {
            m.inc_decl_ref(decl);
        }
        m.inc_ref(value);
        match old {
            None => self.const_decls.push(decl),
            Some(old) => m.dec_ref(old)?,
        }
        self.const_interps.insert(decl as u32, hash, value);
        Ok(())
    }

    /// model_core::register_decl: the interpretation replaces the old one, which is released. The
    /// model holds the declaration.
    pub fn register_func(
        &mut self,
        m: &mut AstManager,
        decl: Decl,
        interp: FuncInterp,
    ) -> Result<(), SmtError> {
        let hash = m.get_decl_hash(decl);
        let old = self
            .func_interps
            .get_mut(decl as u32, hash)
            .map(std::mem::take);
        if old.is_none() {
            self.func_decls.push(decl);
            m.inc_decl_ref(decl);
        }
        self.func_interps.insert(decl as u32, hash, interp);
        if let Some(mut old) = old {
            old.release(m)?;
        }
        Ok(())
    }

    pub fn register_aux_decl(
        &mut self,
        m: &mut AstManager,
        decl: Decl,
        interp: Option<FuncInterp>,
    ) -> Result<(), SmtError> {
        if let Some(interp) = interp {
            self.register_func(m, decl, interp)?;
        }
        self.aux_decls.insert(decl as u32, m.get_decl_hash(decl));
        Ok(())
    }

    /// reregister_decl: the old interpretation of decl moves to aux_decl.
    pub fn reregister_decl(
        &mut self,
        m: &mut AstManager,
        decl: Decl,
        interp: FuncInterp,
        aux_decl: Decl,
    ) -> Result<(), SmtError> {
        let hash = m.get_decl_hash(decl);
        let Some(old) = self
            .func_interps
            .get_mut(decl as u32, hash)
            .map(std::mem::take)
        else {
            return self.register_func(m, decl, interp);
        };
        self.register_func(m, aux_decl, old)?;
        self.aux_decls
            .insert(aux_decl as u32, m.get_decl_hash(aux_decl));
        self.func_interps.insert(decl as u32, hash, interp);
        Ok(())
    }

    /// eval: the result comes with a reference, which the caller releases.
    pub fn eval(
        &mut self,
        m: &mut AstManager,
        expr: Expr,
        is_model_completion: bool,
    ) -> Result<Expr, SmtError> {
        let mut evaluator = self
            .evaluator
            .take()
            .ok_or_else(|| SmtError::Invariant("the model is evaluating already".into()))?;
        let result = evaluator
            .set_model_completion(m, is_model_completion)
            .and_then(|()| evaluator.rewrite(m, self, expr));
        self.evaluator = Some(evaluator);
        result
    }

    fn get_value_set(&mut self, sort: Sort) -> &mut ObjHashtable {
        self.values.get_or_insert_with(sort, ObjHashtable::new)
    }

    // arith_factory's values are the integers, of either sort.
    fn mk_indexed_value(m: &mut AstManager, index: i32, sort: Sort) -> Expr {
        if is_arith_sort(sort) {
            m.mk_numeral_of_sort(&Rational::from_int(Int::from(index)), sort)
        } else {
            m.mk_model_value(index, sort)
        }
    }

    // mk_value and register_value: a value is inserted only when it is new, since inserting grows
    // the table even for a value it has.
    fn add_value(&mut self, m: &mut AstManager, sort: Sort, value: Expr) {
        let hash = m.hashes[value as usize];
        if self.get_value_set(sort).contains(value as u32, hash) {
            return;
        }
        if is_arith_sort(sort) {
            self.arith_values.push(m, value);
        } else {
            self.user_sort_values.push(m, value);
        }
        self.get_value_set(sort).insert(value as u32, hash);
    }

    fn mk_value(&mut self, m: &mut AstManager, index: i32, sort: Sort) -> Expr {
        let value = ProtoModel::mk_indexed_value(m, index, sort);
        self.add_value(m, sort, value);
        value
    }

    pub fn register_value(&mut self, m: &mut AstManager, value: Expr) {
        let sort = m.sorts[value as usize];
        if sort != SORT_BOOL {
            self.add_value(m, sort, value);
        }
    }

    pub fn get_some_value(&mut self, m: &mut AstManager, sort: Sort) -> Expr {
        if sort == SORT_BOOL {
            return if self.bool_random.next().is_multiple_of(2) {
                m.false_expr
            } else {
                m.true_expr
            };
        }
        let set = self.values.get(&sort);
        if self.finite_sorts.contains(&sort)
            && let Some(set) = set
        {
            let mut random = RandomGen::new(m.get_num_asts() as u32);
            let mut count = 1;
            let mut result = m.false_expr;
            for value in set.iter() {
                if random.next().is_multiple_of(count) {
                    result = value as Expr;
                }
                count += 1;
                if count > 10 {
                    break;
                }
            }
            return result;
        }
        if let Some(first) = set.and_then(|set| set.iter().next()) {
            return first as Expr;
        }
        self.mk_value(m, 0, sort)
    }

    pub fn get_fresh_value(&mut self, m: &mut AstManager, sort: Sort) -> Option<Expr> {
        if sort == SORT_BOOL || self.finite_sorts.contains(&sort) {
            return None;
        }
        self.get_value_set(sort);
        let mut next = self.next_value.get(&sort).copied().unwrap_or(0);
        loop {
            let value = ProtoModel::mk_indexed_value(m, next, sort);
            next += 1;
            let hash = m.hashes[value as usize];
            if !self.get_value_set(sort).contains(value as u32, hash) {
                self.add_value(m, sort, value);
                self.next_value.insert(sort, next);
                return Some(value);
            }
        }
    }

    pub fn freeze_universe(&mut self, m: &mut AstManager, sort: Sort) {
        if self.finite_sorts.contains(&sort) {
            return;
        }
        if self.values.get(&sort).is_none_or(ObjHashtable::is_empty) {
            self.get_some_value(m, sort);
        }
        self.finite_sorts.insert(sort);
    }

    pub fn is_finite(&self, m: &AstManager, sort: Sort) -> bool {
        m.is_uninterpreted_sort(sort) && self.finite_sorts.contains(&sort)
    }

    /// The values of the sort, in Z3's hash order.
    pub fn get_known_universe(&self, sort: Sort) -> Vec<Expr> {
        self.values.get(&sort).map_or_else(Vec::new, |set| {
            set.iter().map(|value| value as Expr).collect()
        })
    }

    pub fn compress(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        for index in 0..self.func_decls.len() {
            let decl = self.func_decls[index];
            if let Some(interp) = self
                .func_interps
                .get_mut(decl as u32, m.get_decl_hash(decl))
            {
                interp.compress(m)?;
            }
        }
        Ok(())
    }

    pub fn complete_partial_func(
        &mut self,
        m: &mut AstManager,
        decl: Decl,
        is_using_fresh: bool,
    ) -> Result<(), SmtError> {
        let hash = m.get_decl_hash(decl);
        let max_occ_result = match self.func_interps.get(decl as u32, hash) {
            Some(interp) if interp.is_partial() => interp.get_max_occ_result(),
            _ => return Ok(()),
        };
        let range = m.func_decls[decl as usize].range;
        let fresh = if is_using_fresh {
            self.get_fresh_value(m, range)
        } else {
            None
        };
        let value = match fresh.or(max_occ_result) {
            Some(value) => value,
            None => self.get_some_value(m, range),
        };
        match self.func_interps.get_mut(decl as u32, hash) {
            Some(interp) => interp.set_else(m, value),
            None => Ok(()),
        }
    }

    pub fn complete_partial_funcs(
        &mut self,
        m: &mut AstManager,
        is_using_fresh: bool,
    ) -> Result<(), SmtError> {
        // get_some_value may register more declarations, which the loop then completes too.
        let mut index = 0;
        while index < self.func_decls.len() {
            let decl = self.func_decls[index];
            self.complete_partial_func(m, decl, is_using_fresh)?;
            index += 1;
        }
        Ok(())
    }

    // cleanup_expr: replaces the uninterpreted constants in an else expression with their values.
    // Like Z3, it walks a todo stack, so it rewrites the last argument of a term first. The trail
    // holds the terms it rewrote until the next call.
    fn cleanup_expr(
        &mut self,
        m: &mut AstManager,
        trail: &mut RefVector,
        expr: Expr,
        found_aux_decls: &mut ObjHashtable,
    ) -> Result<Expr, SmtError> {
        trail.reset(m)?;
        // Only looked up, never iterated.
        let mut cache: HashMap<Expr, Expr> = HashMap::new();
        let mut todo = vec![expr];
        while let Some(current) = todo.last().copied() {
            if m.is_uninterpreted_const(current) {
                todo.pop();
                let decl = m.decls[current as usize];
                let existing = self.get_const_interp(m, decl);
                let value = match existing {
                    Some(value) => value,
                    None => self.get_some_value(m, m.sorts[current as usize]),
                };
                if existing.is_none() {
                    self.register_const(m, decl, value)?;
                }
                cache.insert(current, value);
                continue;
            }
            if m.kinds[current as usize] != KIND_APP || m.get_num_args(current) == 0 {
                todo.pop();
                cache.insert(current, current);
                continue;
            }
            let num_todo = todo.len();
            for index in 0..m.get_num_args(current) {
                let arg = m.get_arg(current, index);
                if !cache.contains_key(&arg) {
                    todo.push(arg);
                }
            }
            if todo.len() > num_todo {
                continue;
            }
            todo.pop();
            let decl = m.decls[current as usize];
            if self.aux_decls.contains(decl as u32, m.get_decl_hash(decl)) {
                found_aux_decls.insert(decl as u32, m.get_decl_hash(decl));
            }
            let args: Vec<Expr> = (0..m.get_num_args(current))
                .map(|index| {
                    let arg = m.get_arg(current, index);
                    cache.get(&arg).copied().unwrap_or(arg)
                })
                .collect();
            let sort = m.sorts[current as usize];
            let rewriter = &mut self.rewriter;
            let rewritten = m.with_temporaries(|m| rewriter.mk_app(m, decl, &args, sort))?;
            if rewritten == current {
                m.dec_ref(rewritten)?;
            } else {
                trail.push_owned(rewritten);
            }
            cache.insert(current, rewritten);
        }
        Ok(cache.get(&expr).copied().unwrap_or(expr))
    }

    /// cleanup: also removes the auxiliary declarations that no interpretation uses.
    pub fn cleanup(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        let mut found_aux_decls = ObjHashtable::new();
        let mut trail = RefVector::new();
        // Like Z3, it collects the interpretations before it cleans them up.
        let decls: Vec<u32> = self.func_interps.keys().collect();
        for decl in decls {
            let hash = m.get_decl_hash(decl as Decl);
            let Some(else_expr) = self
                .func_interps
                .get(decl, hash)
                .and_then(FuncInterp::get_else)
            else {
                continue;
            };
            let cleaned = self.cleanup_expr(m, &mut trail, else_expr, &mut found_aux_decls)?;
            if let Some(interp) = self.func_interps.get_mut(decl, hash) {
                interp.set_else(m, cleaned)?;
            }
        }
        let mut index = 0;
        while index < self.const_decls.len() {
            let decl = self.const_decls[index];
            let value = self.get_const_interp(m, decl).ok_or_else(|| {
                SmtError::Invariant("a registered constant has no interpretation".into())
            })?;
            let cleaned = self.cleanup_expr(m, &mut trail, value, &mut found_aux_decls)?;
            if cleaned != value {
                self.register_const(m, decl, cleaned)?;
            }
            index += 1;
        }
        if found_aux_decls.len() != self.aux_decls.len() {
            // remove_aux_decls_not_in_set.
            let aux_decls = &self.aux_decls;
            self.func_decls.retain(|decl| {
                let hash = m.get_decl_hash(*decl);
                !aux_decls.contains(*decl as u32, hash)
                    || found_aux_decls.contains(*decl as u32, hash)
            });
            let removed: Vec<u32> = self
                .aux_decls
                .iter()
                .filter(|decl| !found_aux_decls.contains(*decl, m.get_decl_hash(*decl as Decl)))
                .collect();
            for decl in removed {
                self.unregister_decl(m, decl as Decl)?;
            }
            self.aux_decls = found_aux_decls;
        }
        trail.reset(m)
    }

    // model_core::unregister_decl: releases the value or the interpretation. The last constant
    // takes the place of a removed one.
    fn unregister_decl(&mut self, m: &mut AstManager, decl: Decl) -> Result<(), SmtError> {
        let hash = m.get_decl_hash(decl);
        if let Some(value) = self.const_interps.get(decl as u32, hash).copied() {
            if let Some(index) = self.const_decls.iter().position(|inner| *inner == decl) {
                self.const_decls.swap_remove(index);
            }
            self.const_interps.remove(decl as u32, hash);
            m.dec_decl_ref(decl)?;
            return m.dec_ref(value);
        }
        let Some(mut interp) = self
            .func_interps
            .get_mut(decl as u32, hash)
            .map(std::mem::take)
        else {
            return Ok(());
        };
        self.func_interps.remove(decl as u32, hash);
        if let Some(index) = self.func_decls.iter().position(|inner| *inner == decl) {
            self.func_decls.remove(index);
        }
        m.dec_decl_ref(decl)?;
        interp.release(m)
    }

    pub fn inc_ref(&mut self) {
        self.ref_count += 1;
    }

    /// The last holder releases the model's references.
    pub fn dec_ref(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.ref_count -= 1;
        if self.ref_count == 0 {
            return self.release(m);
        }
        Ok(())
    }

    // ~proto_model: the rewriter, the evaluator and the factories go before the interpretations,
    // and the user sort factory before the arith_factory.
    fn release(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.rewriter.release(m)?;
        if let Some(evaluator) = self.evaluator.as_mut() {
            evaluator.release(m)?;
        }
        self.user_sort_values.reset(m)?;
        self.arith_values.reset(m)?;
        let consts: Vec<(u32, Expr)> = self
            .const_interps
            .iter()
            .map(|(decl, value)| (decl, *value))
            .collect();
        for (decl, value) in consts {
            m.dec_decl_ref(decl as Decl)?;
            m.dec_ref(value)?;
        }
        for (decl, interp) in self.func_interps.iter_mut() {
            m.dec_decl_ref(decl as Decl)?;
            interp.release(m)?;
        }
        Ok(())
    }

    /// mk_model: the model holds the values of the constants and the universes of the
    /// uninterpreted sorts, and takes the interpretations of the functions. The model has no
    /// holder yet.
    pub fn mk_model(&mut self, m: &mut AstManager) -> Result<ProtoModel, SmtError> {
        let mut model = ProtoModel::new(m);
        let consts: Vec<(u32, Expr)> = self
            .const_interps
            .iter()
            .map(|(decl, value)| (decl, *value))
            .collect();
        for (decl, value) in consts {
            model.register_const(m, decl as Decl, value)?;
        }
        let interps: Vec<(u32, FuncInterp)> = self
            .func_interps
            .iter_mut()
            .map(|(decl, interp)| (decl, std::mem::take(interp)))
            .collect();
        for (decl, interp) in interps {
            model.register_func(m, decl as Decl, interp)?;
            m.dec_decl_ref(decl as Decl)?;
        }
        self.func_interps.clear();
        self.func_decls = Vec::new();
        for (sort, set) in self.values.iter() {
            if !is_arith_sort(*sort) {
                for value in set.iter() {
                    model.register_value(m, value as Expr);
                }
            }
        }
        Ok(model)
    }

    /// model::get_some_const_interp.
    pub fn get_some_const_interp(&mut self, m: &mut AstManager, decl: Decl) -> Expr {
        match self.get_const_interp(m, decl) {
            Some(value) => value,
            None => self.get_some_value(m, m.func_decls[decl as usize].range),
        }
    }

    /// model::are_equal for values.
    pub fn are_equal(&self, first: Expr, second: Expr) -> bool {
        first == second
    }
}

#[cfg(test)]
pub(crate) mod tests {
    //! The hand-built interpretations and models of `scripts/smt-model-reference.ts`, built in the
    //! same order, against the table it printed (`tests/tables/models.txt`): each line of a section
    //! here is the line the TypeScript printed.

    use prove_decide::Limits;
    use prove_num::Int;

    use super::{FuncInterp, ProtoModel};
    use crate::core::ast::{
        AstManager, Decl, Expr, OP_IDIV, OP_IDIV0, OP_ITE, OP_MOD, SORT_BOOL, SORT_INT, SmtSymbol,
        Sort, get_symbol_name,
    };
    use crate::util::rlimit::ResourceLimit;

    const TABLE: &str = include_str!("../../tests/tables/models.txt");

    /// The lines of a section of the table.
    pub(crate) fn get_section(name: &str) -> Vec<String> {
        let header = format!("== {name} ==");
        TABLE
            .lines()
            .skip_while(|line| *line != header)
            .skip(1)
            .take_while(|line| !line.starts_with("== "))
            .map(str::to_string)
            .collect()
    }

    pub(crate) fn show(m: &AstManager, expr: Option<Expr>) -> String {
        match expr {
            None | Some(-1) => "none".into(),
            Some(expr) => format!("{}#{}", m.to_string(expr), m.ids[expr as usize]),
        }
    }

    fn get_decl_name(m: &AstManager, decl: u32) -> String {
        get_symbol_name(&m.func_decls[decl as usize].name)
    }

    fn get_interp_text(m: &AstManager, interp: &FuncInterp) -> String {
        let mut parts: Vec<String> = interp
            .get_entries()
            .iter()
            .map(|entry| {
                let args: Vec<String> = entry.args.iter().map(|arg| show(m, Some(*arg))).collect();
                format!("[{} -> {}]", args.join(" "), show(m, Some(entry.result)))
            })
            .collect();
        parts.push(format!("else {}", show(m, interp.get_else())));
        parts.join(" ")
    }

    /// The constants and functions in slot order, and the universes of the sorts.
    pub(crate) fn print_model(
        out: &mut Vec<String>,
        m: &AstManager,
        model: &ProtoModel,
        sorts: &[Sort],
    ) {
        for (decl, value) in model.const_interps.iter() {
            out.push(format!(
                "const {} = {}",
                get_decl_name(m, decl),
                show(m, Some(*value))
            ));
        }
        for (decl, interp) in model.func_interps.iter() {
            out.push(format!(
                "func {} {}",
                get_decl_name(m, decl),
                get_interp_text(m, interp)
            ));
        }
        for sort in sorts {
            let universe: Vec<String> = model
                .get_known_universe(*sort)
                .iter()
                .map(|value| show(m, Some(*value)))
                .collect();
            out.push(format!(
                "universe {}: {}",
                m.sort_names[*sort as usize],
                universe.join(" ")
            ));
        }
    }

    pub(crate) fn print_counts(out: &mut Vec<String>, m: &AstManager, label: &str) {
        out.push(format!(
            "{label}: steps={} asts={}",
            m.limit.count(),
            m.get_num_asts()
        ));
    }

    /// The value of each term without and with model completion; the terms are held, as a caller
    /// holds what it evaluates.
    pub(crate) fn print_evals(
        out: &mut Vec<String>,
        m: &mut AstManager,
        model: &mut ProtoModel,
        terms: &[Expr],
    ) {
        for term in terms {
            m.inc_ref(*term);
        }
        for is_model_completion in [false, true] {
            for term in terms {
                let value = model.eval(m, *term, is_model_completion).unwrap();
                out.push(format!(
                    "eval {} {} = {} steps={}",
                    if is_model_completion {
                        "complete"
                    } else {
                        "partial"
                    },
                    show(m, Some(*term)),
                    show(m, Some(value)),
                    m.limit.count()
                ));
                m.dec_ref(value).unwrap();
            }
        }
    }

    pub(crate) fn assert_section(name: &str, out: &[String]) {
        let expected = get_section(name);
        assert!(!expected.is_empty(), "no section {name}");
        for (index, (actual, expected)) in out.iter().zip(&expected).enumerate() {
            assert_eq!(actual, expected, "{name}, line {}", index + 1);
        }
        assert_eq!(out.len(), expected.len(), "{name}: the number of lines");
    }

    fn mk_manager() -> AstManager {
        AstManager::new(ResourceLimit::new(&Limits::new(f64::INFINITY, None, None)))
    }

    fn mk_decl(m: &mut AstManager, name: &str, domain: &[Sort], range: Sort) -> Decl {
        m.mk_func_decl(SmtSymbol::Name(name.into()), domain, range, false)
    }

    fn mk_const(m: &mut AstManager, name: &str, sort: Sort) -> Expr {
        let decl = mk_decl(m, name, &[], sort);
        m.mk_app(decl, &[], sort).unwrap()
    }

    fn mk_fresh_decl(m: &mut AstManager, prefix: &str, domain: &[Sort], range: Sort) -> Decl {
        m.mk_fresh_func_decl(Some(&SmtSymbol::Name(prefix.into())), domain, range, true)
    }

    fn app(m: &mut AstManager, decl: Decl, args: &[Expr], sort: Sort) -> Expr {
        m.mk_app(decl, args, sort).unwrap()
    }

    #[test]
    fn func_interps_hold_their_entries_and_else_expressions() {
        let mut out = Vec::new();
        let m = &mut mk_manager();
        let u = m.mk_sort("U");
        let values: Vec<Expr> = (0..3).map(|index| m.mk_model_value(index, u)).collect();
        for value in &values {
            m.inc_ref(*value);
        }
        let (v0, v1, v2) = (values[0], values[1], values[2]);
        let mut unary = FuncInterp::new(1);
        unary.insert_new_entry(m, &[v0], v1).unwrap();
        unary.insert_entry(m, &[v1], v0).unwrap();
        unary.insert_entry(m, &[v0], v2).unwrap();
        out.push(format!(
            "unary {} partial={}",
            get_interp_text(m, &unary),
            unary.is_partial()
        ));
        out.push(format!(
            "max-occ {} constant={}",
            show(m, unary.get_max_occ_result()),
            unary.is_constant(m)
        ));
        unary.set_else(m, v2).unwrap();
        let interp = unary.get_interp(m).unwrap();
        out.push(format!("interp {}", show(m, interp)));
        unary.compress(m).unwrap();
        let interp = unary.get_interp(m).unwrap();
        out.push(format!(
            "compressed {} interp {}",
            get_interp_text(m, &unary),
            show(m, interp)
        ));
        let x0 = m.mk_var(0, u);
        let eq = m.mk_eq(v0, x0).unwrap();
        let inner = app(m, OP_ITE, &[eq, v0, v1], u);
        let eq = m.mk_eq(x0, v1).unwrap();
        let ite = app(m, OP_ITE, &[eq, v2, inner], u);
        let mut from_ite = FuncInterp::new(1);
        from_ite.set_else(m, ite).unwrap();
        let interp = from_ite.get_interp(m).unwrap();
        out.push(format!(
            "from-ite {} interp {}",
            get_interp_text(m, &from_ite),
            show(m, interp)
        ));
        from_ite.compress(m).unwrap();
        out.push(format!(
            "from-ite compressed {}",
            get_interp_text(m, &from_ite)
        ));
        let x1 = m.mk_var(1, u);
        let first = m.mk_eq(x0, v0).unwrap();
        let second = m.mk_eq(v1, x1).unwrap();
        let condition = m.mk_and(&[first, second]).unwrap();
        let binary_ite = app(m, OP_ITE, &[condition, v2, v0], u);
        let mut binary = FuncInterp::new(2);
        binary.set_else(m, binary_ite).unwrap();
        binary.insert_entry(m, &[v1, v1], v0).unwrap();
        let interp = binary.get_interp(m).unwrap();
        out.push(format!(
            "binary {} interp {}",
            get_interp_text(m, &binary),
            show(m, interp)
        ));
        binary.compress(m).unwrap();
        out.push(format!(
            "binary compressed {} constant={}",
            get_interp_text(m, &binary),
            binary.is_constant(m)
        ));
        let (true_expr, false_expr) = (m.true_expr, m.false_expr);
        let mut predicate = FuncInterp::new(2);
        predicate.insert_new_entry(m, &[v0, v1], true_expr).unwrap();
        predicate
            .insert_new_entry(m, &[v1, v0], false_expr)
            .unwrap();
        predicate.insert_new_entry(m, &[v2, v2], true_expr).unwrap();
        predicate.set_else(m, false_expr).unwrap();
        let interp = predicate.get_interp(m).unwrap();
        out.push(format!("predicate interp {}", show(m, interp)));
        predicate.set_else(m, true_expr).unwrap();
        let interp = predicate.get_interp(m).unwrap();
        out.push(format!("predicate interp {}", show(m, interp)));
        let mut identity = FuncInterp::new(1);
        identity
            .insert_new_entry(m, &[true_expr], true_expr)
            .unwrap();
        identity.set_else(m, false_expr).unwrap();
        identity.compress(m).unwrap();
        out.push(format!("identity {}", get_interp_text(m, &identity)));
        let mut constant = FuncInterp::new(1);
        constant.insert_new_entry(m, &[v0], v1).unwrap();
        constant.insert_new_entry(m, &[v2], v1).unwrap();
        constant.set_else(m, v1).unwrap();
        out.push(format!("constant={}", constant.is_constant(m)));
        for interp in [
            &mut unary,
            &mut from_ite,
            &mut binary,
            &mut predicate,
            &mut identity,
            &mut constant,
        ] {
            interp.release(m).unwrap();
        }
        let refs: Vec<String> = values
            .iter()
            .map(|value| m.get_ref_count(*value).to_string())
            .collect();
        out.push(format!("refs {} asts={}", refs.join(" "), m.get_num_asts()));
        assert_section("func-interp", &out);
    }

    #[test]
    fn evaluates_completes_and_cleans_up_a_proto_model() {
        let mut out = Vec::new();
        let m = &mut mk_manager();
        let u = m.mk_sort("U");
        let f = mk_decl(m, "f", &[u], u);
        let g = mk_decl(m, "g", &[u, u], u);
        let p = mk_decl(m, "p", &[u], SORT_BOOL);
        let h = mk_decl(m, "h", &[u], u);
        let a = mk_const(m, "a", u);
        let b = mk_const(m, "b", u);
        let c = mk_const(m, "c", u);
        let k = mk_const(m, "k", u);
        let q = mk_const(m, "q", SORT_BOOL);
        let x = mk_const(m, "x", SORT_INT);
        mk_const(m, "y", SORT_INT);
        let mut model = ProtoModel::new(m);
        model.inc_ref();
        let v0 = model.get_fresh_value(m, u);
        let v1 = model.get_fresh_value(m, u);
        let fresh_int = model.get_fresh_value(m, SORT_INT);
        out.push(format!(
            "fresh {} {} int {}",
            show(m, v0),
            show(m, v1),
            show(m, fresh_int)
        ));
        let (v0, v1) = (v0.unwrap(), v1.unwrap());
        let some = model.get_some_value(m, u);
        let bools: Vec<String> = (0..4)
            .map(|_| {
                let value = model.get_some_value(m, SORT_BOOL);
                show(m, Some(value))
            })
            .collect();
        out.push(format!("some {} {}", show(m, Some(some)), bools.join(" ")));
        model.register_const(m, m.decls[a as usize], v0).unwrap();
        model.register_const(m, m.decls[b as usize], v1).unwrap();
        let mut f_interp = FuncInterp::new(1);
        f_interp.insert_new_entry(m, &[v0], v1).unwrap();
        model.register_func(m, f, f_interp).unwrap();
        let mut g_interp = FuncInterp::new(2);
        g_interp.insert_new_entry(m, &[v0, v1], v0).unwrap();
        g_interp.set_else(m, v1).unwrap();
        model.register_func(m, g, g_interp).unwrap();
        let eq = m.mk_eq(a, b).unwrap();
        let k_value = app(m, OP_ITE, &[eq, a, b], u);
        model
            .register_const(m, m.decls[k as usize], k_value)
            .unwrap();
        print_counts(&mut out, m, "built");
        print_model(&mut out, m, &model, &[u, SORT_INT]);
        let zero = m.mk_numeral(&Int::from(0));
        let fa = app(m, f, &[a], u);
        let fb = app(m, f, &[b], u);
        let fa_inner = app(m, f, &[a], u);
        let ffa = app(m, f, &[fa_inner], u);
        let gab = app(m, g, &[a, b], u);
        let gba = app(m, g, &[b, a], u);
        let gac = app(m, g, &[a, c], u);
        let pa = app(m, p, &[a], SORT_BOOL);
        let kb = m.mk_eq(k, b).unwrap();
        let ab = m.mk_eq(a, b).unwrap();
        let conjunction = m.mk_and(&[q, ab]).unwrap();
        let division = app(m, OP_IDIV, &[x, zero], SORT_INT);
        let two = m.mk_numeral(&Int::from(2));
        let modulo = app(m, OP_MOD, &[x, two], SORT_INT);
        let ha = app(m, h, &[a], u);
        let ca = m.mk_eq(c, a).unwrap();
        let fc = app(m, f, &[c], u);
        let hb = app(m, h, &[b], u);
        let ite = app(m, OP_ITE, &[ca, fc, hb], u);
        let terms = [
            fa,
            fb,
            ffa,
            gab,
            gba,
            gac,
            pa,
            k,
            kb,
            c,
            conjunction,
            division,
            modulo,
            ha,
            ite,
        ];
        print_evals(&mut out, m, &mut model, &terms);
        print_model(&mut out, m, &model, &[u, SORT_INT]);
        let aux_decl = mk_fresh_decl(m, "aux", &[u], u);
        let unused = mk_fresh_decl(m, "unused", &[u], u);
        let mut aux_interp = FuncInterp::new(1);
        aux_interp.set_else(m, v1).unwrap();
        model
            .register_aux_decl(m, aux_decl, Some(aux_interp))
            .unwrap();
        model
            .register_aux_decl(m, unused, Some(FuncInterp::new(1)))
            .unwrap();
        let mut h_interp = FuncInterp::new(1);
        let variable = m.mk_var(0, u);
        let h_else = app(m, aux_decl, &[variable], u);
        h_interp.set_else(m, h_else).unwrap();
        let h_aux = mk_fresh_decl(m, "h", &[u], u);
        model.reregister_decl(m, h, h_interp, h_aux).unwrap();
        model.register_func(m, p, FuncInterp::new(1)).unwrap();
        model.complete_partial_funcs(m, false).unwrap();
        print_counts(&mut out, m, "completed");
        print_model(&mut out, m, &model, &[u, SORT_INT]);
        model.cleanup(m).unwrap();
        print_counts(&mut out, m, "cleaned");
        print_model(&mut out, m, &model, &[u, SORT_INT]);
        model.compress(m).unwrap();
        model.freeze_universe(m, u);
        let is_finite = model.is_finite(m, u);
        let some = model.get_some_value(m, u);
        let fresh = model.get_fresh_value(m, u);
        let c_value = model.get_some_const_interp(m, m.decls[c as usize]);
        let q_value = model.get_some_const_interp(m, m.decls[q as usize]);
        out.push(format!(
            "finite={is_finite} some {} fresh {} const {} {}",
            show(m, Some(some)),
            show(m, fresh),
            show(m, Some(c_value)),
            show(m, Some(q_value))
        ));
        let mut made = model.mk_model(m).unwrap();
        made.inc_ref();
        print_counts(&mut out, m, "made");
        print_model(&mut out, m, &made, &[u, SORT_INT]);
        print_model(&mut out, m, &model, &[u, SORT_INT]);
        print_evals(&mut out, m, &mut made, &terms[..4]);
        model.dec_ref(m).unwrap();
        made.dec_ref(m).unwrap();
        print_counts(&mut out, m, "released");
        assert_section("proto-model", &out);
    }

    #[test]
    fn evaluates_divisions_by_zero_with_their_interpretations() {
        let mut out = Vec::new();
        let m = &mut mk_manager();
        let x = mk_const(m, "x", SORT_INT);
        let y = mk_const(m, "y", SORT_INT);
        let mut model = ProtoModel::new(m);
        model.inc_ref();
        let mut interp = FuncInterp::new(2);
        let seven = m.mk_numeral(&Int::from(7));
        interp.set_else(m, seven).unwrap();
        model.register_func(m, OP_IDIV0, interp).unwrap();
        let first = app(m, OP_IDIV, &[x, y], SORT_INT);
        let zero = m.mk_numeral(&Int::from(0));
        let second = app(m, OP_IDIV, &[x, zero], SORT_INT);
        let third = app(m, OP_MOD, &[x, y], SORT_INT);
        let five = m.mk_numeral(&Int::from(5));
        let zero = m.mk_numeral(&Int::from(0));
        let fourth = app(m, OP_MOD, &[five, zero], SORT_INT);
        print_evals(&mut out, m, &mut model, &[first, second, third, fourth]);
        print_model(&mut out, m, &model, &[SORT_INT]);
        model.dec_ref(m).unwrap();
        print_counts(&mut out, m, "released");
        assert_section("partial-theory", &out);
    }
}
