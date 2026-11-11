//! Ported from Z3 (src/smt/qi_queue.cpp, src/smt/smt_checker.cpp), MIT license, see
//! z3-license.txt, through `qi-queue.ts`. Instances found by E-matching wait here. Z3's default cost
//! is (+ weight generation): cheap instances are created at once, expensive ones only in the final
//! check, and the checker skips instances that the current assignment already satisfies.
//!
//! `QiQueue` and `Checker` keep the context, so (design/smt-core.md, "The context") the queue is a
//! struct held by the quantifier manager whose methods that reach the context are `impl Context`
//! methods named `qi_queue_<method>`. The checker only reads the context, except for `is_diseq`,
//! and nothing it calls reaches the checker, so its methods take the context, and the queue lends
//! it out for each run (`Context::qi_queue_checker`).

use std::collections::HashMap;
use std::mem;

use crate::core::ast::{
    AstManager, Expr, KIND_APP, KIND_VAR, OP_AND, OP_EQ, OP_FALSE, OP_ITE, OP_NOT, OP_OR, OP_TRUE,
};
use crate::core::context::Context;
use crate::core::enode::EnodeId;
use crate::core::mam_compiler::set_at;
use crate::core::ref_vector::RefVector;
use crate::core::rewriter_tpl::MAX_RECURSION_DEPTH;
use crate::core::var_subst::VarSubst;
use crate::util::error::SmtError;
use crate::util::lbool::LBool;

const EAGER_COST_THRESHOLD: f64 = 10.0;
const LAZY_COST_THRESHOLD: f64 = 20.0;

#[derive(Clone, Debug)]
struct Entry {
    quantifier: Expr,
    bindings: Vec<EnodeId>,
    cost: f64,
    generation: u32,
    is_instantiated: bool,
}

/// A copy of the array with room for the index, at least twice as long.
fn grow(array: &mut Vec<i32>, index: usize) {
    let length = (2 * array.len()).max(index + 1);
    array.resize(length, 0);
}

/// smt::checker: evaluates a quantifier body under bindings with the E-graph and the assignment.
#[derive(Clone, Debug, Default)]
pub struct Checker {
    bindings: Vec<EnodeId>,
    // The caches of a run, by expression, which hold an entry for the run whose stamp it has. So a
    // run starts with them empty without clearing them.
    stamp: i32,
    check_stamps: Vec<i32>,
    check_results: Vec<i32>,
    enode_stamps: Vec<i32>,
    enode_results: Vec<Option<EnodeId>>,
    // The ptr_buffer of each level of get_enode_eq_to_core, which Z3 keeps on the stack.
    arg_buffers: Vec<Vec<EnodeId>>,
    arg_depth: usize,
}

impl Checker {
    pub fn is_sat(
        &mut self,
        context: &mut Context,
        body: Expr,
        bindings: &[EnodeId],
    ) -> Result<bool, SmtError> {
        self.run(context, body, bindings, true)
    }

    pub fn is_unsat(
        &mut self,
        context: &mut Context,
        body: Expr,
        bindings: &[EnodeId],
    ) -> Result<bool, SmtError> {
        self.run(context, body, bindings, false)
    }

    fn run(
        &mut self,
        context: &mut Context,
        body: Expr,
        bindings: &[EnodeId],
        is_true: bool,
    ) -> Result<bool, SmtError> {
        self.bindings.clear();
        self.bindings.extend_from_slice(bindings);
        self.stamp = self.stamp.wrapping_add(1);
        self.check(context, body, 0, is_true)
    }

    fn check(
        &mut self,
        context: &mut Context,
        expr: Expr,
        depth: u32,
        is_true: bool,
    ) -> Result<bool, SmtError> {
        let key = expr as usize * 2 + usize::from(is_true);
        if key >= self.check_stamps.len() {
            grow(&mut self.check_stamps, key);
            grow(&mut self.check_results, key);
        }
        if self.check_stamps[key] == self.stamp {
            return Ok(self.check_results[key] == 1);
        }
        let result = self.check_core(context, expr, depth, is_true)?;
        self.check_stamps[key] = self.stamp;
        self.check_results[key] = i32::from(result);
        Ok(result)
    }

    fn is_assigned(&self, context: &Context, expr: Expr, is_true: bool) -> Result<bool, SmtError> {
        let value = if context.is_b_internalized(expr) {
            context.get_bool_var_assignment(context.get_bool_var(expr)?)
        } else {
            LBool::Undef
        };
        Ok(value != LBool::Undef && is_true == (value == LBool::True))
    }

    fn check_any(
        &mut self,
        context: &mut Context,
        expr: Expr,
        depth: u32,
        is_true: bool,
    ) -> Result<bool, SmtError> {
        for index in 0..context.m.get_num_args(expr) {
            let arg = context.m.get_arg(expr, index);
            if self.check(context, arg, depth, is_true)? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn check_all(
        &mut self,
        context: &mut Context,
        expr: Expr,
        depth: u32,
        is_true: bool,
    ) -> Result<bool, SmtError> {
        for index in 0..context.m.get_num_args(expr) {
            let arg = context.m.get_arg(expr, index);
            if !self.check(context, arg, depth, is_true)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn check_core(
        &mut self,
        context: &mut Context,
        expr: Expr,
        depth: u32,
        is_true: bool,
    ) -> Result<bool, SmtError> {
        if depth > 600 {
            return Ok(false);
        }
        if context.is_b_internalized(expr) && context.is_relevant(expr) {
            return self.is_assigned(context, expr, is_true);
        }
        if context.m.kinds[expr as usize] != KIND_APP {
            return Ok(false);
        }
        let next = depth + 1;
        match context.m.get_op(expr) {
            OP_TRUE => return Ok(is_true),
            OP_FALSE => return Ok(!is_true),
            OP_NOT => {
                let arg = context.m.get_arg(expr, 0);
                return self.check(context, arg, next, !is_true);
            }
            OP_OR => {
                return if is_true {
                    self.check_any(context, expr, next, true)
                } else {
                    self.check_all(context, expr, next, false)
                };
            }
            OP_AND => {
                return if is_true {
                    self.check_all(context, expr, next, true)
                } else {
                    self.check_any(context, expr, next, false)
                };
            }
            OP_EQ => {
                let first = context.m.get_arg(expr, 0);
                let second = context.m.get_arg(expr, 1);
                if !context.m.is_bool(first) {
                    let lhs = self.get_enode_eq_to(context, first)?;
                    let rhs = self.get_enode_eq_to(context, second)?;
                    let (Some(lhs), Some(rhs)) = (lhs, rhs) else {
                        return Ok(false);
                    };
                    if !context.is_relevant(context.node(lhs).owner)
                        || !context.is_relevant(context.node(rhs).owner)
                    {
                        return Ok(false);
                    }
                    return if is_true {
                        Ok(context.root(lhs) == context.root(rhs))
                    } else {
                        context.is_diseq(lhs, rhs)
                    };
                }
                return Ok((self.check(context, first, next, true)?
                    && self.check(context, second, next, is_true)?)
                    || (self.check(context, first, next, false)?
                        && self.check(context, second, next, !is_true)?));
            }
            OP_ITE => {
                let condition = context.m.get_arg(expr, 0);
                let atom = if context.m.is_not(condition) {
                    context.m.get_arg(condition, 0)
                } else {
                    condition
                };
                let then_branch = context.m.get_arg(expr, 1);
                let else_branch = context.m.get_arg(expr, 2);
                if condition != context.m.false_expr
                    && (!context.is_b_internalized(atom) || !context.is_relevant(condition))
                {
                    return Ok(self.check(context, then_branch, next, is_true)?
                        && self.check(context, else_branch, next, is_true)?);
                }
                let value = context.get_assignment(context.get_literal(condition)?);
                if value == LBool::Undef {
                    return Ok(false);
                }
                let branch = if value == LBool::True {
                    then_branch
                } else {
                    else_branch
                };
                return self.check(context, branch, next, is_true);
            }
            _ => {}
        }
        let node = self.get_enode_eq_to(context, expr)?;
        let Some(node) = node else {
            return Ok(false);
        };
        let owner = context.node(node).owner;
        if !context.m.is_bool(owner) || !context.is_relevant(owner) {
            return Ok(false);
        }
        self.is_assigned(context, owner, is_true)
    }

    /// get_enode_eq_to: the relevant term of the E-graph that the expression equals by
    /// congruence. It recurses on the term, which the TypeScript answers unknown on when the stack
    /// overflows, so it stops past `MAX_RECURSION_DEPTH`.
    fn get_enode_eq_to(
        &mut self,
        context: &Context,
        expr: Expr,
    ) -> Result<Option<EnodeId>, SmtError> {
        let m = &context.m;
        if m.kinds[expr as usize] == KIND_VAR {
            let index = m.values[expr as usize] as usize;
            return Ok(if index < self.bindings.len() {
                Some(self.bindings[self.bindings.len() - index - 1])
            } else {
                None
            });
        }
        let existing = context.get_enode(expr);
        if let Some(existing) = existing
            && context.is_relevant(expr)
        {
            return Ok(Some(existing));
        }
        if m.kinds[expr as usize] != KIND_APP || m.get_num_args(expr) == 0 {
            return Ok(None);
        }
        if expr as usize >= self.enode_stamps.len() {
            grow(&mut self.enode_stamps, expr as usize);
        }
        if self.enode_stamps[expr as usize] == self.stamp {
            return Ok(self.enode_results.get(expr as usize).copied().flatten());
        }
        let depth = self.arg_depth;
        if depth >= MAX_RECURSION_DEPTH {
            return Err(SmtError::Unsupported(
                "the checker's term nests too deeply".into(),
            ));
        }
        if depth == self.arg_buffers.len() {
            self.arg_buffers.push(Vec::new());
        }
        self.arg_buffers[depth].clear();
        self.arg_depth = depth + 1;
        for index in 0..m.get_num_args(expr) {
            let arg = m.get_arg(expr, index);
            let node = match self.get_enode_eq_to(context, arg) {
                Ok(node) => node,
                Err(error) => {
                    self.arg_depth = depth;
                    return Err(error);
                }
            };
            let Some(node) = node else {
                self.arg_depth = depth;
                self.enode_stamps[expr as usize] = self.stamp;
                set_at(&mut self.enode_results, expr as usize, None, None);
                return Ok(None);
            };
            self.arg_buffers[depth].push(node);
        }
        self.arg_depth = depth;
        let found = context.find_congruent(m.decls[expr as usize], &self.arg_buffers[depth]);
        let result = found.filter(|found| context.is_relevant(context.node(*found).owner));
        self.enode_stamps[expr as usize] = self.stamp;
        set_at(&mut self.enode_results, expr as usize, result, None);
        Ok(result)
    }
}

#[derive(Clone, Debug)]
pub struct QiQueue {
    new_entries: Vec<Entry>,
    delayed_entries: Vec<Entry>,
    instantiated_trail: Vec<usize>,
    scopes: Vec<usize>,
    checker: Checker,
    // cached_var_subst: each instance by its quantifier and bindings, which the queue holds with
    // them until the next search. instance_refs lists the quantifier, the bindings and the
    // instance of each. instance_starts holds where each instance starts there, and instance_next
    // the earlier instance of the same hash, or None. instances maps a hash of the key to its last
    // instance.
    subst: VarSubst,
    instances: HashMap<i32, usize>,
    instance_refs: Vec<Expr>,
    instance_starts: Vec<usize>,
    instance_next: Vec<Option<usize>>,
    binding_owners: Vec<Expr>,
    // m_instances: the lemmas, which the queue holds until their scope is popped.
    lemmas: RefVector,
    pub num_instances: u32,
}

impl QiQueue {
    pub fn new(m: &AstManager) -> QiQueue {
        QiQueue {
            new_entries: Vec::new(),
            delayed_entries: Vec::new(),
            instantiated_trail: Vec::new(),
            scopes: Vec::new(),
            checker: Checker::default(),
            subst: VarSubst::new(m, true),
            instances: HashMap::new(),
            instance_refs: Vec::new(),
            instance_starts: Vec::new(),
            instance_next: Vec::new(),
            binding_owners: Vec::new(),
            lemmas: RefVector::new(),
            num_instances: 0,
        }
    }

    fn get_instance(
        &mut self,
        m: &mut AstManager,
        quantifier: Expr,
        bindings: &[Expr],
    ) -> Result<Expr, SmtError> {
        let mut hash = quantifier;
        for binding in bindings {
            hash = hash
                .wrapping_mul(0x9e37_79b1_u32 as i32)
                .wrapping_add(*binding);
        }
        let last = self.instances.get(&hash).copied();
        let mut entry = last;
        while let Some(current) = entry {
            let start = self.instance_starts[current];
            let refs = &self.instance_refs;
            let mut is_same = refs[start] == quantifier;
            let mut index = 0;
            while index < bindings.len() && is_same {
                is_same = refs[start + 1 + index] == bindings[index];
                index += 1;
            }
            if is_same {
                return Ok(refs[start + 1 + bindings.len()]);
            }
            entry = self.instance_next[current];
        }
        let body = m.get_quantifier(quantifier)?.body;
        let instance = self.subst.apply(m, body, bindings)?;
        self.instances.insert(hash, self.instance_starts.len());
        self.instance_starts.push(self.instance_refs.len());
        self.instance_next.push(last);
        m.inc_ref(quantifier);
        self.instance_refs.push(quantifier);
        for binding in bindings {
            m.inc_ref(*binding);
            self.instance_refs.push(*binding);
        }
        self.instance_refs.push(instance);
        Ok(instance)
    }

    pub fn has_work(&self) -> bool {
        !self.new_entries.is_empty()
    }

    pub fn insert(
        &mut self,
        m: &AstManager,
        quantifier: Expr,
        bindings: Vec<EnodeId>,
        generation: u32,
    ) -> Result<(), SmtError> {
        let weight = m.get_quantifier(quantifier)?.weight;
        self.new_entries.push(Entry {
            quantifier,
            bindings,
            cost: f64::from(weight) + f64::from(generation),
            generation,
            is_instantiated: false,
        });
        Ok(())
    }

    pub fn push(&mut self) {
        self.scopes.push(self.delayed_entries.len());
        self.scopes.push(self.instantiated_trail.len());
        self.scopes.push(self.lemmas.len());
    }

    pub fn pop(&mut self, m: &mut AstManager, num_scopes: u32) -> Result<(), SmtError> {
        let offset = self.scopes.len() - num_scopes as usize * 3;
        let delayed_limit = self.scopes[offset];
        let trail_limit = self.scopes[offset + 1];
        for index in trail_limit..self.instantiated_trail.len() {
            let entry = self.instantiated_trail[index];
            self.delayed_entries[entry].is_instantiated = false;
        }
        self.instantiated_trail.truncate(trail_limit);
        self.delayed_entries.truncate(delayed_limit);
        self.lemmas.shrink(m, self.scopes[offset + 2])?;
        self.new_entries = Vec::new();
        self.scopes.truncate(offset);
        Ok(())
    }

    pub fn init_search_eh(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        for expr in mem::take(&mut self.instance_refs) {
            m.dec_ref(expr)?;
        }
        self.instance_starts = Vec::new();
        self.instance_next = Vec::new();
        self.instances.clear();
        self.new_entries = Vec::new();
        Ok(())
    }
}

impl Context {
    /// A run of the checker, which the queue lends out while it runs.
    fn qi_queue_checker(
        &mut self,
        quantifier: Expr,
        bindings: &[EnodeId],
        is_sat: bool,
    ) -> Result<bool, SmtError> {
        let body = self.m.get_quantifier(quantifier)?.body;
        let mut checker = mem::take(&mut self.qmanager.qi_queue.checker);
        let result = if is_sat {
            checker.is_sat(self, body, bindings)
        } else {
            checker.is_unsat(self, body, bindings)
        };
        self.qmanager.qi_queue.checker = checker;
        result
    }

    pub fn qi_queue_instantiate(&mut self) -> Result<(), SmtError> {
        let entries = mem::take(&mut self.qmanager.qi_queue.new_entries);
        let mut since_last_check = 0;
        for entry in entries {
            if entry.cost <= EAGER_COST_THRESHOLD
                || self.qi_queue_checker(entry.quantifier, &entry.bindings, false)?
            {
                self.qi_queue_instantiate_entry(&entry)?;
            } else {
                self.qmanager.qi_queue.delayed_entries.push(entry);
            }
            let since = since_last_check;
            since_last_check += 1;
            if since > 100 {
                if self.check_canceled() {
                    break;
                }
                since_last_check = 0;
            }
        }
        Ok(())
    }

    /// instantiate_entry. The caller marks a delayed entry as instantiated when the context is
    /// consistent, as the TypeScript does here first.
    fn qi_queue_instantiate_entry(&mut self, entry: &Entry) -> Result<(), SmtError> {
        if self.is_inconsistent() {
            return Ok(());
        }
        let weight = self.m.get_quantifier(entry.quantifier)?.weight;
        if self.qi_queue_checker(entry.quantifier, &entry.bindings, true)? {
            return Ok(());
        }
        // The bindings' expressions, which Z3 writes into the buffer that m_subst returns.
        let mut owners = mem::take(&mut self.qmanager.qi_queue.binding_owners);
        owners.clear();
        for binding in &entry.bindings {
            owners.push(self.node(*binding).owner);
        }
        let substituted =
            self.qmanager
                .qi_queue
                .get_instance(&mut self.m, entry.quantifier, &owners);
        self.qmanager.qi_queue.binding_owners = owners;
        let substituted = substituted?;
        self.m.inc_ref(substituted);
        let instance = self.rewriter.rewrite(&mut self.m, substituted)?;
        if instance != self.m.true_expr {
            let negated = self.m.mk_not(entry.quantifier)?;
            let mut disjuncts = vec![negated];
            if self.m.get_op(instance) == OP_OR {
                self.m.push_args(instance, &mut disjuncts);
            } else if instance != self.m.false_expr {
                disjuncts.push(instance);
            }
            let lemma = self.m.mk_or(&disjuncts)?;
            self.qmanager.qi_queue.lemmas.push(&mut self.m, lemma);
            self.qmanager.qi_queue.num_instances += 1;
            let new_generation = if weight > 0 || entry.cost > 0.0 {
                entry.cost.trunc()
            } else {
                f64::from(entry.generation + 1).max(entry.cost.trunc())
            };
            self.internalize_assertion(lemma, new_generation as u32)?;
        }
        self.m.dec_ref(instance)?;
        self.m.dec_ref(substituted)
    }

    pub fn qi_queue_final_check_eh(&mut self) -> Result<bool, SmtError> {
        let mut result = true;
        let mut index = 0;
        while index < self.qmanager.qi_queue.delayed_entries.len() {
            let entry = &self.qmanager.qi_queue.delayed_entries[index];
            if entry.is_instantiated || entry.cost > LAZY_COST_THRESHOLD {
                index += 1;
                continue;
            }
            let entry = entry.clone();
            result = false;
            self.qmanager.qi_queue.instantiated_trail.push(index);
            if !self.is_inconsistent() {
                self.qmanager.qi_queue.delayed_entries[index].is_instantiated = true;
            }
            self.qi_queue_instantiate_entry(&entry)?;
            if self.check_canceled() {
                break;
            }
            index += 1;
        }
        Ok(result)
    }
}
