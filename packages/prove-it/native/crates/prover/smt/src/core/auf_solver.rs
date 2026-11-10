//! Ported from Z3 (src/smt/smt_model_finder.cpp), MIT license, through `auf-solver.ts`. The
//! instantiation sets and the AUF solver of the model finder: the solver groups the argument
//! positions and variables that must share an instantiation set, and each group gets a projection
//! function that maps any value to the value of a term in its set.
//!
//! # Design
//!
//! - The TypeScript `Node`s link to each other (`find`, the avoid sets), so they are an arena owned
//!   by the solver, `nodes`, indexed by a [`NodeId`]; a node's methods are the solver's, taking the
//!   node's id. Nodes are never removed before `reset`, so an id never aliases a newer node.
//! - `m_A_f_is` is an `ObjMap` in Z3's slot order, hashed like `pair_hash` of the declaration and
//!   the position. The TypeScript keys it by `decl * 2^20 + index`, which does not fit a `u32`, so
//!   here it is keyed by the node's id (unique per declaration and position) with the same hash,
//!   which gives the same slots, and `afi_index` finds the node of a declaration and position.
//! - The TypeScript's `eval` never returns `null`, so its tests for a `null` value are left out.
//! - The rewriter that the TypeScript's model finder shares with the solver and the quantifier
//!   analyzer is the solver's `rewriter`.

use std::collections::HashMap;

use prove_num::Int;

use crate::core::ast::{
    AstManager, Decl, Expr, OP_ITE, OP_LT, SORT_BOOL, SORT_INT, SmtSymbol, Sort, is_arith_sort,
};
use crate::core::proto_model::{FuncInterp, ProtoModel, ProtoModelRef};
use crate::core::ref_vector::RefVector;
use crate::core::rewriter::Rewriter;
use crate::util::error::SmtError;
use crate::util::hash::combine_hash;
use crate::util::hashtable::{ObjHashtable, ObjMap};
use crate::util::random_gen::RandomGen;

pub type NodeId = u32;

/// instantiation_set: the S_{k,j} sets of the paper, with the generation of each term. The set
/// holds its terms.
#[derive(Clone, Default)]
pub struct InstantiationSet {
    /// The generation of each term, keyed by the term, hashed by its hash.
    pub elems: ObjMap<u32>,
    /// A term of each value, keyed by the value.
    pub inv: ObjMap<Expr>,
}

impl InstantiationSet {
    pub fn new() -> InstantiationSet {
        InstantiationSet::default()
    }

    pub fn insert(&mut self, m: &mut AstManager, expr: Expr, generation: u32) {
        if self
            .elems
            .contains_key(expr as u32, m.hashes[expr as usize])
            || m.contains_model_value(expr)
        {
            return;
        }
        m.inc_ref(expr);
        self.elems
            .insert(expr as u32, m.hashes[expr as usize], generation);
    }

    pub fn remove(&mut self, m: &mut AstManager, expr: Expr) -> Result<(), SmtError> {
        self.elems.remove(expr as u32, m.hashes[expr as usize]);
        m.dec_ref(expr)
    }

    /// ~instantiation_set.
    pub fn release(&self, m: &mut AstManager) -> Result<(), SmtError> {
        for expr in self.elems.keys() {
            m.dec_ref(expr as Expr)?;
        }
        Ok(())
    }

    /// The terms, in slot order.
    pub fn get_elems(&self) -> Vec<(Expr, u32)> {
        self.elems
            .iter()
            .map(|(expr, generation)| (expr as Expr, *generation))
            .collect()
    }

    pub fn get_inv(&self, m: &AstManager, value: Expr, model: &ProtoModel) -> Option<Expr> {
        if let Some(term) = self.inv.get(value as u32, m.hashes[value as usize]) {
            return Some(*term);
        }
        self.inv
            .iter()
            .find(|(key, _)| model.are_equal(*key as Expr, value))
            .map(|(_, term)| *term)
    }

    pub fn get_generation(&self, m: &AstManager, term: Expr) -> u32 {
        self.elems
            .get(term as u32, m.hashes[term as usize])
            .copied()
            .unwrap_or(0)
    }

    pub fn mk_inverse(
        &mut self,
        m: &mut AstManager,
        mut evaluate: impl FnMut(&mut AstManager, Expr) -> Result<Expr, SmtError>,
    ) -> Result<(), SmtError> {
        for (term, generation) in self.get_elems() {
            let value = evaluate(m, term)?;
            let hash = m.hashes[value as usize];
            let old = self.inv.get(value as u32, hash).copied();
            let is_better = match old {
                None => true,
                Some(old) => {
                    generation
                        < self
                            .elems
                            .get(old as u32, m.hashes[old as usize])
                            .copied()
                            .unwrap_or(0)
                }
            };
            if is_better {
                self.inv.insert(value as u32, hash, term);
            }
        }
        Ok(())
    }
}

/// node: a set of argument positions and variables that share an instantiation set.
#[derive(Clone)]
pub struct Node {
    pub id: NodeId,
    pub sort: Sort,
    find: Option<NodeId>,
    eqc_size: u32,
    is_mono: bool,
    avoid_set: Vec<NodeId>,
    exceptions: Vec<Expr>,
    set: Option<InstantiationSet>,
    else_expr: Option<Expr>,
    proj: Option<Decl>,
}

impl Node {
    fn new(id: NodeId, sort: Sort) -> Node {
        Node {
            id,
            sort,
            find: None,
            eqc_size: 1,
            is_mono: false,
            avoid_set: Vec::new(),
            exceptions: Vec::new(),
            set: None,
            else_expr: None,
            proj: None,
        }
    }

    pub fn is_root(&self) -> bool {
        self.find.is_none()
    }
}

// appendNew: the items of source that target lacks join it.
fn append_new<T: PartialEq + Copy>(target: &mut Vec<T>, source: &[T]) {
    for item in source {
        if !target.contains(item) {
            target.push(*item);
        }
    }
}

/// auf_solver: the "almost uninterpreted fragment" of the paper.
pub struct AufSolver {
    nodes: Vec<Node>,
    // Only looked up, never iterated.
    uvars: HashMap<(Expr, u32), NodeId>,
    // m_A_f_is, in Z3's slot order: the declaration of each node (module header), and its index.
    a_f_is: ObjMap<Decl>,
    afi_index: HashMap<(Decl, u32), NodeId>,
    // Only looked up, never iterated.
    sort2k: HashMap<Sort, Expr>,
    // m_ks, the range of m_sort2k.
    ks: RefVector,
    model: Option<ProtoModelRef>,
    // m_eval_cache for each model completion flag, and m_eval_cache_range, which holds the
    // results. Only looked up, never iterated.
    eval_cache: [HashMap<Expr, Expr>; 2],
    eval_cache_range: RefVector,
    root_nodes: Vec<NodeId>,
    /// The constraints of the last model, which the model finder asserts at the next restart.
    pub new_constraints: Vec<Expr>,
    // m_rand, seeded with the steps the resource limit counted before the solver was made, which
    // then counts one more.
    random: RandomGen,
    pub rewriter: Rewriter,
}

impl AufSolver {
    pub fn new(m: &mut AstManager, rewriter: Rewriter) -> AufSolver {
        let random = RandomGen::new(m.limit.count() as u32);
        m.limit.inc();
        AufSolver {
            nodes: Vec::new(),
            uvars: HashMap::new(),
            a_f_is: ObjMap::new(),
            afi_index: HashMap::new(),
            sort2k: HashMap::new(),
            ks: RefVector::new(),
            model: None,
            eval_cache: [HashMap::new(), HashMap::new()],
            eval_cache_range: RefVector::new(),
            root_nodes: Vec::new(),
            new_constraints: Vec::new(),
            random,
            rewriter,
        }
    }

    pub fn reset(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        for node in &self.nodes {
            if let Some(set) = &node.set {
                set.release(m)?;
            }
        }
        self.nodes = Vec::new();
        self.uvars.clear();
        self.a_f_is.clear();
        self.afi_index.clear();
        self.root_nodes = Vec::new();
        self.sort2k.clear();
        self.ks.reset(m)
    }

    pub fn set_model(&mut self, m: &mut AstManager, model: &ProtoModelRef) -> Result<(), SmtError> {
        self.reset_eval_cache(m)?;
        self.model = Some(model.clone());
        Ok(())
    }

    fn get_model(&self) -> Result<ProtoModelRef, SmtError> {
        self.model
            .clone()
            .ok_or_else(|| SmtError::Invariant("the model finder has no model".into()))
    }

    fn reset_eval_cache(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.eval_cache[0].clear();
        self.eval_cache[1].clear();
        self.eval_cache_range.reset(m)
    }

    // Nodes.

    pub fn node(&self, node: NodeId) -> &Node {
        &self.nodes[node as usize]
    }

    pub fn get_root(&self, node: NodeId) -> NodeId {
        let mut current = node;
        while let Some(next) = self.nodes[current as usize].find {
            current = next;
        }
        current
    }

    pub fn merge(&mut self, node: NodeId, other: NodeId) {
        let mut first = self.get_root(node);
        let mut second = self.get_root(other);
        if first == second {
            return;
        }
        if self.nodes[first as usize].eqc_size > self.nodes[second as usize].eqc_size {
            std::mem::swap(&mut first, &mut second);
        }
        let first_node = &mut self.nodes[first as usize];
        first_node.find = Some(second);
        let eqc_size = first_node.eqc_size;
        let is_mono = first_node.is_mono;
        let avoid_set = first_node.avoid_set.clone();
        let exceptions = first_node.exceptions.clone();
        let second_node = &mut self.nodes[second as usize];
        second_node.eqc_size += eqc_size;
        second_node.is_mono = second_node.is_mono || is_mono;
        append_new(&mut second_node.avoid_set, &avoid_set);
        append_new(&mut second_node.exceptions, &exceptions);
    }

    pub fn insert_avoid(&mut self, node: NodeId, avoid: NodeId) {
        let root = self.get_root(node) as usize;
        if !self.nodes[root].avoid_set.contains(&avoid) {
            self.nodes[root].avoid_set.push(avoid);
        }
    }

    pub fn insert_exception(&mut self, node: NodeId, expr: Expr) {
        let root = self.get_root(node) as usize;
        if !self.nodes[root].exceptions.contains(&expr) {
            self.nodes[root].exceptions.push(expr);
        }
    }

    pub fn set_mono_proj(&mut self, node: NodeId) {
        let root = self.get_root(node) as usize;
        self.nodes[root].is_mono = true;
    }

    pub fn is_mono_proj(&self, node: NodeId) -> bool {
        self.nodes[self.get_root(node) as usize].is_mono
    }

    /// Only closed terms join the set.
    pub fn insert(&mut self, m: &mut AstManager, node: NodeId, expr: Expr, generation: u32) {
        if !m.is_ground(expr) {
            return;
        }
        let root = self.get_root(node) as usize;
        if let Some(set) = self.nodes[root].set.as_mut() {
            set.insert(m, expr, generation);
        }
    }

    pub fn get_instantiation_set(&self, node: NodeId) -> Result<&InstantiationSet, SmtError> {
        self.nodes[self.get_root(node) as usize]
            .set
            .as_ref()
            .ok_or_else(|| SmtError::Invariant("the instantiation set was not created".into()))
    }

    fn get_instantiation_set_mut(
        &mut self,
        node: NodeId,
    ) -> Result<&mut InstantiationSet, SmtError> {
        let root = self.get_root(node) as usize;
        self.nodes[root]
            .set
            .as_mut()
            .ok_or_else(|| SmtError::Invariant("the instantiation set was not created".into()))
    }

    fn get_exceptions(&self, node: NodeId) -> Vec<Expr> {
        self.nodes[self.get_root(node) as usize].exceptions.clone()
    }

    fn get_avoid_set(&self, node: NodeId) -> Vec<NodeId> {
        self.nodes[self.get_root(node) as usize].avoid_set.clone()
    }

    fn set_else(&mut self, node: NodeId, expr: Expr) {
        let root = self.get_root(node) as usize;
        self.nodes[root].else_expr = Some(expr);
    }

    fn get_else(&self, node: NodeId) -> Option<Expr> {
        self.nodes[self.get_root(node) as usize].else_expr
    }

    fn set_proj(&mut self, node: NodeId, decl: Decl) {
        let root = self.get_root(node) as usize;
        self.nodes[root].proj = Some(decl);
    }

    pub fn get_proj(&self, node: NodeId) -> Option<Decl> {
        self.nodes[self.get_root(node) as usize].proj
    }

    // The solver.

    fn mk_node(&mut self, sort: Sort) -> NodeId {
        let id = self.nodes.len() as NodeId;
        self.nodes.push(Node::new(id, sort));
        id
    }

    pub fn get_uvar(
        &mut self,
        m: &AstManager,
        quantifier: Expr,
        index: u32,
    ) -> Result<NodeId, SmtError> {
        if let Some(node) = self.uvars.get(&(quantifier, index)) {
            return Ok(*node);
        }
        let sorts = &m.get_quantifier(quantifier)?.sorts;
        let sort = sorts
            .len()
            .checked_sub(index as usize + 1)
            .map(|position| sorts[position])
            .ok_or_else(|| SmtError::Invariant("the variable is not bound".into()))?;
        let node = self.mk_node(sort);
        self.uvars.insert((quantifier, index), node);
        Ok(node)
    }

    pub fn get_a_f_i(&mut self, m: &AstManager, decl: Decl, index: u32) -> NodeId {
        if let Some(node) = self.afi_index.get(&(decl, index)) {
            return *node;
        }
        let node = self.mk_node(m.func_decls[decl as usize].domain[index as usize]);
        self.afi_index.insert((decl, index), node);
        self.a_f_is
            .insert(node, combine_hash(m.get_decl_hash(decl), index), decl);
        node
    }

    pub fn has_uvar(&self, quantifier: Expr, index: u32) -> bool {
        self.uvars.contains_key(&(quantifier, index))
    }

    pub fn get_uvar_inst_set(
        &self,
        quantifier: Expr,
        index: u32,
    ) -> Result<Option<&InstantiationSet>, SmtError> {
        match self.uvars.get(&(quantifier, index)) {
            None => Ok(None),
            Some(node) => self.get_instantiation_set(*node).map(Some),
        }
    }

    pub fn mk_instantiation_sets(&mut self) {
        for node in &mut self.nodes {
            if node.is_root() {
                node.set = Some(InstantiationSet::new());
            }
        }
    }

    // cleanup_instantiation_sets: drops the terms that do not evaluate to values.
    fn cleanup_instantiation_sets(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        for index in 0..self.nodes.len() {
            if !self.nodes[index].is_root() {
                continue;
            }
            let node = index as NodeId;
            let terms = self.get_instantiation_set(node)?.get_elems();
            let mut to_delete = Vec::new();
            for (term, _) in terms {
                let value = self.eval(m, term, true)?;
                if !m.is_unique_value(value) {
                    to_delete.push(term);
                }
            }
            for term in to_delete {
                self.get_instantiation_set_mut(node)?.remove(m, term)?;
            }
            self.reset_eval_cache(m)?;
        }
        Ok(())
    }

    pub fn eval(
        &mut self,
        m: &mut AstManager,
        expr: Expr,
        is_model_completion: bool,
    ) -> Result<Expr, SmtError> {
        let cache_index = usize::from(is_model_completion);
        if let Some(cached) = self.eval_cache[cache_index].get(&expr) {
            return Ok(*cached);
        }
        let result = self
            .get_model()?
            .borrow_mut()
            .eval(m, expr, is_model_completion)?;
        self.eval_cache[cache_index].insert(expr, result);
        self.eval_cache_range.push_owned(result);
        Ok(result)
    }

    fn collect_exceptions_values(
        &mut self,
        m: &mut AstManager,
        node: NodeId,
    ) -> Result<Vec<Expr>, SmtError> {
        let mut result = Vec::new();
        for expr in self.get_exceptions(node) {
            result.push(self.eval(m, expr, true)?);
        }
        for avoid in self.get_avoid_set(node) {
            let root = self.get_root(avoid);
            if let Some(else_expr) = self.get_else(root)
                && !self.is_mono_proj(root)
            {
                result.push(self.eval(m, else_expr, true)?);
            }
        }
        Ok(result)
    }

    fn are_distinct(m: &AstManager, first: Expr, second: Expr) -> bool {
        first != second && m.is_unique_value(first) && m.is_unique_value(second)
    }

    // pick_instance_diff_exceptions: the term of least generation whose value differs from every
    // exception.
    fn pick_instance_diff_exceptions(
        &mut self,
        m: &mut AstManager,
        node: NodeId,
        exception_values: &[Expr],
    ) -> Result<Option<Expr>, SmtError> {
        let mut result: Option<(Expr, u32)> = None;
        for (term, generation) in self.get_instantiation_set(node)?.get_elems() {
            let value = self.eval(m, term, true)?;
            let is_found = exception_values
                .iter()
                .any(|other| !AufSolver::are_distinct(m, value, *other));
            if !is_found && result.is_none_or(|(_, best)| generation < best) {
                result = Some((term, generation));
            }
        }
        Ok(result.map(|(term, _)| term))
    }

    // Uninterpreted sorts are not assumed infinite in benchmarks with quantifiers.
    fn is_infinite(sort: Sort) -> bool {
        is_arith_sort(sort)
    }

    fn get_k_for(&mut self, m: &mut AstManager, sort: Sort) -> Result<Expr, SmtError> {
        if let Some(existing) = self.sort2k.get(&sort) {
            return Ok(*existing);
        }
        let created = m.mk_fresh_const(Some(&SmtSymbol::Name("k".into())), sort)?;
        let decl = m.decls[created as usize];
        self.get_model()?
            .borrow_mut()
            .register_aux_decl(m, decl, None)?;
        self.sort2k.insert(sort, created);
        self.ks.push(m, created);
        Ok(created)
    }

    fn get_k_interp(&mut self, m: &mut AstManager, k: Expr) -> Result<Option<Expr>, SmtError> {
        let model = self.get_model()?;
        let mut model = model.borrow_mut();
        let decl = m.decls[k as usize];
        if let Some(existing) = model.get_const_interp(m, decl) {
            return Ok(Some(existing));
        }
        let sort = m.sorts[k as usize];
        let Some(fresh) = model.get_fresh_value(m, sort) else {
            return Ok(None);
        };
        model.register_const(m, decl, fresh)?;
        Ok(Some(fresh))
    }

    fn assert_k_diseq_exceptions(
        &mut self,
        m: &mut AstManager,
        k: Expr,
        exceptions: &[Expr],
    ) -> Result<bool, SmtError> {
        let Some(k_value) = self.get_k_interp(m, k)? else {
            return Ok(false);
        };
        for exception in exceptions {
            let value = self.eval(m, *exception, true)?;
            // The constraint cannot go into the context while the model is built, so it waits for
            // the next restart.
            if !AufSolver::are_distinct(m, k_value, value) {
                let eq = m.mk_eq(k, *exception)?;
                let constraint = m.mk_not(eq)?;
                self.new_constraints.push(constraint);
            }
        }
        Ok(true)
    }

    fn set_projection_else(&mut self, m: &mut AstManager, node: NodeId) -> Result<(), SmtError> {
        if self.get_instantiation_set(node)?.elems.is_empty() {
            return Ok(());
        }
        let exceptions = self.get_exceptions(node);
        if !exceptions.is_empty() || !self.get_avoid_set(node).is_empty() {
            let exception_values = self.collect_exceptions_values(m, node)?;
            if let Some(picked) = self.pick_instance_diff_exceptions(m, node, &exception_values)? {
                self.set_else(node, picked);
                return Ok(());
            }
            let sort = self.nodes[node as usize].sort;
            if AufSolver::is_infinite(sort) {
                let k = self.get_k_for(m, sort)?;
                if self.assert_k_diseq_exceptions(m, k, &exceptions)? {
                    self.insert(m, node, k, 0);
                    self.set_else(node, k);
                    return Ok(());
                }
            }
        }
        let first = self
            .get_instantiation_set(node)?
            .elems
            .keys()
            .next()
            .map_or(0, |key| key as Expr);
        self.set_else(node, first);
        Ok(())
    }

    // add_mono_exceptions: e - 1 and e + 1 join the set for each integer exception e.
    fn add_mono_exceptions(&mut self, m: &mut AstManager, node: NodeId) -> Result<(), SmtError> {
        if self.nodes[node as usize].sort != SORT_INT {
            return Ok(());
        }
        let one = m.mk_numeral(&Int::from(1));
        for exception in self.get_exceptions(node) {
            let minus_one = self.rewriter.mk_sub(m, exception, one)?;
            let plus_one = self.rewriter.mk_add(m, &[exception, one])?;
            self.insert(m, node, plus_one, 0);
            self.insert(m, node, minus_one, 0);
        }
        Ok(())
    }

    fn get_instantiation_set_values(
        &mut self,
        m: &mut AstManager,
        node: NodeId,
    ) -> Result<Vec<Expr>, SmtError> {
        let mut values: Vec<Expr> = Vec::new();
        // Only looked up, never iterated.
        let mut found = std::collections::HashSet::new();
        for (term, _) in self.get_instantiation_set(node)?.get_elems() {
            let value = self.eval(m, term, true)?;
            let is_found = !m.is_unique_value(value) && values.contains(&value);
            if !is_found && !found.contains(&value) {
                values.push(value);
                found.insert(value);
            }
        }
        Ok(values)
    }

    fn mk_mono_proj(&mut self, m: &mut AstManager, node: NodeId) -> Result<(), SmtError> {
        self.add_mono_exceptions(m, node)?;
        let mut values = self.get_instantiation_set_values(m, node)?;
        if values.is_empty() {
            return Ok(());
        }
        let sort = self.nodes[node as usize].sort;
        if !is_arith_sort(sort) || !values.iter().all(|value| m.is_numeral(*value)) {
            return Ok(());
        }
        values.sort_by(|first, second| {
            m.get_rational_value(*first)
                .compare(m.get_rational_value(*second))
        });
        let variable = m.mk_var(0, sort);
        let mut projection = values[values.len() - 1];
        for index in (1..values.len()).rev() {
            let condition = m.mk_app(OP_LT, &[variable, values[index]], SORT_BOOL)?;
            projection = m.mk_app(OP_ITE, &[condition, values[index - 1], projection], sort)?;
        }
        let mut interp = FuncInterp::new(1);
        interp.set_else(m, projection)?;
        let decl = m.mk_fresh_func_decl(None, &[sort], sort, true);
        self.get_model()?
            .borrow_mut()
            .register_aux_decl(m, decl, Some(interp))?;
        self.set_proj(node, decl);
        Ok(())
    }

    fn mk_simple_proj(&mut self, m: &mut AstManager, node: NodeId) -> Result<(), SmtError> {
        self.set_projection_else(m, node)?;
        let values = self.get_instantiation_set_values(m, node)?;
        let sort = self.nodes[node as usize].sort;
        let decl = m.mk_fresh_func_decl(None, &[sort], sort, true);
        let model = self.get_model()?;
        model
            .borrow_mut()
            .register_aux_decl(m, decl, Some(FuncInterp::new(1)))?;
        if let Some(else_expr) = self.get_else(node) {
            let else_value = self.eval(m, else_expr, true)?;
            if let Some(interp) = model.borrow_mut().get_func_interp_mut(m, decl) {
                interp.set_else(m, else_value)?;
            }
        }
        for value in values {
            if let Some(interp) = model.borrow_mut().get_func_interp_mut(m, decl) {
                interp.insert_new_entry(m, &[value], value)?;
            }
        }
        self.set_proj(node, decl);
        Ok(())
    }

    // collect_partial_funcs: a func_decl_set, in Z3's slot order.
    fn collect_partial_funcs(&mut self, m: &mut AstManager) -> Result<ObjHashtable, SmtError> {
        let model = self.get_model()?;
        let mut model = model.borrow_mut();
        let mut result = ObjHashtable::new();
        let decls: Vec<Decl> = self.a_f_is.iter().map(|(_, decl)| *decl).collect();
        for decl in decls {
            let hash = m.get_decl_hash(decl);
            if result.contains(decl as u32, hash) {
                continue;
            }
            if model.get_func_interp(m, decl).is_none() {
                let arity = m.func_decls[decl as usize].domain.len();
                model.register_func(m, decl, FuncInterp::new(arity))?;
            }
            if model
                .get_func_interp(m, decl)
                .is_some_and(FuncInterp::is_partial)
            {
                result.insert(decl as u32, hash);
            }
        }
        Ok(result)
    }

    // mk_sorts_finite: every uninterpreted sort gets a finite universe.
    fn mk_sorts_finite(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        let model = self.get_model()?;
        let mut model = model.borrow_mut();
        for node in &self.root_nodes {
            let sort = self.nodes[*node as usize].sort;
            if m.is_uninterpreted_sort(sort) && !model.is_finite(m, sort) {
                model.freeze_universe(m, sort);
            }
        }
        Ok(())
    }

    fn add_elem_to_empty_inst_sets(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        // Only looked up, never iterated.
        let mut sort2elems: HashMap<Sort, Expr> = HashMap::new();
        let mut need_fresh = Vec::new();
        for index in 0..self.root_nodes.len() {
            let node = self.root_nodes[index];
            let sort = self.nodes[node as usize].sort;
            let first = self.get_instantiation_set(node)?.elems.keys().next();
            match first {
                None => {
                    if m.is_uninterpreted_sort(sort) {
                        need_fresh.push(node);
                    } else {
                        let value = self.get_model()?.borrow_mut().get_some_value(m, sort);
                        self.insert(m, node, value, 0);
                    }
                }
                Some(first) => {
                    sort2elems.insert(sort, first as Expr);
                }
            }
        }
        for node in need_fresh {
            let sort = self.nodes[node as usize].sort;
            let elem = match sort2elems.get(&sort) {
                Some(elem) => *elem,
                None => {
                    let elem = m.mk_fresh_const(Some(&SmtSymbol::Name("elem".into())), sort)?;
                    sort2elems.insert(sort, elem);
                    elem
                }
            };
            self.insert(m, node, elem, 0);
        }
        Ok(())
    }

    fn collect_root_nodes(&mut self) {
        self.root_nodes = self
            .nodes
            .iter()
            .filter(|node| node.is_root())
            .map(|node| node.id)
            .collect();
    }

    fn get_f_i_proj(&self, decl: Decl, index: u32) -> Option<Decl> {
        self.afi_index
            .get(&(decl, index))
            .and_then(|node| self.get_proj(*node))
    }

    fn complete_partial_funcs(
        &mut self,
        m: &mut AstManager,
        partial_funcs: &ObjHashtable,
    ) -> Result<(), SmtError> {
        let model = self.get_model()?;
        let mut model = model.borrow_mut();
        for decl in partial_funcs.iter() {
            let decl = decl as Decl;
            model.complete_partial_func(m, decl, true)?;
            match model.get_func_interp(m, decl) {
                Some(interp) if !interp.is_constant(m) => {}
                _ => continue,
            }
            let data = m.func_decls[decl as usize].clone();
            let mut has_proj = false;
            let mut args = Vec::with_capacity(data.domain.len());
            for (index, sort) in data.domain.iter().enumerate() {
                let variable = m.mk_var(index as i32, *sort);
                match self.get_f_i_proj(decl, index as u32) {
                    None => args.push(variable),
                    Some(proj) => {
                        has_proj = true;
                        args.push(m.mk_app(proj, &[variable], *sort)?);
                    }
                }
            }
            if !has_proj {
                continue;
            }
            let aux_decl = m.mk_fresh_func_decl(Some(&data.name), &data.domain, data.range, true);
            let mut new_interp = FuncInterp::new(data.domain.len());
            let else_expr = m.mk_app(aux_decl, &args, data.range)?;
            new_interp.set_else(m, else_expr)?;
            model.reregister_decl(m, decl, new_interp, aux_decl)?;
        }
        Ok(())
    }

    fn mk_inverses(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        let offset = self.random.next() as usize;
        let count = self.root_nodes.len();
        for index in (0..count).rev() {
            let node = self.root_nodes[(index + offset) % count];
            let root = self.get_root(node) as usize;
            let Some(mut set) = self.nodes[root].set.take() else {
                return Err(SmtError::Invariant(
                    "the instantiation set was not created".into(),
                ));
            };
            let result = set.mk_inverse(m, |m, expr| self.eval(m, expr, true));
            self.nodes[root].set = Some(set);
            result?;
        }
        Ok(())
    }

    pub fn fix_model(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.cleanup_instantiation_sets(m)?;
        let partial_funcs = self.collect_partial_funcs(m)?;
        self.reset_eval_cache(m)?;
        self.collect_root_nodes();
        self.add_elem_to_empty_inst_sets(m)?;
        self.mk_sorts_finite(m)?;
        for index in 0..self.root_nodes.len() {
            let node = self.root_nodes[index];
            if self.is_mono_proj(node) {
                self.mk_mono_proj(m, node)?;
            } else {
                self.mk_simple_proj(m, node)?;
            }
        }
        self.mk_inverses(m)?;
        self.complete_partial_funcs(m, &partial_funcs)
    }

    pub fn is_default_representative(&self, m: &AstManager, term: Expr) -> bool {
        self.sort2k.get(&m.sorts[term as usize]) == Some(&term)
    }
}

#[cfg(test)]
mod tests {
    use prove_decide::Limits;

    use super::{AufSolver, InstantiationSet};
    use crate::core::ast::{AstManager, Expr, QuantifierData, SORT_BOOL, SmtSymbol};
    use crate::core::proto_model::ProtoModel;
    use crate::core::rewriter::{Rewriter, TACTIC_REWRITER_OPTIONS};
    use crate::util::rlimit::ResourceLimit;

    fn mk_manager() -> AstManager {
        AstManager::new(ResourceLimit::new(&Limits::new(f64::INFINITY, None, None)))
    }

    #[test]
    fn holds_the_closed_terms_of_a_set_and_inverts_it_by_least_generation() {
        let m = &mut mk_manager();
        let u = m.mk_sort("U");
        let constant = |m: &mut AstManager, name: &str| -> Expr {
            let decl = m.mk_func_decl(SmtSymbol::Name(name.into()), &[], u, false);
            m.mk_app(decl, &[], u).unwrap()
        };
        let a = constant(m, "a");
        let b = constant(m, "b");
        let c = constant(m, "c");
        let value = m.mk_model_value(0, u);
        let other = m.mk_model_value(1, u);
        m.inc_ref(value);
        m.inc_ref(other);
        let x = m.mk_var(0, u);
        let mut set = InstantiationSet::new();
        set.insert(m, a, 3);
        set.insert(m, b, 1);
        // A term it has keeps its generation, and model values are left out.
        set.insert(m, a, 0);
        set.insert(m, value, 0);
        set.insert(m, c, 2);
        assert_eq!(set.elems.len(), 3);
        assert_eq!(set.get_generation(m, a), 3);
        assert_eq!(set.get_generation(m, x), 0);
        assert_eq!(m.get_ref_count(a), 1);
        // a and b take the same value, c another: b has the least generation.
        set.mk_inverse(m, |_, expr| Ok(if expr == c { other } else { value }))
            .unwrap();
        let model = ProtoModel::new(m);
        assert_eq!(set.get_inv(m, value, &model), Some(b));
        assert_eq!(set.get_inv(m, other, &model), Some(c));
        assert_eq!(set.get_inv(m, m.true_expr, &model), None);
        set.remove(m, a).unwrap();
        assert_eq!(set.elems.len(), 2);
        assert_eq!(m.ids[a as usize], -1);
        set.release(m).unwrap();
        assert_eq!(m.ids[b as usize], -1);
    }

    #[test]
    fn merges_nodes_into_the_larger_class() {
        let m = &mut mk_manager();
        let u = m.mk_sort("U");
        let f = m.mk_func_decl(SmtSymbol::Name("f".into()), &[u, u], u, false);
        let body = m.mk_var(0, SORT_BOOL);
        let quantifier = m
            .mk_quantifier(QuantifierData {
                is_forall: true,
                sorts: vec![u, SORT_BOOL],
                names: vec![SmtSymbol::Name("x".into()), SmtSymbol::Name("y".into())],
                body,
                patterns: Vec::new(),
                weight: 0,
                qid: String::new(),
            })
            .unwrap();
        let count = m.limit.count();
        let rewriter = Rewriter::new(m, TACTIC_REWRITER_OPTIONS, false);
        let mut solver = AufSolver::new(m, rewriter);
        // The solver takes a step when it is made.
        assert_eq!(m.limit.count(), count + 1);
        // Variable i takes the sort of the de Bruijn index i.
        let y = solver.get_uvar(m, quantifier, 0).unwrap();
        let x = solver.get_uvar(m, quantifier, 1).unwrap();
        assert_eq!(solver.node(y).sort, SORT_BOOL);
        assert_eq!(solver.node(x).sort, u);
        let f0 = solver.get_a_f_i(m, f, 0);
        let f1 = solver.get_a_f_i(m, f, 1);
        assert_eq!(solver.get_a_f_i(m, f, 0), f0);
        assert_eq!(solver.get_uvar(m, quantifier, 1).unwrap(), x);
        solver.insert_exception(x, body);
        solver.insert_avoid(f0, y);
        // Of two classes of one node, the first joins the second, with its exceptions.
        solver.merge(x, f0);
        assert_eq!(solver.get_root(x), f0);
        // The smaller class joins the larger, whichever comes first.
        solver.set_mono_proj(f1);
        solver.merge(f0, f1);
        assert_eq!(solver.get_root(f1), f0);
        assert!(solver.is_mono_proj(x));
        solver.mk_instantiation_sets();
        assert!(solver.node(f0).is_root() && !solver.node(f1).is_root());
        assert!(solver.get_instantiation_set(f1).is_ok());
        assert!(solver.get_uvar_inst_set(quantifier, 1).unwrap().is_some());
        assert!(solver.get_uvar_inst_set(quantifier, 2).unwrap().is_none());
    }
}
