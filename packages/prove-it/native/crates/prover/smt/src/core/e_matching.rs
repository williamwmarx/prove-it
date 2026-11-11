//! Ported from Z3 (src/smt/mam.cpp), MIT license, see z3-license.txt, through `e-matching.ts`.
//! Matching of quantifier patterns against the E-graph with Z3's matching abstract machine: the
//! patterns are compiled into code trees, new relevant terms become candidates of the tree for
//! their label, and the inverted path index with approximate label sets finds the candidates that
//! a merge creates.
//!
//! `Mam` keeps the context, so (design/smt-core.md, "The context") its state is a struct held by
//! the quantifier manager, which has two (`mam` and `lazy_mam`), and its methods that reach the
//! context are `impl Context` methods named `mam_<method>`, which take the `MamKind` of the
//! matcher. The path trees are an arena of the matcher, as the code trees are (`mam_compiler.rs`).
//! The closures the matcher pushes on its own trail are the enum `MamTrail`, and those it and its
//! compiler push on the context's trail are `MamClosure`.
//!
//! The TypeScript's `onMatch` is the quantifier manager's `addInstance`, the only one it makes.
//! The interpreter runs with the context borrowed for reading, so it keeps the matches a run
//! yields, in order, and `mam_execute`/`mam_execute_core` hand them to `qmanager_add_instance` once
//! the run returns. Nothing a match reads changes in between: `addInstance` only touches the
//! fingerprints and the instance queue, which the interpreter never reads, and takes no step.

use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};
use std::mem;

use crate::core::ast::{Decl, Expr, KIND_VAR};
use crate::core::context::{Context, TrailClosure};
use crate::core::enode::EnodeId;
use crate::core::mam_compiler::{
    CodeTrees, Compiler, InstrId, LabelHasher, TreeId, has_hash, set_at, set_hash,
};
use crate::core::mam_interpreter::Interpreter;
use crate::core::rewriter_tpl::MAX_RECURSION_DEPTH;
use crate::util::error::SmtError;
use crate::util::hash::{hash_u, mk_mix};
use crate::util::ordered_map::OrderedMap;

/// Which of the quantifier manager's two matchers: the eager one, or the lazy one that runs in
/// the final check.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MamKind {
    Eager,
    Lazy,
}

/// A path tree node: its index in `Mam::path_trees`.
pub type PathTreeId = u32;

/// The closures the matcher and its compiler push on the context's trail, undone by
/// `mam_undo_closure`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MamClosure {
    /// mam-compiler.ts setNext: `() => { instr.next = old; }`.
    Next {
        mam: MamKind,
        instr: InstrId,
        old: Option<InstrId>,
    },
    /// mam-compiler.ts insert_new_lbl_hash: `() => { filter.lblLow = low; filter.lblHigh = high; }`.
    Filter {
        mam: MamKind,
        instr: InstrId,
        low: u32,
        high: u32,
    },
    /// mam-compiler.ts insert: `() => { tree.numRegs = numRegs; }`.
    NumRegs {
        mam: MamKind,
        tree: TreeId,
        num_regs: u32,
    },
    /// mam-compiler.ts insert: `() => { tree.numChoices = numChoices; }`.
    NumChoices {
        mam: MamKind,
        tree: TreeId,
        num_choices: u32,
    },
    /// setLblHash: `() => { node.lblHash = -1; }`.
    LblHash { node: EnodeId },
    /// setLblHash: `() => { root.lbls = low; root.lblsHigh = high; }`.
    Lbls { root: EnodeId, low: u32, high: u32 },
    /// addSharedEnode: `() => this.sharedEnodes.delete(node)`.
    SharedEnode { mam: MamKind, node: EnodeId },
}

/// The closures of the matcher's own trail (m_trail_stack).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum MamTrail {
    Lbls {
        root: EnodeId,
        low: u32,
        high: u32,
    },
    Plbls {
        root: EnodeId,
        low: u32,
        high: u32,
    },
    PlblsDelete(Decl),
    ClblsDelete(Decl),
    FirstChild(PathTreeId),
    Code(PathTreeId),
    Sibling(PathTreeId),
    PathFilter {
        tree: PathTreeId,
        low: u32,
        high: u32,
    },
    PcDelete(u32),
    PpEntry {
        key: u32,
        index: usize,
    },
    PpDelete(u32),
    TreesDelete(Decl),
    AddEq {
        r2: EnodeId,
        lbls: u32,
        lbls_high: u32,
        plbls: u32,
        plbls_high: u32,
    },
}

/// A step from a term to its parent: the parent's label, the position of the term in it, and an
/// optional ground argument the parent must also have. The child is an index in the paths of the
/// pattern being added.
#[derive(Clone, Copy, Debug)]
struct Path {
    label: Decl,
    arg_index: u32,
    ground_arg_index: u32,
    ground_arg: Option<EnodeId>,
    pattern_index: usize,
    child: Option<usize>,
}

/// The inverted path index shares the prefixes of paths. Siblings are alternatives for the same
/// step, the first child is the next step, and a code receives the terms where a path ends.
#[derive(Clone, Debug)]
struct PathTree {
    label: Decl,
    arg_index: u32,
    ground_arg_index: u32,
    ground_arg: Option<EnodeId>,
    filter: u32,
    filter_high: u32,
    code: Option<TreeId>,
    first_child: Option<PathTreeId>,
    sibling: Option<PathTreeId>,
    // The roots that collect_parents visits at this node, while it walks the tree.
    todo: Option<Vec<EnodeId>>,
}

fn is_equal_path(paths: &[Path], first: usize, second: usize) -> bool {
    let mut left = &paths[first];
    let mut right = &paths[second];
    loop {
        if left.label != right.label
            || left.arg_index != right.arg_index
            || left.pattern_index != right.pattern_index
            || left.child.is_none() != right.child.is_none()
        {
            return false;
        }
        match (left.child, right.child) {
            (Some(left_child), Some(right_child)) => {
                left = &paths[left_child];
                right = &paths[right_child];
            }
            _ => return true,
        }
    }
}

/// A multi-pattern of a quantifier: the terms of one of its patterns.
#[derive(Clone, Debug)]
struct MultiPattern {
    quantifier: Expr,
    patterns: Vec<Expr>,
}

#[derive(Clone, Debug, Default)]
pub struct Mam {
    trees: OrderedMap<Decl, TreeId>,
    // m_shared_enodes: the ground terms of the patterns.
    shared_enodes: HashSet<EnodeId>,
    to_match: Vec<TreeId>,
    new_patterns: Vec<MultiPattern>,
    pc: HashMap<u32, PathTreeId>,
    pp: HashMap<u32, [Option<PathTreeId>; 2]>,
    plbls: HashSet<Decl>,
    clbls: HashSet<Decl>,
    r1: Option<EnodeId>,
    r2: Option<EnodeId>,
    // The nodes that collect_parents marks, to unmark at the end of each level.
    visited_parents: Vec<EnodeId>,
    queued_roots: Vec<EnodeId>,
    label_hashes: Vec<i32>,
    // m_trail_stack: the matcher undoes its changes with a trail of its own, which the quantifier
    // manager pops before the context pops its trail.
    trail: Vec<MamTrail>,
    trail_scopes: Vec<usize>,
    pub(crate) compiler: Compiler,
    pub(crate) interpreter: Interpreter,
    pub(crate) code: CodeTrees,
    path_trees: Vec<PathTree>,
}

impl Mam {
    pub fn new() -> Mam {
        Mam::default()
    }

    pub fn has_work(&self) -> bool {
        !self.to_match.is_empty() || !self.new_patterns.is_empty()
    }

    pub fn is_shared(&self, node: EnodeId) -> bool {
        self.shared_enodes.contains(&node)
    }

    pub fn push_scope(&mut self) {
        self.trail_scopes.push(self.trail.len());
    }

    fn mk_path_tree_node(&mut self, path: &Path) -> PathTreeId {
        self.path_trees.push(PathTree {
            label: path.label,
            arg_index: path.arg_index,
            ground_arg_index: path.ground_arg_index,
            ground_arg: path.ground_arg,
            filter: 0,
            filter_high: 0,
            code: None,
            first_child: None,
            sibling: None,
            todo: None,
        });
        (self.path_trees.len() - 1) as PathTreeId
    }

    fn path_tree(&self, id: PathTreeId) -> &PathTree {
        &self.path_trees[id as usize]
    }

    fn path_tree_mut(&mut self, id: PathTreeId) -> &mut PathTree {
        &mut self.path_trees[id as usize]
    }
}

impl LabelHasher for Context {
    /// label_hasher: Bob Jenkins' mix of the small id of a declaration, in [0, 64).
    fn get_label_hash(&mut self, mam: MamKind, decl: Decl) -> u32 {
        if let Some(cached) = self.qmanager.mam(mam).label_hashes.get(decl as usize)
            && *cached != -1
        {
            return *cached as u32;
        }
        let hash = mk_mix(17, 3, self.m.func_decls[decl as usize].small_id as u32) & 63;
        set_at(
            &mut self.qmanager.mam_mut(mam).label_hashes,
            decl as usize,
            hash as i32,
            -1,
        );
        hash
    }

    fn get_ground_enode(
        &mut self,
        _mam: MamKind,
        expr: Expr,
        quantifier: Expr,
    ) -> Result<Option<EnodeId>, SmtError> {
        if !self.is_e_internalized(expr) {
            let generation = self.qmanager.get_generation(quantifier);
            self.internalize_with_generation(expr, false, generation)?;
        }
        Ok(self.get_enode(expr))
    }

    fn get_lbl_hash(&mut self, _mam: MamKind, node: EnodeId) -> i32 {
        if self.node(node).lbl_hash == -1 {
            self.mam_set_lbl_hash(node);
        }
        self.node(node).lbl_hash
    }
}

impl Context {
    pub(crate) fn mam_undo_closure(&mut self, closure: MamClosure) {
        match closure {
            MamClosure::Next { mam, instr, old } => {
                self.qmanager.mam_mut(mam).code.instr_mut(instr).next = old;
            }
            MamClosure::Filter {
                mam,
                instr,
                low,
                high,
            } => {
                let filter = self.qmanager.mam_mut(mam).code.instr_mut(instr);
                filter.lbl_low = low;
                filter.lbl_high = high;
            }
            MamClosure::NumRegs {
                mam,
                tree,
                num_regs,
            } => self.qmanager.mam_mut(mam).code.tree_mut(tree).num_regs = num_regs,
            MamClosure::NumChoices {
                mam,
                tree,
                num_choices,
            } => self.qmanager.mam_mut(mam).code.tree_mut(tree).num_choices = num_choices,
            MamClosure::LblHash { node } => self.node_mut(node).lbl_hash = -1,
            MamClosure::Lbls { root, low, high } => {
                let root = self.node_mut(root);
                root.lbls = low;
                root.lbls_high = high;
            }
            MamClosure::SharedEnode { mam, node } => {
                self.qmanager.mam_mut(mam).shared_enodes.remove(&node);
            }
        }
    }

    fn mam_undo_trail(&mut self, mam: MamKind, entry: MamTrail) {
        match entry {
            MamTrail::Lbls { root, low, high } => {
                let root = self.node_mut(root);
                root.lbls = low;
                root.lbls_high = high;
            }
            MamTrail::Plbls { root, low, high } => {
                let root = self.node_mut(root);
                root.plbls = low;
                root.plbls_high = high;
            }
            MamTrail::PlblsDelete(decl) => {
                self.qmanager.mam_mut(mam).plbls.remove(&decl);
            }
            MamTrail::ClblsDelete(decl) => {
                self.qmanager.mam_mut(mam).clbls.remove(&decl);
            }
            MamTrail::FirstChild(tree) => {
                self.qmanager.mam_mut(mam).path_tree_mut(tree).first_child = None;
            }
            MamTrail::Code(tree) => self.qmanager.mam_mut(mam).path_tree_mut(tree).code = None,
            MamTrail::Sibling(tree) => {
                self.qmanager.mam_mut(mam).path_tree_mut(tree).sibling = None;
            }
            MamTrail::PathFilter { tree, low, high } => {
                let tree = self.qmanager.mam_mut(mam).path_tree_mut(tree);
                tree.filter = low;
                tree.filter_high = high;
            }
            MamTrail::PcDelete(key) => {
                self.qmanager.mam_mut(mam).pc.remove(&key);
            }
            MamTrail::PpEntry { key, index } => {
                if let Some(entry) = self.qmanager.mam_mut(mam).pp.get_mut(&key) {
                    entry[index] = None;
                }
            }
            MamTrail::PpDelete(key) => {
                self.qmanager.mam_mut(mam).pp.remove(&key);
            }
            MamTrail::TreesDelete(label) => {
                self.qmanager.mam_mut(mam).trees.remove(&label);
            }
            MamTrail::AddEq {
                r2,
                lbls,
                lbls_high,
                plbls,
                plbls_high,
            } => {
                let r2 = self.node_mut(r2);
                r2.lbls = lbls;
                r2.lbls_high = lbls_high;
                r2.plbls = plbls;
                r2.plbls_high = plbls_high;
            }
        }
    }

    /// enode::set_lbl_hash: a ground term of a pattern hashes its id, and its root's labels take
    /// it. The context's trail undoes both. Z3 pops it after the matcher's trail, so the labels of
    /// a root can keep a hash that a merge undone by the matcher's trail added.
    fn mam_set_lbl_hash(&mut self, node: EnodeId) {
        let owner = self.node(node).owner;
        let hash = (hash_u(self.m.ids[owner as usize] as u32) & 63) as i32;
        self.node_mut(node).lbl_hash = hash;
        self.push_trail(TrailClosure::Mam(MamClosure::LblHash { node }));
        let root = self.root(node);
        let (low, high) = (self.node(root).lbls, self.node(root).lbls_high);
        if has_hash(low, high, hash) {
            return;
        }
        self.push_trail(TrailClosure::Mam(MamClosure::Lbls { root, low, high }));
        let root = self.node_mut(root);
        set_hash(&mut root.lbls, &mut root.lbls_high, hash);
    }

    fn mam_update_lbls(&mut self, mam: MamKind, node: EnodeId, hash: i32) {
        let root = self.root(node);
        let (low, high) = (self.node(root).lbls, self.node(root).lbls_high);
        if has_hash(low, high, hash) {
            return;
        }
        self.qmanager
            .mam_mut(mam)
            .trail
            .push(MamTrail::Lbls { root, low, high });
        let root = self.node_mut(root);
        set_hash(&mut root.lbls, &mut root.lbls_high, hash);
    }

    fn mam_update_children_plbls(&mut self, mam: MamKind, node: EnodeId, hash: i32) {
        for index in 0..self.node(node).num_args() {
            let root = self.enode_arena.get_arg_root(node, index);
            let (low, high) = (self.node(root).plbls, self.node(root).plbls_high);
            if has_hash(low, high, hash) {
                continue;
            }
            self.qmanager
                .mam_mut(mam)
                .trail
                .push(MamTrail::Plbls { root, low, high });
            let root = self.node_mut(root);
            set_hash(&mut root.plbls, &mut root.plbls_high, hash);
        }
    }

    fn mam_update_plbls(&mut self, mam: MamKind, decl: Decl) {
        if !self.qmanager.mam_mut(mam).plbls.insert(decl) {
            return;
        }
        self.qmanager
            .mam_mut(mam)
            .trail
            .push(MamTrail::PlblsDelete(decl));
        let hash = self.get_label_hash(mam, decl) as i32;
        for index in 0..self.enodes_of(decl).len() {
            let node = self.enodes_of(decl)[index];
            if self.is_relevant(self.node(node).owner) {
                self.mam_update_children_plbls(mam, node, hash);
            }
        }
    }

    fn mam_update_clbls(&mut self, mam: MamKind, decl: Decl) {
        if !self.qmanager.mam_mut(mam).clbls.insert(decl) {
            return;
        }
        self.qmanager
            .mam_mut(mam)
            .trail
            .push(MamTrail::ClblsDelete(decl));
        let hash = self.get_label_hash(mam, decl) as i32;
        for index in 0..self.enodes_of(decl).len() {
            let node = self.enodes_of(decl)[index];
            if self.is_relevant(self.node(node).owner) {
                self.mam_update_lbls(mam, node, hash);
            }
        }
    }

    /// mk_code: the code tree of a path, which runs each candidate once.
    fn mam_mk_code(
        &mut self,
        mam: MamKind,
        mp: &MultiPattern,
        pattern_index: usize,
    ) -> Result<TreeId, SmtError> {
        self.compiler_mk_tree(mam, mp.quantifier, &mp.patterns, pattern_index, true)
    }

    /// mk_path_tree: a chain of path tree nodes whose last one has a code for the path's pattern.
    fn mam_mk_path_tree(
        &mut self,
        mam: MamKind,
        paths: &[Path],
        path: usize,
        mp: &MultiPattern,
    ) -> Result<PathTreeId, SmtError> {
        let tree = self.qmanager.mam_mut(mam).mk_path_tree_node(&paths[path]);
        let hash = self.get_label_hash(mam, paths[path].label) as i32;
        let node = self.qmanager.mam_mut(mam).path_tree_mut(tree);
        set_hash(&mut node.filter, &mut node.filter_high, hash);
        match paths[path].child {
            None => {
                let code = self.mam_mk_code(mam, mp, paths[path].pattern_index)?;
                self.qmanager.mam_mut(mam).path_tree_mut(tree).code = Some(code);
            }
            Some(child) => {
                let first_child = self.mam_mk_path_tree(mam, paths, child, mp)?;
                self.qmanager.mam_mut(mam).path_tree_mut(tree).first_child = Some(first_child);
            }
        }
        Ok(tree)
    }

    /// compiler::insert for path trees.
    fn mam_insert_path(
        &mut self,
        mam: MamKind,
        head: PathTreeId,
        paths: &[Path],
        path: usize,
        mp: &MultiPattern,
    ) -> Result<(), SmtError> {
        let current = paths[path];
        let mut is_label_found = false;
        let mut last = head;
        let mut tree = Some(head);
        while let Some(found) = tree {
            last = found;
            let node = self.qmanager.mam(mam).path_tree(found).clone();
            tree = node.sibling;
            if node.label != current.label {
                continue;
            }
            is_label_found = true;
            if node.arg_index != current.arg_index
                || node.ground_arg != current.ground_arg
                || node.ground_arg_index != current.ground_arg_index
            {
                continue;
            }
            match (current.child, node.first_child, node.code) {
                (Some(child), Some(first_child), _) => {
                    self.mam_insert_path(mam, first_child, paths, child, mp)?;
                }
                (Some(child), None, _) => {
                    let first_child = self.mam_mk_path_tree(mam, paths, child, mp)?;
                    let matcher = self.qmanager.mam_mut(mam);
                    matcher.path_tree_mut(found).first_child = Some(first_child);
                    matcher.trail.push(MamTrail::FirstChild(found));
                }
                (None, _, Some(code)) => {
                    self.compiler_insert(
                        mam,
                        code,
                        mp.quantifier,
                        &mp.patterns,
                        current.pattern_index,
                        false,
                    )?;
                }
                (None, _, None) => {
                    let code = self.mam_mk_code(mam, mp, current.pattern_index)?;
                    let matcher = self.qmanager.mam_mut(mam);
                    matcher.path_tree_mut(found).code = Some(code);
                    matcher.trail.push(MamTrail::Code(found));
                }
            }
            return Ok(());
        }
        let sibling = self.mam_mk_path_tree(mam, paths, path, mp)?;
        let matcher = self.qmanager.mam_mut(mam);
        matcher.path_tree_mut(last).sibling = Some(sibling);
        matcher.trail.push(MamTrail::Sibling(last));
        if is_label_found {
            return Ok(());
        }
        let (low, high) = {
            let node = matcher.path_tree(head);
            (node.filter, node.filter_high)
        };
        matcher.trail.push(MamTrail::PathFilter {
            tree: head,
            low,
            high,
        });
        let hash = self.get_label_hash(mam, current.label) as i32;
        let node = self.qmanager.mam_mut(mam).path_tree_mut(head);
        set_hash(&mut node.filter, &mut node.filter_high, hash);
        Ok(())
    }

    fn mam_update_pc(
        &mut self,
        mam: MamKind,
        first_hash: u32,
        second_hash: u32,
        paths: &[Path],
        path: usize,
        mp: &MultiPattern,
    ) -> Result<(), SmtError> {
        let key = first_hash * 64 + second_hash;
        if let Some(existing) = self.qmanager.mam(mam).pc.get(&key).copied() {
            return self.mam_insert_path(mam, existing, paths, path, mp);
        }
        let tree = self.mam_mk_path_tree(mam, paths, path, mp)?;
        let matcher = self.qmanager.mam_mut(mam);
        matcher.pc.insert(key, tree);
        matcher.trail.push(MamTrail::PcDelete(key));
        Ok(())
    }

    fn mam_insert_pp_path(
        &mut self,
        mam: MamKind,
        key: u32,
        index: usize,
        paths: &[Path],
        path: usize,
        mp: &MultiPattern,
    ) -> Result<(), SmtError> {
        let existing = self
            .qmanager
            .mam(mam)
            .pp
            .get(&key)
            .and_then(|entry| entry[index]);
        if let Some(existing) = existing {
            return self.mam_insert_path(mam, existing, paths, path, mp);
        }
        let tree = self.mam_mk_path_tree(mam, paths, path, mp)?;
        let matcher = self.qmanager.mam_mut(mam);
        if let Some(entry) = matcher.pp.get_mut(&key) {
            entry[index] = Some(tree);
        }
        matcher.trail.push(MamTrail::PpEntry { key, index });
        Ok(())
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "the parameters of the TypeScript method, with the matcher and the paths"
    )]
    fn mam_update_pp(
        &mut self,
        mam: MamKind,
        input_first_hash: u32,
        input_second_hash: u32,
        input_first: usize,
        input_second: usize,
        paths: &[Path],
        mp: &MultiPattern,
    ) -> Result<(), SmtError> {
        let is_swapped = input_first_hash > input_second_hash;
        let (first_hash, second_hash) = if is_swapped {
            (input_second_hash, input_first_hash)
        } else {
            (input_first_hash, input_second_hash)
        };
        let (first, second) = if is_swapped {
            (input_second, input_first)
        } else {
            (input_first, input_second)
        };
        let key = first_hash * 64 + second_hash;
        let matcher = self.qmanager.mam_mut(mam);
        if let Entry::Vacant(entry) = matcher.pp.entry(key) {
            entry.insert([None, None]);
            matcher.trail.push(MamTrail::PpDelete(key));
        }
        if first_hash == second_hash {
            self.mam_insert_pp_path(mam, key, 0, paths, first, mp)?;
            if !is_equal_path(paths, first, second) {
                self.mam_insert_pp_path(mam, key, 0, paths, second, mp)?;
            }
            return Ok(());
        }
        self.mam_insert_pp_path(mam, key, 0, paths, first, mp)?;
        self.mam_insert_pp_path(mam, key, 1, paths, second, mp)
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "the parameters of the TypeScript method, with the matcher and the paths"
    )]
    fn mam_update_filters(
        &mut self,
        mam: MamKind,
        pattern: Expr,
        parent_path: Option<usize>,
        pattern_index: usize,
        var_paths: &mut [Vec<usize>],
        paths: &mut Vec<Path>,
        mp: &MultiPattern,
    ) -> Result<(), SmtError> {
        let num_args = self.m.get_num_args(pattern);
        let mut ground_arg_index: i64 = -1;
        let mut index = 0;
        while index < num_args && ground_arg_index == -1 {
            if self.m.is_ground(self.m.get_arg(pattern, index)) {
                ground_arg_index = index as i64;
            }
            index += 1;
        }
        let ground_arg = if ground_arg_index == -1 {
            None
        } else {
            let arg = self.m.get_arg(pattern, ground_arg_index as usize);
            self.get_ground_enode(mam, arg, mp.quantifier)?
        };
        let label = self.m.decls[pattern as usize];
        for index in 0..num_args {
            let child = self.m.get_arg(pattern, index);
            paths.push(Path {
                label,
                arg_index: index as u32,
                ground_arg_index: if ground_arg_index == -1 {
                    0
                } else {
                    ground_arg_index as u32
                },
                ground_arg,
                pattern_index,
                child: parent_path,
            });
            let path = paths.len() - 1;
            if self.m.kinds[child as usize] == KIND_VAR {
                let var_index = self.m.values[child as usize] as usize;
                let mut is_found = false;
                for existing in var_paths[var_index].clone() {
                    if is_equal_path(paths, path, existing) {
                        is_found = true;
                    }
                    self.mam_update_plbls(mam, paths[existing].label);
                    self.mam_update_plbls(mam, paths[path].label);
                    let existing_hash = self.get_label_hash(mam, paths[existing].label);
                    let path_hash = self.get_label_hash(mam, paths[path].label);
                    self.mam_update_pp(mam, existing_hash, path_hash, existing, path, paths, mp)?;
                }
                if !is_found {
                    var_paths[var_index].push(path);
                }
                continue;
            }
            if self.m.is_ground(child) {
                let Some(node) = self.get_ground_enode(mam, child, mp.quantifier)? else {
                    continue;
                };
                self.mam_update_plbls(mam, label);
                let label_hash = self.get_label_hash(mam, label);
                let node_hash = self.get_lbl_hash(mam, node) as u32;
                self.mam_update_pc(mam, label_hash, node_hash, paths, path, mp)?;
                continue;
            }
            let child_label = self.m.decls[child as usize];
            self.mam_update_plbls(mam, label);
            self.mam_update_clbls(mam, child_label);
            let label_hash = self.get_label_hash(mam, label);
            let child_hash = self.get_label_hash(mam, child_label);
            self.mam_update_pc(mam, label_hash, child_hash, paths, path, mp)?;
            self.mam_update_filters(mam, child, Some(path), pattern_index, var_paths, paths, mp)?;
        }
        Ok(())
    }

    pub fn mam_add_pattern(
        &mut self,
        mam: MamKind,
        quantifier: Expr,
        patterns: &[Expr],
    ) -> Result<(), SmtError> {
        if patterns.iter().all(|pattern| self.m.is_ground(*pattern)) {
            return Ok(());
        }
        if patterns
            .iter()
            .any(|pattern| self.m.has_quantifier_flags[*pattern as usize] != 0)
        {
            return Ok(());
        }
        // The compiler and the path index recurse on the patterns, which the TypeScript answers
        // unknown on when the stack overflows.
        if patterns
            .iter()
            .any(|pattern| self.m.depths[*pattern as usize] as usize >= MAX_RECURSION_DEPTH)
        {
            return Err(SmtError::Unsupported("a pattern nests too deeply".into()));
        }
        let mp = MultiPattern {
            quantifier,
            patterns: patterns.to_vec(),
        };
        let num_decls = self.m.get_quantifier(quantifier)?.sorts.len();
        // The compiler indexes its variables by de Bruijn index, which the TypeScript reads past
        // the quantifier's variables as undefined. A pattern only has the quantifier's own.
        if patterns
            .iter()
            .any(|pattern| self.m.free_var_bounds[*pattern as usize] as usize > num_decls)
        {
            return Err(SmtError::Unsupported(
                "a pattern has a variable of an outer quantifier".into(),
            ));
        }
        let mut var_paths: Vec<Vec<usize>> = vec![Vec::new(); num_decls];
        let mut paths = Vec::new();
        for (index, pattern) in patterns.iter().enumerate() {
            self.mam_update_filters(mam, *pattern, None, index, &mut var_paths, &mut paths, &mp)?;
        }
        self.mam_collect_ground_exprs(mam, quantifier, patterns)?;
        self.qmanager.mam_mut(mam).new_patterns.push(mp);
        // code_tree_map::add_pattern for each pattern as the first one.
        for (first_index, pattern) in patterns.iter().enumerate() {
            if self.m.is_ground(*pattern) {
                continue;
            }
            let label = self.m.decls[*pattern as usize];
            if let Some(tree) = self.qmanager.mam(mam).trees.get(&label).copied() {
                if self.qmanager.mam(mam).code.tree(tree).num_args
                    == self.m.get_num_args(*pattern) as u32
                {
                    self.compiler_insert(mam, tree, quantifier, patterns, first_index, false)?;
                }
                continue;
            }
            let tree = self.compiler_mk_tree(mam, quantifier, patterns, first_index, false)?;
            let matcher = self.qmanager.mam_mut(mam);
            matcher.trees.insert(label, tree);
            matcher.trail.push(MamTrail::TreesDelete(label));
        }
        Ok(())
    }

    /// collect_ground_exprs: the ground patterns become relevant enodes, and the ground subterms of
    /// the other patterns become enodes that theory combination treats as shared.
    fn mam_collect_ground_exprs(
        &mut self,
        mam: MamKind,
        quantifier: Expr,
        patterns: &[Expr],
    ) -> Result<(), SmtError> {
        let mut todo = Vec::new();
        for pattern in patterns {
            if !self.m.is_ground(*pattern) {
                todo.push(*pattern);
                continue;
            }
            let Some(node) = self.get_ground_enode(mam, *pattern, quantifier)? else {
                continue;
            };
            self.mark_as_relevant(self.node(node).owner)?;
            self.mam_add_shared_enode(mam, node);
        }
        while let Some(term) = todo.pop() {
            if self.m.is_ground(term) {
                if let Some(node) = self.get_ground_enode(mam, term, quantifier)? {
                    self.mam_add_shared_enode(mam, node);
                }
            } else {
                for index in 0..self.m.get_num_args(term) {
                    let arg = self.m.get_arg(term, index);
                    if self.m.kinds[arg as usize] != KIND_VAR {
                        todo.push(arg);
                    }
                }
            }
        }
        Ok(())
    }

    fn mam_add_shared_enode(&mut self, mam: MamKind, node: EnodeId) {
        if !self.qmanager.mam_mut(mam).shared_enodes.insert(node) {
            return;
        }
        self.push_trail(TrailClosure::Mam(MamClosure::SharedEnode { mam, node }));
    }

    /// add_candidate, with compress_candidates, which keeps the first of each candidate once there
    /// are many, as match does.
    fn mam_add_candidate_to(&mut self, mam: MamKind, tree: TreeId, node: EnodeId) {
        let matcher = self.qmanager.mam_mut(mam);
        let code = matcher.code.tree_mut(tree);
        if code.candidates.is_empty() {
            matcher.to_match.push(tree);
        }
        let code = matcher.code.tree_mut(tree);
        code.candidates.push(node);
        if code.candidates.len() < code.candidate_gc_threshold {
            return;
        }
        let mut seen = HashSet::new();
        code.candidates.retain(|candidate| seen.insert(*candidate));
        if 2 * code.candidates.len() > code.candidate_gc_threshold {
            code.candidate_gc_threshold *= 2;
        }
    }

    pub fn mam_relevant_eh(&mut self, mam: MamKind, node: EnodeId, is_lazy: bool) {
        let lbl_hash = self.node(node).lbl_hash;
        if lbl_hash != -1 {
            self.mam_update_lbls(mam, node, lbl_hash);
        }
        if self.node(node).num_args() == 0 {
            return;
        }
        let decl = self.node(node).decl;
        let hash = self.get_label_hash(mam, decl) as i32;
        if self.qmanager.mam(mam).clbls.contains(&decl) {
            self.mam_update_lbls(mam, node, hash);
        }
        if self.qmanager.mam(mam).plbls.contains(&decl) {
            self.mam_update_children_plbls(mam, node, hash);
        }
        let tree = self.qmanager.mam(mam).trees.get(&decl).copied();
        if !is_lazy && let Some(tree) = tree {
            self.mam_add_candidate_to(mam, tree, node);
        }
    }

    fn mam_is_eq_mod_merge(&self, mam: MamKind, first: EnodeId, second: EnodeId) -> bool {
        let first_root = self.root(first);
        let second_root = self.root(second);
        let matcher = self.qmanager.mam(mam);
        first_root == second_root
            || (Some(first_root) == matcher.r1 && Some(second_root) == matcher.r2)
            || (Some(first_root) == matcher.r2 && Some(second_root) == matcher.r1)
    }

    /// collect_parents: walks the path tree level by level from the merged class, visiting each
    /// parent once per level, and hands the terms where a path ends to that path's code. The mark
    /// of a parent says it was visited at this level, and the second mark of a root says it is
    /// queued for the next.
    fn mam_collect_parents(&mut self, mam: MamKind, start: EnodeId, head: Option<PathTreeId>) {
        let Some(head) = head else {
            return;
        };
        let mut levels = vec![head];
        self.qmanager.mam_mut(mam).path_tree_mut(head).todo = Some(vec![start]);
        let mut level_index = 0;
        while level_index < levels.len() {
            let level = levels[level_index];
            level_index += 1;
            let level_node = self.qmanager.mam_mut(mam).path_tree_mut(level);
            let nodes = level_node.todo.take().unwrap_or_default();
            let filter = level_node.filter;
            let filter_high = level_node.filter_high;
            for node in nodes {
                let child = self.root(node);
                if self.node(child).plbls & filter == 0
                    && self.node(child).plbls_high & filter_high == 0
                {
                    continue;
                }
                for parent_index in 0..self.node(child).parents.len() {
                    let parent = self.node(child).parents[parent_index];
                    if self.node(parent).is_eq() {
                        continue;
                    }
                    let label = self.node(parent).decl;
                    let parent_root = self.root(parent);
                    let parent_cg = self.node(parent).cg;
                    let label_hash = self.get_label_hash(mam, label) as i32;
                    if !has_hash(filter, filter_high, label_hash)
                        || self.node(parent).is_marked()
                        || (parent_cg != parent
                            && self.mam_is_eq_mod_merge(mam, parent_cg, parent_root))
                        || !self.is_relevant(self.node(parent).owner)
                    {
                        continue;
                    }
                    let mut tree = Some(level);
                    while let Some(current) = tree {
                        let node = self.qmanager.mam(mam).path_tree(current);
                        tree = node.sibling;
                        let (tree_label, arg_index, ground_arg, ground_arg_index, code, next) = (
                            node.label,
                            node.arg_index,
                            node.ground_arg,
                            node.ground_arg_index,
                            node.code,
                            node.first_child,
                        );
                        if tree_label != label
                            || arg_index >= self.node(parent).num_args()
                            || self.enode_arena.get_arg_root(parent, arg_index) != child
                        {
                            continue;
                        }
                        if let Some(ground_arg) = ground_arg {
                            let parent_arg = self.node(parent).get_arg(ground_arg_index);
                            if !self.mam_is_eq_mod_merge(mam, ground_arg, parent_arg) {
                                continue;
                            }
                        }
                        if let Some(code) = code {
                            self.mam_add_candidate_to(mam, code, parent);
                        }
                        let Some(next) = next else {
                            continue;
                        };
                        let is_queued = self.node(parent_root).is_marked2();
                        let next_node = self.qmanager.mam_mut(mam).path_tree_mut(next);
                        if next_node.todo.is_none() {
                            next_node.todo = Some(Vec::new());
                            levels.push(next);
                        }
                        if !is_queued && let Some(todo) = next_node.todo.as_mut() {
                            todo.push(parent_root);
                        }
                    }
                    self.node_mut(parent).set_is_marked(true);
                    self.qmanager.mam_mut(mam).visited_parents.push(parent);
                    if !self.node(parent_root).is_marked2() {
                        self.node_mut(parent_root).set_is_marked2(true);
                        self.qmanager.mam_mut(mam).queued_roots.push(parent_root);
                    }
                }
            }
            let visited_parents = mem::take(&mut self.qmanager.mam_mut(mam).visited_parents);
            for parent in &visited_parents {
                self.node_mut(*parent).set_is_marked(false);
            }
            let queued_roots = mem::take(&mut self.qmanager.mam_mut(mam).queued_roots);
            for root in &queued_roots {
                self.node_mut(*root).set_is_marked2(false);
            }
            let matcher = self.qmanager.mam_mut(mam);
            matcher.visited_parents = visited_parents;
            matcher.visited_parents.clear();
            matcher.queued_roots = queued_roots;
            matcher.queued_roots.clear();
        }
    }

    fn mam_process_pc(&mut self, mam: MamKind, r1: EnodeId, r2: EnodeId) {
        if (self.node(r1).plbls == 0 && self.node(r1).plbls_high == 0)
            || (self.node(r2).lbls == 0 && self.node(r2).lbls_high == 0)
        {
            return;
        }
        for parent_hash in 0..64 {
            if !has_hash(self.node(r1).plbls, self.node(r1).plbls_high, parent_hash) {
                continue;
            }
            if self.check_canceled() {
                return;
            }
            for child_hash in 0..64 {
                if has_hash(self.node(r2).lbls, self.node(r2).lbls_high, child_hash) {
                    let key = (parent_hash * 64 + child_hash) as u32;
                    let head = self.qmanager.mam(mam).pc.get(&key).copied();
                    self.mam_collect_parents(mam, r1, head);
                }
            }
        }
    }

    fn mam_process_pp(&mut self, mam: MamKind, r1: EnodeId, r2: EnodeId) {
        if (self.node(r1).plbls == 0 && self.node(r1).plbls_high == 0)
            || (self.node(r2).plbls == 0 && self.node(r2).plbls_high == 0)
        {
            return;
        }
        for first_hash in 0..64 {
            if !has_hash(self.node(r1).plbls, self.node(r1).plbls_high, first_hash) {
                continue;
            }
            if self.check_canceled() {
                return;
            }
            for second_hash in 0..64 {
                if !has_hash(self.node(r2).plbls, self.node(r2).plbls_high, second_hash) {
                    continue;
                }
                let is_swapped = first_hash > second_hash;
                let (low_hash, high_hash) = if is_swapped {
                    (second_hash, first_hash)
                } else {
                    (first_hash, second_hash)
                };
                let (low_root, high_root) = if is_swapped { (r2, r1) } else { (r1, r2) };
                let key = (low_hash * 64 + high_hash) as u32;
                let Some(entry) = self.qmanager.mam(mam).pp.get(&key).copied() else {
                    continue;
                };
                let is_low_smaller =
                    self.node(low_root).parents.len() <= self.node(high_root).parents.len();
                if low_hash == high_hash {
                    if is_low_smaller {
                        self.mam_collect_parents(mam, low_root, entry[0]);
                    } else {
                        self.mam_collect_parents(mam, high_root, entry[0]);
                    }
                } else if is_low_smaller {
                    self.mam_collect_parents(mam, low_root, entry[0]);
                } else {
                    self.mam_collect_parents(mam, high_root, entry[1]);
                }
            }
        }
    }

    /// add_eq_eh: r2's labels take r1's after the paths are followed.
    pub fn mam_add_eq_eh(&mut self, mam: MamKind, r1: EnodeId, r2: EnodeId) {
        self.qmanager.mam_mut(mam).r1 = Some(r1);
        self.qmanager.mam_mut(mam).r2 = Some(r2);
        self.mam_process_pc(mam, r1, r2);
        self.mam_process_pc(mam, r2, r1);
        self.mam_process_pp(mam, r1, r2);
        self.qmanager.mam_mut(mam).r1 = None;
        self.qmanager.mam_mut(mam).r2 = None;
        let second = self.node(r2);
        let entry = MamTrail::AddEq {
            r2,
            lbls: second.lbls,
            lbls_high: second.lbls_high,
            plbls: second.plbls,
            plbls_high: second.plbls_high,
        };
        self.qmanager.mam_mut(mam).trail.push(entry);
        let first = self.node(r1);
        let (lbls, lbls_high, plbls, plbls_high) =
            (first.lbls, first.lbls_high, first.plbls, first.plbls_high);
        let second = self.node_mut(r2);
        second.lbls |= lbls;
        second.lbls_high |= lbls_high;
        second.plbls |= plbls;
        second.plbls_high |= plbls_high;
    }

    /// The interpreter's execute, with its matches handed to the quantifier manager.
    fn mam_execute(&mut self, mam: MamKind, tree: TreeId) -> Result<bool, SmtError> {
        let mut interpreter = mem::take(&mut self.qmanager.mam_mut(mam).interpreter);
        let result = interpreter.execute(self, mam, tree);
        let flushed = self.mam_add_matches(&mut interpreter);
        self.qmanager.mam_mut(mam).interpreter = interpreter;
        let result = result?;
        flushed?;
        Ok(result)
    }

    /// The interpreter's execute_core, with its matches handed to the quantifier manager.
    fn mam_execute_core(
        &mut self,
        mam: MamKind,
        tree: TreeId,
        node: EnodeId,
    ) -> Result<bool, SmtError> {
        let mut interpreter = mem::take(&mut self.qmanager.mam_mut(mam).interpreter);
        let result = interpreter.execute_core(self, mam, tree, node);
        let flushed = self.mam_add_matches(&mut interpreter);
        self.qmanager.mam_mut(mam).interpreter = interpreter;
        let result = result?;
        flushed?;
        Ok(result)
    }

    /// onMatch for each match of the run, in the order the interpreter found them.
    fn mam_add_matches(&mut self, interpreter: &mut Interpreter) -> Result<(), SmtError> {
        let matches = mem::take(&mut interpreter.matches);
        let bindings = mem::take(&mut interpreter.match_bindings);
        let mut result = Ok(());
        for found in &matches {
            result = self.qmanager_add_instance(
                found.quantifier,
                &bindings[found.start..found.start + found.len],
                found.max_generation,
            );
            if result.is_err() {
                break;
            }
        }
        interpreter.matches = matches;
        interpreter.matches.clear();
        interpreter.match_bindings = bindings;
        interpreter.match_bindings.clear();
        result
    }

    pub fn mam_match(&mut self, mam: MamKind) -> Result<(), SmtError> {
        let to_match = self.qmanager.mam(mam).to_match.clone();
        for tree in to_match {
            if !self.mam_execute(mam, tree)? {
                return Ok(());
            }
            self.qmanager.mam_mut(mam).code.tree_mut(tree).candidates = Vec::new();
        }
        self.qmanager.mam_mut(mam).to_match = Vec::new();
        if !self.qmanager.mam(mam).new_patterns.is_empty() {
            self.mam_match_new_patterns(mam)?;
        }
        Ok(())
    }

    /// match_new_patterns: one temporary tree per label, in the order the labels first appear, run
    /// against the relevant terms with the label.
    fn mam_match_new_patterns(&mut self, mam: MamKind) -> Result<(), SmtError> {
        let mut tmp_trees: OrderedMap<Decl, TreeId> = OrderedMap::new();
        let new_patterns = self.qmanager.mam(mam).new_patterns.clone();
        for mp in &new_patterns {
            if self.check_canceled() {
                break;
            }
            let label = self.m.decls[mp.patterns[0] as usize];
            if self.enodes_of(label).is_empty() {
                continue;
            }
            match tmp_trees.get(&label).copied() {
                None => {
                    let tree = self.compiler_mk_tree(mam, mp.quantifier, &mp.patterns, 0, false)?;
                    tmp_trees.insert(label, tree);
                }
                Some(tree) => {
                    self.compiler_insert(mam, tree, mp.quantifier, &mp.patterns, 0, true)?;
                }
            }
        }
        let entries: Vec<(Decl, TreeId)> = tmp_trees
            .iter()
            .map(|(label, tree)| (*label, *tree))
            .collect();
        for (label, tree) in entries {
            let mut index = 0;
            while index < self.enodes_of(label).len() {
                let node = self.enodes_of(label)[index];
                if self.is_relevant(self.node(node).owner) {
                    self.mam_execute_core(mam, tree, node)?;
                }
                index += 1;
            }
        }
        self.qmanager.mam_mut(mam).new_patterns = Vec::new();
        Ok(())
    }

    /// rematch: every code tree, in the order of their labels' small ids, against every relevant
    /// term.
    pub fn mam_rematch(&mut self, mam: MamKind) -> Result<(), SmtError> {
        let mut entries: Vec<(Decl, TreeId)> = self
            .qmanager
            .mam(mam)
            .trees
            .iter()
            .map(|(label, tree)| (*label, *tree))
            .collect();
        let func_decls = &self.m.func_decls;
        entries.sort_by_key(|entry| func_decls[entry.0 as usize].small_id);
        for (label, tree) in entries {
            let mut index = 0;
            while index < self.enodes_of(label).len() {
                let node = self.enodes_of(label)[index];
                if self.is_relevant(self.node(node).owner) {
                    self.mam_execute_core(mam, tree, node)?;
                }
                index += 1;
            }
        }
        Ok(())
    }

    pub fn mam_pop_scope(&mut self, mam: MamKind, num_scopes: u32) {
        let matcher = self.qmanager.mam_mut(mam);
        for index in 0..matcher.to_match.len() {
            let tree = matcher.to_match[index];
            matcher.code.tree_mut(tree).candidates = Vec::new();
        }
        matcher.to_match = Vec::new();
        matcher.new_patterns = Vec::new();
        let limit = matcher.trail_scopes[matcher.trail_scopes.len() - num_scopes as usize];
        while self.qmanager.mam(mam).trail.len() > limit {
            if let Some(entry) = self.qmanager.mam_mut(mam).trail.pop() {
                self.mam_undo_trail(mam, entry);
            }
        }
        let matcher = self.qmanager.mam_mut(mam);
        let new_len = matcher.trail_scopes.len() - num_scopes as usize;
        matcher.trail_scopes.truncate(new_len);
    }
}
