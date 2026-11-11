//! Ported from Z3 (src/smt/mam.cpp), MIT license, see z3-license.txt, through
//! `mam-interpreter.ts`. The interpreter of Z3's matching abstract machine: it runs a code tree
//! against a term, backtracking through the choices of BIND, CONTINUE and CHOOSE, and reports each
//! match.
//!
//! The interpreter keeps the context and its `onMatch`. It runs with the context borrowed for
//! reading, and the code trees it runs are its matcher's (`Mam::code`), read through the context.
//! `onMatch` is always the quantifier manager's `addInstance`, which writes to the context, so a
//! YIELD records its match in `matches`, in order, and the matcher hands them to
//! `qmanager_add_instance` when the run returns (`e_matching.rs`).

use std::collections::HashSet;

use crate::core::ast::{Decl, Expr, OP_ITE};
use crate::core::context::Context;
use crate::core::e_matching::MamKind;
use crate::core::enode::EnodeId;
use crate::core::mam_compiler::{
    CodeTrees, InstrId, Instruction, JOINT_GROUND, JOINT_NESTED, JOINT_VAR, Joint, OP_BIND,
    OP_CFILTER, OP_CHECK, OP_CHOOSE, OP_COMPARE, OP_CONTINUE, OP_FILTER, OP_GET_CGR, OP_GET_ENODE,
    OP_INIT, OP_IS_CGR, OP_NOOP, OP_PFILTER, OP_YIELD, TreeId, set_at,
};
use crate::util::error::SmtError;

/// A match a YIELD reported: the quantifier, its bindings in `Interpreter::match_bindings`, and the
/// largest generation of a term the match went through.
#[derive(Clone, Copy, Debug)]
pub struct PendingMatch {
    pub quantifier: Expr,
    pub start: usize,
    pub len: usize,
    pub max_generation: u32,
}

/// The terms a CONTINUE goes through: all the terms with its label, or the parents a joint gave.
#[derive(Clone, Debug)]
enum Candidates {
    All(Decl),
    Some(Vec<EnodeId>),
}

/// backtrack_point: the instruction to resume, the generation to restore, the term a BIND is at,
/// and the terms a CONTINUE goes through.
#[derive(Clone, Debug)]
struct BacktrackPoint {
    instr: InstrId,
    old_max_generation: u32,
    curr: Option<EnodeId>,
    candidates: Candidates,
    index: usize,
    end: usize,
}

// GET_CGR1 to GET_CGR6 filter their arguments by the parent labels, GET_CGRN does not.
const MAX_FILTERED_GET_CGR_ARGS: u32 = 6;

fn get_candidates<'a>(context: &'a Context, candidates: &'a Candidates) -> &'a [EnodeId] {
    match candidates {
        Candidates::All(label) => context.enodes_of(*label),
        Candidates::Some(nodes) => nodes,
    }
}

fn missing_register() -> SmtError {
    SmtError::Invariant("the matcher read an empty register".into())
}

#[derive(Clone, Debug, Default)]
pub struct Interpreter {
    registers: Vec<Option<EnodeId>>,
    backtrack_stack: Vec<BacktrackPoint>,
    top: usize,
    // m_max_generation: the largest generation of a term the match went through.
    max_generation: u32,
    // The arguments of a GET_CGR.
    args: Vec<EnodeId>,
    /// The matches of the run, which the matcher hands to `onMatch`.
    pub matches: Vec<PendingMatch>,
    pub match_bindings: Vec<EnodeId>,
}

impl Interpreter {
    fn update_max_generation(&mut self, context: &Context, node: EnodeId) {
        self.max_generation = self.max_generation.max(context.get_generation(node));
    }

    fn get_register(&self, reg: u32) -> Option<EnodeId> {
        self.registers.get(reg as usize).copied().flatten()
    }

    fn push_point(&mut self, instr: InstrId, old_max_generation: u32) -> usize {
        if self.top == self.backtrack_stack.len() {
            self.backtrack_stack.push(BacktrackPoint {
                instr,
                old_max_generation,
                curr: None,
                candidates: Candidates::Some(Vec::new()),
                index: 0,
                end: 0,
            });
        }
        let point = &mut self.backtrack_stack[self.top];
        point.instr = instr;
        point.old_max_generation = old_max_generation;
        self.top += 1;
        self.top - 1
    }

    /// get_first_f_app and get_next_f_app: the next congruence root with the label in the class.
    fn get_next_f_app(
        &mut self,
        context: &Context,
        label: Decl,
        num_args: u32,
        first: EnodeId,
        start: Option<EnodeId>,
    ) -> Option<EnodeId> {
        let mut curr = match start {
            None => first,
            Some(start) => context.node(start).next,
        };
        if start.is_some() && curr == first {
            return None;
        }
        loop {
            let node = context.node(curr);
            if node.decl == label && context.enode_arena.is_cgr(curr) && node.num_args() == num_args
            {
                self.update_max_generation(context, curr);
                return Some(curr);
            }
            curr = node.next;
            if curr == first {
                return None;
            }
        }
    }

    /// exec_is_cgr: whether the class has a term with the label and the arguments of the
    /// registers.
    fn is_cgr(&mut self, context: &Context, instr: &Instruction) -> bool {
        let mut args = Vec::with_capacity(instr.regs.len());
        for reg in &instr.regs {
            let Some(node) = self.get_register(*reg) else {
                return false;
            };
            args.push(context.root(node));
        }
        let Some(first) = self.get_register(instr.reg) else {
            return false;
        };
        let mut node = first;
        loop {
            let enode = context.node(node);
            if enode.decl == instr.label
                && enode.num_args() == instr.num_args
                && args.iter().enumerate().all(|(index, arg)| {
                    context.enode_arena.get_arg_root(node, index as u32) == *arg
                })
            {
                self.update_max_generation(context, node);
                return true;
            }
            node = enode.next;
            if node == first {
                return false;
            }
        }
    }

    fn is_relevant_parent(
        context: &Context,
        parent: EnodeId,
        decl: Decl,
        arg_index: u32,
        child: EnodeId,
    ) -> bool {
        let node = context.node(parent);
        node.decl == decl
            && arg_index < node.num_args()
            && context.is_relevant(node.owner)
            && context.enode_arena.is_cgr(parent)
            && context.enode_arena.get_arg_root(parent, arg_index) == child
    }

    /// mk_depth1_vector: the relevant decl-parents of the class of node where it is argument
    /// arg_index. init_continue drops a vector of limit terms or more, so this stops at limit and
    /// returns None.
    fn get_depth1_vector(
        context: &Context,
        node: EnodeId,
        decl: Decl,
        arg_index: u32,
        limit: usize,
    ) -> Option<Vec<EnodeId>> {
        let root = context.root(node);
        let mut result = Vec::new();
        for parent in &context.node(root).parents {
            if !Interpreter::is_relevant_parent(context, *parent, decl, arg_index, root) {
                continue;
            }
            if result.len() + 1 >= limit {
                return None;
            }
            result.push(*parent);
        }
        Some(result)
    }

    /// mk_depth2_vector, which stops at limit like get_depth1_vector.
    fn get_depth2_vector(
        &self,
        context: &Context,
        joint: &Joint,
        decl: Decl,
        arg_index: u32,
        limit: usize,
    ) -> Option<Vec<EnodeId>> {
        let node = self.get_register(joint.reg)?;
        let root = context.root(node);
        if context.node(root).parents.is_empty() {
            return None;
        }
        let mut result = Vec::new();
        for parent in &context.node(root).parents {
            if !Interpreter::is_relevant_parent(context, *parent, joint.decl, joint.arg_pos, root) {
                continue;
            }
            let parent_root = context.root(*parent);
            for grandparent in &context.node(parent_root).parents {
                if !Interpreter::is_relevant_parent(
                    context,
                    *grandparent,
                    decl,
                    arg_index,
                    parent_root,
                ) {
                    continue;
                }
                if result.len() + 1 >= limit {
                    return None;
                }
                result.push(*grandparent);
            }
        }
        Some(result)
    }

    /// SET_VAR's filter: whether the class of each input register has a parent with the label.
    fn has_parent_labels(&self, context: &Context, instr: &Instruction) -> Result<bool, SmtError> {
        for reg in &instr.regs {
            let root = context.root(self.get_register(*reg).ok_or_else(missing_register)?);
            let node = context.node(root);
            if node.plbls & instr.lbl_low == 0 && node.plbls_high & instr.lbl_high == 0 {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn get_joint_node(&self, joint: &Joint) -> Option<EnodeId> {
        if joint.kind == JOINT_GROUND {
            return joint.enode;
        }
        if joint.kind == JOINT_VAR {
            return self.get_register(joint.reg);
        }
        None
    }

    /// init_continue: the smallest candidate vector among the joints, or all terms with the
    /// label.
    fn init_continue(
        &mut self,
        context: &Context,
        instr_id: InstrId,
        instr: &Instruction,
    ) -> Option<EnodeId> {
        let label = instr.label;
        let all = context.enodes_of(label);
        for joint in &instr.joints {
            let Some(node) = self.get_joint_node(joint) else {
                continue;
            };
            let root = context.node(context.root(node));
            if root.plbls & instr.lbl_low == 0 && root.plbls_high & instr.lbl_high == 0 {
                return None;
            }
            if root.parents.is_empty() {
                return None;
            }
        }
        let mut best: Option<Vec<EnodeId>> = None;
        for (arg_index, joint) in instr.joints.iter().enumerate() {
            let node = self.get_joint_node(joint);
            let limit = match &best {
                None => all.len(),
                Some(best) => all.len().min(best.len()),
            };
            let current = match node {
                Some(node) => {
                    Interpreter::get_depth1_vector(context, node, label, arg_index as u32, limit)
                }
                None if joint.kind == JOINT_NESTED => {
                    self.get_depth2_vector(context, joint, label, arg_index as u32, limit)
                }
                None => None,
            };
            let Some(current) = current else {
                continue;
            };
            if current.len() >= all.len()
                || best
                    .as_ref()
                    .is_some_and(|best| current.len() >= best.len())
            {
                continue;
            }
            if current.is_empty() {
                return None;
            }
            best = Some(current);
        }
        let candidates = match best {
            Some(best) => Candidates::Some(best),
            None => Candidates::All(label),
        };
        let nodes = get_candidates(context, &candidates);
        let end = nodes.len();
        let mut index = 0;
        while index < end {
            let node = context.node(nodes[index]);
            if node.num_args() == instr.num_args && context.is_relevant(node.owner) {
                break;
            }
            index += 1;
        }
        if index == end {
            return None;
        }
        let found = nodes[index];
        let point = self.push_point(instr_id, self.max_generation);
        let point = &mut self.backtrack_stack[point];
        point.candidates = candidates;
        point.index = index;
        point.end = end;
        self.update_max_generation(context, found);
        Some(found)
    }

    fn set_args(&mut self, context: &Context, oreg: u32, node: EnodeId, num_args: u32) {
        for index in 0..num_args {
            let arg = context.node(node).get_arg(index);
            set_at(
                &mut self.registers,
                (oreg + index) as usize,
                Some(arg),
                None,
            );
        }
    }

    /// The backtracking step of execute_core: the instruction to resume at, or None when the top
    /// choice is exhausted and was popped.
    fn resume(
        &mut self,
        context: &Context,
        code: &CodeTrees,
        point_index: usize,
    ) -> Result<Option<InstrId>, SmtError> {
        let instr_id = self.backtrack_stack[point_index].instr;
        let instr = code.instr(instr_id);
        if instr.op == OP_CHOOSE {
            self.top -= 1;
            return Ok(instr.alt);
        }
        if instr.op == OP_BIND {
            let first = self.get_register(instr.reg).ok_or_else(missing_register)?;
            let curr = self.backtrack_stack[point_index].curr;
            let Some(node) = self.get_next_f_app(context, instr.label, instr.num_args, first, curr)
            else {
                self.top -= 1;
                return Ok(None);
            };
            self.backtrack_stack[point_index].curr = Some(node);
            self.set_args(context, instr.oreg, node, instr.num_args);
            return Ok(instr.next);
        }
        let end = self.backtrack_stack[point_index].end;
        let mut index = self.backtrack_stack[point_index].index + 1;
        while index < end {
            let node =
                get_candidates(context, &self.backtrack_stack[point_index].candidates)[index];
            let enode = context.node(node);
            if enode.num_args() == instr.num_args && context.is_relevant(enode.owner) {
                self.backtrack_stack[point_index].index = index;
                self.update_max_generation(context, node);
                self.set_args(context, instr.oreg, node, instr.num_args);
                return Ok(instr.next);
            }
            index += 1;
        }
        self.backtrack_stack[point_index].index = index;
        self.top -= 1;
        Ok(None)
    }

    /// execute_core: runs the tree against a term, one instruction at a time, and backtracks when
    /// an instruction fails. It returns false when the search is canceled.
    pub fn execute_core(
        &mut self,
        context: &Context,
        mam: MamKind,
        tree: TreeId,
        node: EnodeId,
    ) -> Result<bool, SmtError> {
        let code = &context.qmanager.mam(mam).code;
        self.max_generation = context.get_generation(node);
        set_at(&mut self.registers, 0, Some(node), None);
        self.top = 0;
        let mut since_last_check = 0;
        let mut pc = Some(code.tree(tree).root);
        loop {
            let Some(instr_id) = pc else {
                if self.top == 0 {
                    return Ok(true);
                }
                let point_index = self.top - 1;
                self.max_generation = self.backtrack_stack[point_index].old_max_generation;
                let since = since_last_check;
                since_last_check += 1;
                if since > 100 {
                    since_last_check = 0;
                    if context.check_canceled() {
                        self.top = 0;
                        return Ok(false);
                    }
                }
                pc = self.resume(context, code, point_index)?;
                continue;
            };
            let instr = code.instr(instr_id);
            pc = None;
            match instr.op {
                OP_INIT => {
                    let first = self.get_register(0).ok_or_else(missing_register)?;
                    if context.node(first).num_args() == instr.num_args {
                        self.set_args(context, 1, first, instr.num_args);
                        pc = instr.next;
                    }
                }
                OP_COMPARE => {
                    if let (Some(first), Some(second)) =
                        (self.get_register(instr.reg), self.get_register(instr.reg2))
                        && context.root(first) == context.root(second)
                    {
                        pc = instr.next;
                    }
                }
                OP_CHECK => {
                    // Z3's hack for dynamically generated patterns: a ground if-then-else is not
                    // checked.
                    if let (Some(first), Some(second)) = (self.get_register(instr.reg), instr.enode)
                        && (context.root(first) == context.root(second)
                            || context.m.get_op(context.node(second).owner) == OP_ITE)
                    {
                        pc = instr.next;
                    }
                }
                OP_CFILTER | OP_FILTER | OP_PFILTER => {
                    let register = self.get_register(instr.reg).ok_or_else(missing_register)?;
                    let root = context.node(context.root(register));
                    let is_parent = instr.op == OP_PFILTER;
                    let low = if is_parent { root.plbls } else { root.lbls };
                    let high = if is_parent {
                        root.plbls_high
                    } else {
                        root.lbls_high
                    };
                    if low & instr.lbl_low != 0 || high & instr.lbl_high != 0 {
                        pc = instr.next;
                    }
                }
                OP_CHOOSE => {
                    self.push_point(instr_id, self.max_generation);
                    pc = instr.next;
                }
                OP_NOOP => pc = instr.next,
                OP_BIND => {
                    let old_max_generation = self.max_generation;
                    let first = self.get_register(instr.reg).ok_or_else(missing_register)?;
                    if let Some(found) =
                        self.get_next_f_app(context, instr.label, instr.num_args, first, None)
                    {
                        let point = self.push_point(instr_id, old_max_generation);
                        self.backtrack_stack[point].curr = Some(found);
                        self.set_args(context, instr.oreg, found, instr.num_args);
                        pc = instr.next;
                    }
                }
                OP_YIELD => {
                    let num_bindings = instr.regs.len();
                    let start = self.match_bindings.len();
                    for index in 0..num_bindings {
                        let binding = self
                            .get_register(instr.regs[num_bindings - index - 1])
                            .ok_or_else(missing_register)?;
                        self.match_bindings.push(binding);
                        self.update_max_generation(context, binding);
                    }
                    self.matches.push(PendingMatch {
                        quantifier: instr.quantifier,
                        start,
                        len: num_bindings,
                        max_generation: self.max_generation,
                    });
                }
                OP_GET_ENODE => {
                    set_at(&mut self.registers, instr.oreg as usize, instr.enode, None);
                    pc = instr.next;
                }
                OP_GET_CGR => {
                    if instr.num_args <= MAX_FILTERED_GET_CGR_ARGS
                        && !self.has_parent_labels(context, instr)?
                    {
                        continue;
                    }
                    self.args.clear();
                    for reg in &instr.regs {
                        let arg = self.get_register(*reg).ok_or_else(missing_register)?;
                        self.args.push(arg);
                    }
                    let Some(found) = context.find_congruent(instr.label, &self.args) else {
                        continue;
                    };
                    if !context.is_relevant(context.node(found).owner) {
                        continue;
                    }
                    self.update_max_generation(context, found);
                    set_at(&mut self.registers, instr.oreg as usize, Some(found), None);
                    pc = instr.next;
                }
                OP_IS_CGR => {
                    if self.is_cgr(context, instr) {
                        pc = instr.next;
                    }
                }
                OP_CONTINUE => {
                    if let Some(found) = self.init_continue(context, instr_id, instr) {
                        self.set_args(context, instr.oreg, found, instr.num_args);
                        pc = instr.next;
                    }
                }
                _ => {}
            }
        }
    }

    /// execute: runs the tree against its candidates. A tree that filters its candidates runs each
    /// term once.
    pub fn execute(
        &mut self,
        context: &Context,
        mam: MamKind,
        tree: TreeId,
    ) -> Result<bool, SmtError> {
        let code = context.qmanager.mam(mam).code.tree(tree);
        let mut seen = code.is_filtering_candidates.then(HashSet::new);
        for node in &code.candidates {
            if seen.as_ref().is_some_and(|seen| seen.contains(node))
                || !context.enode_arena.is_cgr(*node)
            {
                continue;
            }
            if context.check_canceled() || !self.execute_core(context, mam, tree, *node)? {
                return Ok(false);
            }
            if let Some(seen) = seen.as_mut() {
                seen.insert(*node);
            }
        }
        Ok(true)
    }
}
