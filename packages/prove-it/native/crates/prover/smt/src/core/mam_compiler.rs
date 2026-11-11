//! Ported from Z3 (src/smt/mam.cpp), MIT license, see z3-license.txt, through `mam-compiler.ts`.
//! The code trees of Z3's matching abstract machine and the compiler that builds them: each pattern
//! becomes a sequence of instructions, and the patterns that start with the same label share the
//! instructions they have in common, so a term is matched against all of them at once and the
//! matches come in Z3's order.
//!
//! The instructions and the code trees are objects linked to each other and named by the trail's
//! closures, so (design/smt-core.md, "Objects with identity") they live in a `CodeTrees` arena
//! owned by their matcher (`Mam::code`), named by `InstrId` and `TreeId` handles. The compiler keeps
//! the context and its matcher (`LabelHasher`), so its state is the struct `Compiler`, held by the
//! matcher, and its methods are `impl Context` methods named `compiler_<method>`, which take the
//! matcher they compile for.

use std::collections::HashMap;
use std::mem;

use crate::core::ast::{AstManager, Decl, Expr, KIND_VAR};
use crate::core::context::{Context, TrailClosure};
use crate::core::e_matching::{MamClosure, MamKind};
use crate::core::enode::EnodeId;
use crate::util::error::SmtError;

pub const OP_INIT: u8 = 0;
pub const OP_BIND: u8 = 1;
pub const OP_YIELD: u8 = 2;
pub const OP_COMPARE: u8 = 3;
pub const OP_CHECK: u8 = 4;
pub const OP_FILTER: u8 = 5;
pub const OP_CFILTER: u8 = 6;
pub const OP_PFILTER: u8 = 7;
pub const OP_CHOOSE: u8 = 8;
pub const OP_NOOP: u8 = 9;
pub const OP_CONTINUE: u8 = 10;
pub const OP_GET_ENODE: u8 = 11;
pub const OP_GET_CGR: u8 = 12;
pub const OP_IS_CGR: u8 = 13;

const JOINT_NULL: u8 = 0;
pub const JOINT_GROUND: u8 = 1;
pub const JOINT_VAR: u8 = 2;
pub const JOINT_NESTED: u8 = 3;

/// An instruction: its index in `CodeTrees::instrs`.
pub type InstrId = u32;
/// A code tree: its index in `CodeTrees::trees`.
pub type TreeId = u32;

/// A joint of a CONTINUE argument: a ground term, the register of a bound variable, or a depth-2
/// joint (f ... (g ... X ...) ...), with g, the position of X in it, and X's register.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Joint {
    pub kind: u8,
    pub enode: Option<EnodeId>,
    pub reg: u32,
    pub decl: Decl,
    pub arg_pos: u32,
}

const NULL_JOINT: Joint = Joint {
    kind: JOINT_NULL,
    enode: None,
    reg: 0,
    decl: -1,
    arg_pos: 0,
};

/// instruction and its subclasses in one shape. The fields an opcode does not use keep their
/// defaults. reg is the register of CHECK, COMPARE (m_reg1), the filters, and the input register
/// of BIND and IS_CGR. regs holds the input registers of GET_CGR and IS_CGR and the bindings of
/// YIELD.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Instruction {
    pub op: u8,
    pub next: Option<InstrId>,
    pub num_args: u32,
    pub reg: u32,
    pub reg2: u32,
    pub oreg: u32,
    pub label: Decl,
    pub enode: Option<EnodeId>,
    pub lbl_low: u32,
    pub lbl_high: u32,
    pub alt: Option<InstrId>,
    pub quantifier: Expr,
    pub regs: Vec<u32>,
    pub joints: Vec<Joint>,
}

impl Instruction {
    /// mkInstruction.
    fn new(op: u8) -> Instruction {
        Instruction {
            op,
            next: None,
            num_args: 0,
            reg: 0,
            reg2: 0,
            oreg: 0,
            label: -1,
            enode: None,
            lbl_low: 0,
            lbl_high: 0,
            alt: None,
            quantifier: -1,
            regs: Vec::new(),
            joints: Vec::new(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct CodeTree {
    pub root_label: Decl,
    pub num_args: u32,
    pub is_filtering_candidates: bool,
    pub num_regs: u32,
    pub num_choices: u32,
    pub root: InstrId,
    pub candidates: Vec<EnodeId>,
    /// code_tree::m_candidate_gc_threshold: the number of candidates at which duplicates are
    /// dropped.
    pub candidate_gc_threshold: usize,
}

/// The instructions and code trees of a matcher. Slots are never reused, so a closure on the trail
/// that names one never names a newer object.
#[derive(Clone, Debug, Default)]
pub struct CodeTrees {
    pub instrs: Vec<Instruction>,
    pub trees: Vec<CodeTree>,
}

impl CodeTrees {
    fn mk(&mut self, instr: Instruction) -> InstrId {
        self.instrs.push(instr);
        (self.instrs.len() - 1) as InstrId
    }

    pub fn instr(&self, id: InstrId) -> &Instruction {
        &self.instrs[id as usize]
    }

    pub fn instr_mut(&mut self, id: InstrId) -> &mut Instruction {
        &mut self.instrs[id as usize]
    }

    pub fn tree(&self, id: TreeId) -> &CodeTree {
        &self.trees[id as usize]
    }

    pub fn tree_mut(&mut self, id: TreeId) -> &mut CodeTree {
        &mut self.trees[id as usize]
    }
}

/// What the compiler needs from the matching abstract machine, implemented by the context for the
/// matcher it names (`e_matching.rs`).
pub trait LabelHasher {
    /// label_hasher.
    fn get_label_hash(&mut self, mam: MamKind, decl: Decl) -> u32;
    /// mk_enode: the enode of a ground term, internalized at the quantifier's generation if needed.
    fn get_ground_enode(
        &mut self,
        mam: MamKind,
        expr: Expr,
        quantifier: Expr,
    ) -> Result<Option<EnodeId>, SmtError>;
    /// The label hash of a ground term's enode, which set_lbl_hash gives it if it has none.
    fn get_lbl_hash(&mut self, mam: MamKind, node: EnodeId) -> i32;
}

const NOT_CHECKED: u8 = 0;
const CHECK_SET: u8 = 1;
const CHECK_SINGLETON: u8 = 2;

// FIND_BEST_CHILD_THRESHOLD and SIMPLE_SEQ_THRESHOLD.
const FIND_BEST_CHILD_THRESHOLD: u32 = 64;
const SIMPLE_SEQ_THRESHOLD: u32 = 4;

/// approx_set over 64 bits, in two words. A hash of -1 (a ground pattern without an enode) tests
/// bit 31 of the low word, as JavaScript's `1 << -1` does.
pub fn has_hash(low: u32, high: u32, hash: i32) -> bool {
    (if hash < 32 { low } else { high }) & (1u32 << (hash & 31)) != 0
}

/// `1 << hash` into the word of approx_set that holds it.
pub fn set_hash(low: &mut u32, high: &mut u32, hash: i32) {
    if hash < 32 {
        *low |= 1u32 << (hash & 31);
    } else {
        *high |= 1u32 << (hash & 31);
    }
}

/// `array[index] = value` on a JavaScript array, whose holes read as `fill`.
pub(crate) fn set_at<T: Clone>(values: &mut Vec<T>, index: usize, value: T, fill: T) {
    if index >= values.len() {
        values.resize(index + 1, fill);
    }
    values[index] = value;
}

fn mk_filter(op: u8, reg: u32, low: u32, high: u32) -> Instruction {
    let mut instr = Instruction::new(op);
    instr.reg = reg;
    instr.lbl_low = low;
    instr.lbl_high = high;
    instr
}

fn mk_singleton_filter(op: u8, reg: u32, hash: i32) -> Instruction {
    let mut instr = mk_filter(op, reg, 0, 0);
    set_hash(&mut instr.lbl_low, &mut instr.lbl_high, hash);
    instr
}

fn mk_compare(reg1: u32, reg2: u32) -> Instruction {
    let mut instr = Instruction::new(OP_COMPARE);
    instr.reg = reg1;
    instr.reg2 = reg2;
    instr
}

fn mk_check(reg: u32, enode: Option<EnodeId>) -> Instruction {
    let mut instr = Instruction::new(OP_CHECK);
    instr.reg = reg;
    instr.enode = enode;
    instr
}

fn mk_choose(alt: Option<InstrId>) -> Instruction {
    let mut instr = Instruction::new(OP_CHOOSE);
    instr.alt = alt;
    instr
}

fn mk_init(num_args: u32) -> Instruction {
    let mut instr = Instruction::new(OP_INIT);
    instr.num_args = num_args;
    instr
}

/// The size of a pattern and its number of unbound variables (get_stats).
fn get_stats(m: &AstManager, vars: &[i32], expr: Expr) -> (u32, u32) {
    let mut size = 0;
    let mut num_unbound_vars = 0;
    fn visit(m: &AstManager, vars: &[i32], term: Expr, size: &mut u32, num_unbound: &mut u32) {
        *size += 1;
        if m.is_ground(term) {
            return;
        }
        for index in 0..m.get_num_args(term) {
            let arg = m.get_arg(term, index);
            if m.kinds[arg as usize] == KIND_VAR {
                *size += 1;
                if vars[m.values[arg as usize] as usize] == -1 {
                    *num_unbound += 1;
                }
            } else {
                visit(m, vars, arg, size, num_unbound);
            }
        }
    }
    visit(m, vars, expr, &mut size, &mut num_unbound_vars);
    (size, num_unbound_vars)
}

/// get_num_bound_vars: the number of bound variables in a pattern, and whether it has unbound
/// ones.
fn get_num_bound_vars(m: &AstManager, vars: &[i32], expr: Expr) -> (u32, bool) {
    let mut count = 0;
    let mut has_unbound_vars = false;
    fn visit(m: &AstManager, vars: &[i32], term: Expr, count: &mut u32, has_unbound: &mut bool) {
        if m.is_ground(term) {
            return;
        }
        for index in 0..m.get_num_args(term) {
            let arg = m.get_arg(term, index);
            if m.kinds[arg as usize] != KIND_VAR {
                visit(m, vars, arg, count, has_unbound);
            } else if vars[m.values[arg as usize] as usize] != -1 {
                *count += 1;
            } else {
                *has_unbound = true;
            }
        }
    }
    visit(m, vars, expr, &mut count, &mut has_unbound_vars);
    (count, has_unbound_vars)
}

/// The patterns are the terms of a multi-pattern, and first_index picks the one the tree starts
/// with.
#[derive(Clone, Debug)]
pub struct Compiler {
    // The pattern each register holds, -1 for none.
    registers: Vec<Expr>,
    // m_todo: the registers whose patterns are still to be processed.
    todo: Vec<u32>,
    aux: Vec<u32>,
    // The register of each variable by de Bruijn index, -1 while it is unbound.
    vars: Vec<i32>,
    quantifier: Expr,
    patterns: Vec<Expr>,
    tree: TreeId,
    num_choices: u32,
    is_tmp_tree: bool,
    is_mp_already_processed: Vec<bool>,
    matched_exprs: HashMap<Expr, u32>,
    marks: Vec<u8>,
    to_reset: Vec<u32>,
    compatible: Vec<InstrId>,
    incompatible: Vec<InstrId>,
    seq: Vec<InstrId>,
}

impl Default for Compiler {
    fn default() -> Self {
        Compiler {
            registers: Vec::new(),
            todo: Vec::new(),
            aux: Vec::new(),
            vars: Vec::new(),
            quantifier: -1,
            patterns: Vec::new(),
            tree: TreeId::MAX,
            num_choices: 0,
            is_tmp_tree: false,
            is_mp_already_processed: Vec::new(),
            matched_exprs: HashMap::new(),
            marks: Vec::new(),
            to_reset: Vec::new(),
            compatible: Vec::new(),
            incompatible: Vec::new(),
            seq: Vec::new(),
        }
    }
}

impl Compiler {
    fn get_register(&self, reg: u32) -> Expr {
        self.registers.get(reg as usize).copied().unwrap_or(-1)
    }

    fn get_mark(&self, reg: u32) -> u8 {
        self.marks.get(reg as usize).copied().unwrap_or(NOT_CHECKED)
    }

    fn set_mark(&mut self, reg: u32, mark: u8) {
        set_at(&mut self.marks, reg as usize, mark, NOT_CHECKED);
    }

    fn set_register(&mut self, reg: u32, expr: Expr) {
        set_at(&mut self.registers, reg as usize, expr, -1);
    }

    fn erase_todo(&mut self, reg: u32) {
        if let Some(index) = self.todo.iter().position(|item| *item == reg) {
            self.todo.remove(index);
        }
    }
}

fn is_app(m: &AstManager, expr: Expr) -> bool {
    expr != -1 && m.kinds[expr as usize] != KIND_VAR
}

fn is_ground(m: &AstManager, expr: Expr) -> bool {
    expr != -1 && m.is_ground(expr)
}

impl Context {
    fn compiler(&mut self, mam: MamKind) -> &mut Compiler {
        &mut self.qmanager.mam_mut(mam).compiler
    }

    fn compiler_ref(&self, mam: MamKind) -> &Compiler {
        &self.qmanager.mam(mam).compiler
    }

    fn code(&mut self, mam: MamKind) -> &mut CodeTrees {
        &mut self.qmanager.mam_mut(mam).code
    }

    fn code_ref(&self, mam: MamKind) -> &CodeTrees {
        &self.qmanager.mam(mam).code
    }

    fn compiler_push_seq(&mut self, mam: MamKind, instr: Instruction) -> InstrId {
        let id = self.code(mam).mk(instr);
        self.compiler(mam).seq.push(id);
        id
    }

    fn compiler_init(
        &mut self,
        mam: MamKind,
        tree: TreeId,
        quantifier: Expr,
        patterns: &[Expr],
        first_index: usize,
    ) -> Result<(), SmtError> {
        let first = patterns[first_index];
        let num_decls = self.m.get_quantifier(quantifier)?.sorts.len();
        let first_args: Vec<Expr> = self.m.get_args(first);
        let compiler = &mut self.qmanager.mam_mut(mam).compiler;
        compiler.tree = tree;
        compiler.quantifier = quantifier;
        compiler.patterns = patterns.to_vec();
        compiler.num_choices = 0;
        compiler.todo = Vec::new();
        compiler.registers.fill(-1);
        for (index, arg) in first_args.into_iter().enumerate() {
            compiler.set_register(index as u32 + 1, arg);
            compiler.todo.push(index as u32 + 1);
        }
        while compiler.vars.len() < num_decls {
            compiler.vars.push(-1);
        }
        compiler.vars[..num_decls].fill(-1);
        Ok(())
    }

    /// all_args_are_bound_vars.
    fn compiler_is_all_args_bound_vars(&self, mam: MamKind, expr: Expr) -> bool {
        let m = &self.m;
        let vars = &self.compiler_ref(mam).vars;
        m.every_arg(expr, |arg, _| {
            m.kinds[arg as usize] == KIND_VAR && vars[m.values[arg as usize] as usize] != -1
        })
    }

    /// linearise_core: the registers in m_todo that do not need a BIND are processed first, then a
    /// single BIND or IS_CGR is produced, and the registers left and the new ones become m_todo.
    fn compiler_linearise_core(&mut self, mam: MamKind) -> Result<(), SmtError> {
        let todo = mem::take(&mut self.compiler(mam).todo);
        self.compiler(mam).aux.clear();
        let quantifier = self.compiler_ref(mam).quantifier;
        let mut first_app: Expr = -1;
        let mut first_app_reg = 0;
        let mut first_app_size = 0;
        let mut first_app_num_unbound_vars = 0;
        for &reg in &todo {
            let pattern = self.compiler_ref(mam).registers[reg as usize];
            if self.m.kinds[pattern as usize] == KIND_VAR {
                let var_index = self.m.values[pattern as usize] as usize;
                let var_reg = self.compiler_ref(mam).vars[var_index];
                if var_reg != -1 {
                    self.compiler_push_seq(mam, mk_compare(var_reg as u32, reg));
                } else {
                    self.compiler(mam).vars[var_index] = reg as i32;
                }
                continue;
            }
            if self.m.is_ground(pattern) {
                let enode = self.get_ground_enode(mam, pattern, quantifier)?;
                self.compiler_push_seq(mam, mk_check(reg, enode));
                self.compiler(mam).set_mark(reg, NOT_CHECKED);
                continue;
            }
            let matched_reg = self.compiler_ref(mam).matched_exprs.get(&pattern).copied();
            if let Some(matched_reg) = matched_reg
                && reg != matched_reg
            {
                self.compiler_push_seq(mam, mk_compare(matched_reg, reg));
                self.compiler(mam).set_mark(reg, NOT_CHECKED);
                continue;
            }
            self.compiler(mam).matched_exprs.insert(pattern, reg);
            if self.compiler_ref(mam).get_mark(reg) != CHECK_SINGLETON {
                let hash = self.get_label_hash(mam, self.m.decls[pattern as usize]);
                self.compiler_push_seq(mam, mk_singleton_filter(OP_FILTER, reg, hash as i32));
                self.compiler(mam).set_mark(reg, CHECK_SINGLETON);
            }
            if first_app == -1 {
                first_app = pattern;
                first_app_reg = reg;
                let stats = get_stats(&self.m, &self.compiler_ref(mam).vars, pattern);
                first_app_size = stats.0;
                first_app_num_unbound_vars = stats.1;
            } else if first_app_num_unbound_vars == 0 {
                self.compiler(mam).aux.push(reg);
            } else {
                let stats = get_stats(&self.m, &self.compiler_ref(mam).vars, pattern);
                if stats.1 == 0
                    || stats.0 > first_app_size
                    || (stats.0 == first_app_size && stats.1 < first_app_num_unbound_vars)
                {
                    self.compiler(mam).aux.push(first_app_reg);
                    first_app = pattern;
                    first_app_reg = reg;
                    first_app_size = stats.0;
                    first_app_num_unbound_vars = stats.1;
                } else {
                    self.compiler(mam).aux.push(reg);
                }
            }
        }
        if first_app != -1 {
            let label = self.m.decls[first_app as usize];
            let num_args = self.m.get_num_args(first_app) as u32;
            if self.compiler_is_all_args_bound_vars(mam, first_app) {
                let mut instr = Instruction::new(OP_IS_CGR);
                instr.label = label;
                instr.reg = first_app_reg;
                instr.num_args = num_args;
                let vars = &self.compiler_ref(mam).vars;
                let m = &self.m;
                instr.regs = m.map_args(first_app, |arg, _| {
                    vars[m.values[arg as usize] as usize] as u32
                });
                self.compiler_push_seq(mam, instr);
            } else {
                let tree = self.compiler_ref(mam).tree;
                let oreg = self.code_ref(mam).tree(tree).num_regs;
                self.code(mam).tree_mut(tree).num_regs += num_args;
                for index in 0..num_args {
                    let arg = self.m.get_arg(first_app, index as usize);
                    let compiler = self.compiler(mam);
                    compiler.set_register(oreg + index, arg);
                    compiler.aux.push(oreg + index);
                }
                let mut instr = Instruction::new(OP_BIND);
                instr.label = label;
                instr.num_args = num_args;
                instr.reg = first_app_reg;
                instr.oreg = oreg;
                self.compiler_push_seq(mam, instr);
                self.compiler(mam).num_choices += 1;
            }
            self.compiler(mam).set_mark(first_app_reg, NOT_CHECKED);
        }
        let compiler = self.compiler(mam);
        compiler.todo = mem::take(&mut compiler.aux);
        compiler.aux = todo;
        Ok(())
    }

    /// gen_mp_filter: compiles a pattern whose variables are all bound, and returns the register
    /// that gets the enode congruent to it.
    fn compiler_gen_mp_filter(&mut self, mam: MamKind, expr: Expr) -> Result<u32, SmtError> {
        let tree = self.compiler_ref(mam).tree;
        if self.m.is_ground(expr) {
            let oreg = self.code_ref(mam).tree(tree).num_regs;
            self.code(mam).tree_mut(tree).num_regs += 1;
            let mut instr = Instruction::new(OP_GET_ENODE);
            instr.oreg = oreg;
            let quantifier = self.compiler_ref(mam).quantifier;
            instr.enode = self.get_ground_enode(mam, expr, quantifier)?;
            self.compiler_push_seq(mam, instr);
            return Ok(oreg);
        }
        let mut iregs = Vec::new();
        for index in 0..self.m.get_num_args(expr) {
            let arg = self.m.get_arg(expr, index);
            iregs.push(if self.m.kinds[arg as usize] == KIND_VAR {
                self.compiler_ref(mam).vars[self.m.values[arg as usize] as usize] as u32
            } else {
                self.compiler_gen_mp_filter(mam, arg)?
            });
        }
        let oreg = self.code_ref(mam).tree(tree).num_regs;
        self.code(mam).tree_mut(tree).num_regs += 1;
        let mut instr = Instruction::new(OP_GET_CGR);
        instr.label = self.m.decls[expr as usize];
        instr.num_args = iregs.len() as u32;
        instr.oreg = oreg;
        instr.regs = iregs;
        let hash = self.get_label_hash(mam, instr.label);
        set_hash(&mut instr.lbl_low, &mut instr.lbl_high, hash as i32);
        self.compiler_push_seq(mam, instr);
        Ok(oreg)
    }

    /// linearise_multi_pattern: the other patterns of a multi-pattern, the one with the most bound
    /// variables first.
    fn compiler_linearise_multi_pattern(&mut self, mam: MamKind) -> Result<(), SmtError> {
        let patterns = self.compiler_ref(mam).patterns.clone();
        let quantifier = self.compiler_ref(mam).quantifier;
        for _round in 1..patterns.len() {
            let mut best: Expr = -1;
            let mut best_num_bound_vars = 0;
            let mut best_index = 0;
            let mut is_found_bounded_mp = false;
            for (index, pattern) in patterns.iter().enumerate() {
                if self.compiler_ref(mam).is_mp_already_processed[index] {
                    continue;
                }
                let counted = get_num_bound_vars(&self.m, &self.compiler_ref(mam).vars, *pattern);
                if !counted.1 {
                    best = *pattern;
                    best_index = index;
                    is_found_bounded_mp = true;
                    break;
                }
                if best == -1 || counted.0 > best_num_bound_vars {
                    best = *pattern;
                    best_num_bound_vars = counted.0;
                    best_index = index;
                }
            }
            if best == -1 {
                continue;
            }
            self.compiler(mam).is_mp_already_processed[best_index] = true;
            if is_found_bounded_mp {
                self.compiler_gen_mp_filter(mam, best)?;
                continue;
            }
            let tree = self.compiler_ref(mam).tree;
            let num_args = self.m.get_num_args(best);
            let oreg = self.code_ref(mam).tree(tree).num_regs;
            self.code(mam).tree_mut(tree).num_regs += num_args as u32;
            let mut has_depth1_joint = false;
            for index in 0..num_args {
                let arg = self.m.get_arg(best, index);
                let compiler = self.compiler(mam);
                compiler.set_register(oreg + index as u32, arg);
                compiler.todo.push(oreg + index as u32);
                let m = &self.m;
                if (m.kinds[arg as usize] == KIND_VAR
                    && self.compiler_ref(mam).vars[m.values[arg as usize] as usize] >= 0)
                    || (m.kinds[arg as usize] != KIND_VAR && m.is_ground(arg))
                {
                    has_depth1_joint = true;
                }
            }
            let mut joints = Vec::new();
            for index in 0..num_args {
                let arg = self.m.get_arg(best, index);
                let joint = if has_depth1_joint {
                    if self.m.kinds[arg as usize] == KIND_VAR {
                        let reg = self.compiler_ref(mam).vars[self.m.values[arg as usize] as usize];
                        if reg >= 0 {
                            Joint {
                                kind: JOINT_VAR,
                                reg: reg as u32,
                                ..NULL_JOINT
                            }
                        } else {
                            NULL_JOINT
                        }
                    } else if self.m.is_ground(arg) {
                        Joint {
                            kind: JOINT_GROUND,
                            enode: self.get_ground_enode(mam, arg, quantifier)?,
                            ..NULL_JOINT
                        }
                    } else {
                        NULL_JOINT
                    }
                } else if self.m.kinds[arg as usize] == KIND_VAR {
                    NULL_JOINT
                } else {
                    let m = &self.m;
                    let vars = &self.compiler_ref(mam).vars;
                    let mut arg_pos: i64 = -1;
                    let mut inner_index = 0;
                    while inner_index < m.get_num_args(arg) && arg_pos == -1 {
                        let inner_arg = m.get_arg(arg, inner_index);
                        if m.kinds[inner_arg as usize] == KIND_VAR
                            && vars[m.values[inner_arg as usize] as usize] >= 0
                        {
                            arg_pos = inner_index as i64;
                        }
                        inner_index += 1;
                    }
                    if arg_pos == -1 {
                        NULL_JOINT
                    } else {
                        let var = m.get_arg(arg, arg_pos as usize);
                        Joint {
                            kind: JOINT_NESTED,
                            enode: None,
                            reg: vars[m.values[var as usize] as usize] as u32,
                            decl: m.decls[arg as usize],
                            arg_pos: arg_pos as u32,
                        }
                    }
                };
                joints.push(joint);
            }
            let mut instr = Instruction::new(OP_CONTINUE);
            instr.label = self.m.decls[best as usize];
            instr.num_args = num_args as u32;
            instr.oreg = oreg;
            instr.joints = joints;
            let hash = self.get_label_hash(mam, instr.label);
            set_hash(&mut instr.lbl_low, &mut instr.lbl_high, hash as i32);
            self.compiler_push_seq(mam, instr);
            self.compiler(mam).num_choices += 1;
            while !self.compiler_ref(mam).todo.is_empty() {
                self.compiler_linearise_core(mam)?;
            }
        }
        Ok(())
    }

    /// linearise: the instructions for the registers in m_todo, appended after head.
    fn compiler_linearise(
        &mut self,
        mam: MamKind,
        head: InstrId,
        first_index: usize,
    ) -> Result<(), SmtError> {
        self.compiler(mam).seq = Vec::new();
        self.compiler(mam).matched_exprs.clear();
        while !self.compiler_ref(mam).todo.is_empty() {
            self.compiler_linearise_core(mam)?;
        }
        let num_patterns = self.compiler_ref(mam).patterns.len();
        if num_patterns > 1 {
            self.compiler(mam).is_mp_already_processed = (0..num_patterns)
                .map(|index| index == first_index)
                .collect();
            self.compiler_linearise_multi_pattern(mam)?;
        }
        let quantifier = self.compiler_ref(mam).quantifier;
        let num_decls = self.m.get_quantifier(quantifier)?.sorts.len();
        if self.compiler_ref(mam).vars[..num_decls].contains(&-1) {
            return Ok(());
        }
        let mut instr = Instruction::new(OP_YIELD);
        instr.quantifier = quantifier;
        instr.num_args = num_decls as u32;
        instr.regs = self.compiler_ref(mam).vars[..num_decls]
            .iter()
            .map(|reg| *reg as u32)
            .collect();
        self.compiler_push_seq(mam, instr);
        let seq = mem::take(&mut self.compiler(mam).seq);
        let code = self.code(mam);
        let mut curr = head;
        for next in &seq {
            code.instr_mut(curr).next = Some(*next);
            curr = *next;
        }
        self.compiler(mam).seq = seq;
        Ok(())
    }

    fn compiler_set_next(&mut self, mam: MamKind, instr: InstrId, next: Option<InstrId>) {
        if !self.compiler_ref(mam).is_tmp_tree {
            let old = self.code_ref(mam).instr(instr).next;
            self.push_trail(TrailClosure::Mam(MamClosure::Next { mam, instr, old }));
        }
        self.code(mam).instr_mut(instr).next = next;
    }

    fn compiler_find_best_child(
        &mut self,
        mam: MamKind,
        first_child: InstrId,
    ) -> Result<Option<InstrId>, SmtError> {
        let mut num_too_simple = 0;
        let mut best_child = None;
        let mut max_compatibility = 0;
        let mut child = Some(first_child);
        while let Some(current) = child {
            let (weight, is_simple) = self.compiler_get_compatibility_measure(mam, current)?;
            if is_simple {
                num_too_simple += 1;
                if num_too_simple > FIND_BEST_CHILD_THRESHOLD {
                    return Ok(None);
                }
            }
            if weight > max_compatibility {
                best_child = Some(current);
                max_compatibility = weight;
            }
            child = self.code_ref(mam).instr(current).alt;
        }
        Ok(best_child)
    }

    fn compiler_is_bind_compatible(&self, mam: MamKind, instr: InstrId) -> bool {
        let instr = self.code_ref(mam).instr(instr);
        let expr = self.compiler_ref(mam).get_register(instr.reg);
        is_app(&self.m, expr)
            && !self.m.is_ground(expr)
            && self.m.decls[expr as usize] == instr.label
            && self.m.get_num_args(expr) as u32 == instr.num_args
    }

    fn compiler_is_compare_compatible(&self, mam: MamKind, instr: InstrId) -> bool {
        let instr = self.code_ref(mam).instr(instr);
        let compiler = self.compiler_ref(mam);
        let expr = compiler.get_register(instr.reg);
        expr != -1 && expr == compiler.get_register(instr.reg2)
    }

    fn compiler_is_check_compatible(
        &mut self,
        mam: MamKind,
        instr: InstrId,
    ) -> Result<bool, SmtError> {
        let reg = self.code_ref(mam).instr(instr).reg;
        let expr = self.compiler_ref(mam).get_register(reg);
        if !is_app(&self.m, expr) || !self.m.is_ground(expr) {
            return Ok(false);
        }
        let quantifier = self.compiler_ref(mam).quantifier;
        let node = self.get_ground_enode(mam, expr, quantifier)?;
        let enode = self.code_ref(mam).instr(instr).enode;
        Ok(match (enode, node) {
            (Some(enode), Some(node)) => self.root(enode) == self.root(node),
            _ => false,
        })
    }

    /// get_pat_lbl_hash: a ground pattern is a constant, hashed by its enode.
    fn compiler_get_pat_lbl_hash(&mut self, mam: MamKind, reg: u32) -> Result<i32, SmtError> {
        let expr = self.compiler_ref(mam).registers[reg as usize];
        if self.m.is_ground(expr) {
            let quantifier = self.compiler_ref(mam).quantifier;
            let node = self.get_ground_enode(mam, expr, quantifier)?;
            return Ok(match node {
                None => -1,
                Some(node) => self.get_lbl_hash(mam, node),
            });
        }
        Ok(self.get_label_hash(mam, self.m.decls[expr as usize]) as i32)
    }

    fn compiler_is_check_semi_compatible(
        &mut self,
        mam: MamKind,
        instr: InstrId,
    ) -> Result<bool, SmtError> {
        let enode = self.code_ref(mam).instr(instr).enode;
        let reg = self.code_ref(mam).instr(instr).reg;
        if let Some(enode) = enode {
            self.get_lbl_hash(mam, enode);
        }
        let expr = self.compiler_ref(mam).get_register(reg);
        let Some(enode) = enode else {
            return Ok(false);
        };
        Ok(expr != -1
            && self.compiler_ref(mam).get_mark(reg) == NOT_CHECKED
            && self.m.is_ground(expr)
            && self.compiler_get_pat_lbl_hash(mam, reg)? == self.node(enode).lbl_hash)
    }

    fn compiler_is_filter_compatible(
        &mut self,
        mam: MamKind,
        instr: InstrId,
    ) -> Result<bool, SmtError> {
        let instr = self.code_ref(mam).instr(instr);
        let (reg, low, high) = (instr.reg, instr.lbl_low, instr.lbl_high);
        let expr = self.compiler_ref(mam).get_register(reg);
        Ok(is_app(&self.m, expr)
            && !self.m.is_ground(expr)
            && has_hash(low, high, self.compiler_get_pat_lbl_hash(mam, reg)?))
    }

    fn compiler_is_cfilter_compatible(
        &mut self,
        mam: MamKind,
        instr: InstrId,
    ) -> Result<bool, SmtError> {
        let instr = self.code_ref(mam).instr(instr);
        let (reg, low, high) = (instr.reg, instr.lbl_low, instr.lbl_high);
        let expr = self.compiler_ref(mam).get_register(reg);
        Ok(is_ground(&self.m, expr)
            && has_hash(low, high, self.compiler_get_pat_lbl_hash(mam, reg)?))
    }

    fn compiler_is_filter_semi_compatible(&self, mam: MamKind, instr: InstrId) -> bool {
        let reg = self.code_ref(mam).instr(instr).reg;
        let compiler = self.compiler_ref(mam);
        let expr = compiler.get_register(reg);
        compiler.get_mark(reg) == NOT_CHECKED && is_app(&self.m, expr) && !self.m.is_ground(expr)
    }

    /// get_compatibility_measure: how many instructions of the branch at child are compatible
    /// with the patterns in the registers, and whether the branch is too simple to look at.
    fn compiler_get_compatibility_measure(
        &mut self,
        mam: MamKind,
        child: InstrId,
    ) -> Result<(u32, bool), SmtError> {
        self.compiler(mam).to_reset.clear();
        let mut weight = 0;
        let mut num_instructions = 0;
        let mut curr = self.code_ref(mam).instr(child).next;
        while let Some(current) = curr {
            let op = self.code_ref(mam).instr(current).op;
            if op == OP_CHOOSE || op == OP_NOOP {
                break;
            }
            num_instructions += 1;
            match op {
                OP_BIND => {
                    if self.compiler_is_bind_compatible(mam, current) {
                        weight += 4;
                        let instr = self.code_ref(mam).instr(current);
                        let (reg, oreg, num_args) = (instr.reg, instr.oreg, instr.num_args);
                        let expr = self.compiler_ref(mam).registers[reg as usize];
                        for index in 0..num_args {
                            let arg = self.m.get_arg(expr, index as usize);
                            let compiler = self.compiler(mam);
                            compiler.set_register(oreg + index, arg);
                            compiler.to_reset.push(oreg + index);
                        }
                    }
                }
                OP_COMPARE => {
                    if self.compiler_is_compare_compatible(mam, current) {
                        weight += 2;
                    }
                }
                OP_CHECK => {
                    if self.compiler_is_check_compatible(mam, current)? {
                        weight += 2;
                    } else if self.compiler_is_check_semi_compatible(mam, current)? {
                        weight += 1;
                    }
                }
                OP_CFILTER => {
                    if self.compiler_is_cfilter_compatible(mam, current)? {
                        weight += 2;
                    }
                }
                OP_FILTER => {
                    if self.compiler_is_filter_compatible(mam, current)? {
                        weight += 2;
                    } else if self.compiler_is_filter_semi_compatible(mam, current) {
                        weight += 1;
                    }
                }
                _ => {}
            }
            curr = self.code_ref(mam).instr(current).next;
        }
        let is_choose =
            curr.is_some_and(|current| self.code_ref(mam).instr(current).op == OP_CHOOSE);
        let is_simple = !(num_instructions > SIMPLE_SEQ_THRESHOLD || is_choose);
        let compiler = self.compiler(mam);
        for index in 0..compiler.to_reset.len() {
            let reg = compiler.to_reset[index];
            compiler.registers[reg as usize] = -1;
        }
        Ok((weight, is_simple))
    }

    /// compiler::insert: follows the instructions compatible with the new pattern, then branches
    /// off with a CHOOSE where they stop.
    fn compiler_insert_at(
        &mut self,
        mam: MamKind,
        start: InstrId,
        first_index: usize,
    ) -> Result<(), SmtError> {
        let mut head = start;
        loop {
            self.compiler(mam).compatible.clear();
            self.compiler(mam).incompatible.clear();
            let mut curr = self.code_ref(mam).instr(head).next;
            let mut last = head;
            while let Some(current) = curr {
                let op = self.code_ref(mam).instr(current).op;
                if op == OP_CHOOSE || op == OP_NOOP {
                    break;
                }
                let instr = self.code_ref(mam).instr(current);
                let (reg, reg2, oreg, num_args, low, high, enode) = (
                    instr.reg,
                    instr.reg2,
                    instr.oreg,
                    instr.num_args,
                    instr.lbl_low,
                    instr.lbl_high,
                    instr.enode,
                );
                match op {
                    OP_BIND => {
                        if self.compiler_is_bind_compatible(mam, current) {
                            let expr = self.compiler_ref(mam).registers[reg as usize];
                            let compiler = self.compiler(mam);
                            compiler.erase_todo(reg);
                            compiler.set_mark(reg, NOT_CHECKED);
                            compiler.compatible.push(current);
                            for index in 0..num_args {
                                let arg = self.m.get_arg(expr, index as usize);
                                let compiler = self.compiler(mam);
                                compiler.set_register(oreg + index, arg);
                                compiler.todo.push(oreg + index);
                            }
                        } else {
                            self.compiler(mam).incompatible.push(current);
                        }
                    }
                    OP_CHECK => {
                        if self.compiler_is_check_compatible(mam, current)? {
                            let compiler = self.compiler(mam);
                            compiler.erase_todo(reg);
                            compiler.set_mark(reg, NOT_CHECKED);
                            compiler.compatible.push(current);
                        } else if self.compiler_is_check_semi_compatible(mam, current)?
                            && let Some(enode) = enode
                        {
                            let mut filter = mk_filter(OP_CFILTER, reg, 0, 0);
                            let enode_hash = self.get_lbl_hash(mam, enode);
                            set_hash(&mut filter.lbl_low, &mut filter.lbl_high, enode_hash);
                            let pattern_hash = self.compiler_get_pat_lbl_hash(mam, reg)?;
                            set_hash(&mut filter.lbl_low, &mut filter.lbl_high, pattern_hash);
                            let filter = self.code(mam).mk(filter);
                            let compiler = self.compiler(mam);
                            compiler.set_mark(reg, CHECK_SET);
                            compiler.compatible.push(filter);
                            compiler.incompatible.push(current);
                        } else {
                            self.compiler(mam).incompatible.push(current);
                        }
                    }
                    OP_COMPARE => {
                        if self.compiler_is_compare_compatible(mam, current) {
                            let compiler = self.compiler(mam);
                            compiler.erase_todo(reg2);
                            compiler.set_mark(reg2, NOT_CHECKED);
                            let expr = compiler.registers[reg as usize];
                            if self.m.kinds[expr as usize] == KIND_VAR {
                                let var_index = self.m.values[expr as usize] as usize;
                                let compiler = self.compiler(mam);
                                compiler.erase_todo(reg);
                                compiler.set_mark(reg, NOT_CHECKED);
                                if compiler.vars[var_index] == -1 {
                                    compiler.vars[var_index] = reg as i32;
                                }
                            }
                            self.compiler(mam).compatible.push(current);
                        } else {
                            self.compiler(mam).incompatible.push(current);
                        }
                    }
                    OP_CFILTER => {
                        if self.compiler_is_cfilter_compatible(mam, current)? {
                            let compiler = self.compiler(mam);
                            compiler.set_mark(reg, CHECK_SINGLETON);
                            compiler.compatible.push(current);
                        } else {
                            self.compiler(mam).incompatible.push(current);
                        }
                    }
                    OP_FILTER => {
                        if self.compiler_is_filter_compatible(mam, current)? {
                            let is_singleton = low.count_ones() + high.count_ones() == 1;
                            let compiler = self.compiler(mam);
                            compiler.set_mark(
                                reg,
                                if is_singleton {
                                    CHECK_SINGLETON
                                } else {
                                    CHECK_SET
                                },
                            );
                            compiler.compatible.push(current);
                        } else if self.compiler_is_filter_semi_compatible(mam, current) {
                            let hash = self.compiler_get_pat_lbl_hash(mam, reg)?;
                            self.compiler(mam).set_mark(reg, CHECK_SET);
                            if low.count_ones() + high.count_ones() > 1 {
                                // insert_new_lbl_hash.
                                self.push_trail(TrailClosure::Mam(MamClosure::Filter {
                                    mam,
                                    instr: current,
                                    low,
                                    high,
                                }));
                                let filter = self.code(mam).instr_mut(current);
                                set_hash(&mut filter.lbl_low, &mut filter.lbl_high, hash);
                                self.compiler(mam).compatible.push(current);
                            } else {
                                let mut filter = mk_filter(OP_FILTER, reg, low, high);
                                set_hash(&mut filter.lbl_low, &mut filter.lbl_high, hash);
                                let filter = self.code(mam).mk(filter);
                                let compiler = self.compiler(mam);
                                compiler.compatible.push(filter);
                                compiler.incompatible.push(current);
                            }
                        } else {
                            self.compiler(mam).incompatible.push(current);
                        }
                    }
                    _ => self.compiler(mam).incompatible.push(current),
                }
                last = current;
                curr = self.code_ref(mam).instr(current).next;
            }
            if self.compiler_ref(mam).incompatible.is_empty() {
                let Some(current) = curr else {
                    return Ok(());
                };
                let Some(best_child) = self.compiler_find_best_child(mam, current)? else {
                    // head -> ... -> last -> new_child: CHOOSE(first_child) -> linearise.
                    let new_child = self.code(mam).mk(mk_choose(Some(current)));
                    self.compiler(mam).num_choices += 1;
                    self.compiler_set_next(mam, last, Some(new_child));
                    return self.compiler_linearise(mam, new_child, first_index);
                };
                head = best_child;
                continue;
            }
            // head -> compatible -> new_child_head1: CHOOSE(new_child_head2) -> incompatible ->
            // curr, and new_child_head2: NOOP -> linearise.
            let first_child_head = curr;
            let new_child_head2 = self.code(mam).mk(Instruction::new(OP_NOOP));
            let new_child_head1 = self.code(mam).mk(mk_choose(Some(new_child_head2)));
            self.compiler(mam).num_choices += 1;
            let compatible = mem::take(&mut self.compiler(mam).compatible);
            let incompatible = mem::take(&mut self.compiler(mam).incompatible);
            let mut tail = head;
            for instr in &compatible {
                self.compiler_set_next(mam, tail, Some(*instr));
                tail = *instr;
            }
            self.compiler_set_next(mam, tail, Some(new_child_head1));
            tail = new_child_head1;
            for instr in &incompatible {
                if tail == new_child_head1 {
                    self.code(mam).instr_mut(tail).next = Some(*instr);
                } else {
                    self.compiler_set_next(mam, tail, Some(*instr));
                }
                tail = *instr;
            }
            self.compiler(mam).compatible = compatible;
            self.compiler(mam).incompatible = incompatible;
            self.compiler_set_next(mam, tail, first_child_head);
            return self.compiler_linearise(mam, new_child_head2, first_index);
        }
    }

    /// mk_tree: a new code tree for a quantifier, which starts with the pattern at first_index.
    pub fn compiler_mk_tree(
        &mut self,
        mam: MamKind,
        quantifier: Expr,
        patterns: &[Expr],
        first_index: usize,
        is_filtering_candidates: bool,
    ) -> Result<TreeId, SmtError> {
        let pattern = patterns[first_index];
        let num_args = self.m.get_num_args(pattern) as u32;
        let root_label = self.m.decls[pattern as usize];
        let code = self.code(mam);
        let root = code.mk(mk_init(num_args));
        code.trees.push(CodeTree {
            root_label,
            num_args,
            is_filtering_candidates,
            num_regs: num_args + 1,
            num_choices: 0,
            root,
            candidates: Vec::new(),
            candidate_gc_threshold: 10000,
        });
        let tree = (self.code_ref(mam).trees.len() - 1) as TreeId;
        self.compiler_init(mam, tree, quantifier, patterns, first_index)?;
        self.compiler_linearise(mam, root, first_index)?;
        let num_choices = self.compiler_ref(mam).num_choices;
        self.code(mam).tree_mut(tree).num_choices = num_choices;
        Ok(tree)
    }

    /// insert: adds a pattern to a code tree. A temporary tree records no trail.
    pub fn compiler_insert(
        &mut self,
        mam: MamKind,
        tree: TreeId,
        quantifier: Expr,
        patterns: &[Expr],
        first_index: usize,
        is_tmp_tree: bool,
    ) -> Result<(), SmtError> {
        if self.code_ref(mam).tree(tree).num_args
            != self.m.get_num_args(patterns[first_index]) as u32
        {
            return Ok(());
        }
        self.compiler(mam).is_tmp_tree = is_tmp_tree;
        if !is_tmp_tree {
            let num_regs = self.code_ref(mam).tree(tree).num_regs;
            self.push_trail(TrailClosure::Mam(MamClosure::NumRegs {
                mam,
                tree,
                num_regs,
            }));
        }
        self.compiler_init(mam, tree, quantifier, patterns, first_index)?;
        let tree_num_choices = self.code_ref(mam).tree(tree).num_choices;
        self.compiler(mam).num_choices = tree_num_choices;
        let root = self.code_ref(mam).tree(tree).root;
        self.compiler_insert_at(mam, root, first_index)?;
        let num_choices = self.compiler_ref(mam).num_choices;
        if num_choices <= tree_num_choices {
            return Ok(());
        }
        if !is_tmp_tree {
            self.push_trail(TrailClosure::Mam(MamClosure::NumChoices {
                mam,
                tree,
                num_choices: tree_num_choices,
            }));
        }
        self.code(mam).tree_mut(tree).num_choices = num_choices;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    //! The code trees the compiler makes and grows, against those that
    //! `scripts/smt-ematching-reference.ts` printed for the TypeScript compiler on the same
    //! patterns, made in the same order.

    use std::collections::HashMap;
    use std::fmt::Write;

    use prove_decide::Limits;

    use super::{CodeTrees, InstrId, TreeId};
    use crate::core::ast::{AstManager, Expr, QuantifierData, SORT_BOOL, SmtSymbol, Sort};
    use crate::core::context::{Context, SmtParams};
    use crate::core::e_matching::MamKind;
    use crate::util::rlimit::ResourceLimit;

    const OP_NAMES: [&str; 14] = [
        "INIT",
        "BIND",
        "YIELD",
        "COMPARE",
        "CHECK",
        "FILTER",
        "CFILTER",
        "PFILTER",
        "CHOOSE",
        "NOOP",
        "CONTINUE",
        "GET_ENODE",
        "GET_CGR",
        "IS_CGR",
    ];

    const EXPECTED: &str = "tree regs=4 choices=1
  0 INIT reg=0 reg2=0 oreg=0 n=2 label=-1 enode=-1 lbl=0,0 q=-1 regs=[] joints=[] next=1 alt=-
  1 FILTER reg=1 reg2=0 oreg=0 n=0 label=-1 enode=-1 lbl=4194304,0 q=-1 regs=[] joints=[] next=2 alt=-
  2 BIND reg=1 reg2=0 oreg=3 n=1 label=31 enode=-1 lbl=0,0 q=-1 regs=[] joints=[] next=3 alt=-
  3 YIELD reg=0 reg2=0 oreg=0 n=2 label=-1 enode=-1 lbl=0,0 q=18 regs=[2,3] joints=[] next=- alt=-
tree regs=4 choices=2
  0 INIT reg=0 reg2=0 oreg=0 n=2 label=-1 enode=-1 lbl=0,0 q=-1 regs=[] joints=[] next=1 alt=-
  1 FILTER reg=1 reg2=0 oreg=0 n=0 label=-1 enode=-1 lbl=4194304,0 q=-1 regs=[] joints=[] next=2 alt=-
  2 BIND reg=1 reg2=0 oreg=3 n=1 label=31 enode=-1 lbl=0,0 q=-1 regs=[] joints=[] next=3 alt=-
  3 CHOOSE reg=0 reg2=0 oreg=0 n=0 label=-1 enode=-1 lbl=0,0 q=-1 regs=[] joints=[] next=4 alt=5
  4 YIELD reg=0 reg2=0 oreg=0 n=2 label=-1 enode=-1 lbl=0,0 q=18 regs=[2,3] joints=[] next=- alt=-
  5 NOOP reg=0 reg2=0 oreg=0 n=0 label=-1 enode=-1 lbl=0,0 q=-1 regs=[] joints=[] next=- alt=-
tree regs=5 choices=4
  0 INIT reg=0 reg2=0 oreg=0 n=2 label=-1 enode=-1 lbl=0,0 q=-1 regs=[] joints=[] next=1 alt=-
  1 FILTER reg=1 reg2=0 oreg=0 n=0 label=-1 enode=-1 lbl=4194304,8 q=-1 regs=[] joints=[] next=2 alt=-
  2 CHOOSE reg=0 reg2=0 oreg=0 n=0 label=-1 enode=-1 lbl=0,0 q=-1 regs=[] joints=[] next=3 alt=8
  3 FILTER reg=1 reg2=0 oreg=0 n=0 label=-1 enode=-1 lbl=4194304,0 q=-1 regs=[] joints=[] next=4 alt=-
  4 BIND reg=1 reg2=0 oreg=3 n=1 label=31 enode=-1 lbl=0,0 q=-1 regs=[] joints=[] next=5 alt=-
  5 CHOOSE reg=0 reg2=0 oreg=0 n=0 label=-1 enode=-1 lbl=0,0 q=-1 regs=[] joints=[] next=6 alt=7
  6 YIELD reg=0 reg2=0 oreg=0 n=2 label=-1 enode=-1 lbl=0,0 q=18 regs=[2,3] joints=[] next=- alt=-
  7 NOOP reg=0 reg2=0 oreg=0 n=0 label=-1 enode=-1 lbl=0,0 q=-1 regs=[] joints=[] next=- alt=-
  8 NOOP reg=0 reg2=0 oreg=0 n=0 label=-1 enode=-1 lbl=0,0 q=-1 regs=[] joints=[] next=- alt=-
tree regs=7 choices=7
  0 INIT reg=0 reg2=0 oreg=0 n=2 label=-1 enode=-1 lbl=0,0 q=-1 regs=[] joints=[] next=1 alt=-
  1 CHOOSE reg=0 reg2=0 oreg=0 n=0 label=-1 enode=-1 lbl=0,0 q=-1 regs=[] joints=[] next=2 alt=10
  2 FILTER reg=1 reg2=0 oreg=0 n=0 label=-1 enode=-1 lbl=4194304,8 q=-1 regs=[] joints=[] next=3 alt=-
  3 CHOOSE reg=0 reg2=0 oreg=0 n=0 label=-1 enode=-1 lbl=0,0 q=-1 regs=[] joints=[] next=4 alt=9
  4 FILTER reg=1 reg2=0 oreg=0 n=0 label=-1 enode=-1 lbl=4194304,0 q=-1 regs=[] joints=[] next=5 alt=-
  5 BIND reg=1 reg2=0 oreg=3 n=1 label=31 enode=-1 lbl=0,0 q=-1 regs=[] joints=[] next=6 alt=-
  6 CHOOSE reg=0 reg2=0 oreg=0 n=0 label=-1 enode=-1 lbl=0,0 q=-1 regs=[] joints=[] next=7 alt=8
  7 YIELD reg=0 reg2=0 oreg=0 n=2 label=-1 enode=-1 lbl=0,0 q=18 regs=[2,3] joints=[] next=- alt=-
  8 NOOP reg=0 reg2=0 oreg=0 n=0 label=-1 enode=-1 lbl=0,0 q=-1 regs=[] joints=[] next=- alt=-
  9 NOOP reg=0 reg2=0 oreg=0 n=0 label=-1 enode=-1 lbl=0,0 q=-1 regs=[] joints=[] next=- alt=-
  10 NOOP reg=0 reg2=0 oreg=0 n=0 label=-1 enode=-1 lbl=0,0 q=-1 regs=[] joints=[] next=11 alt=-
  11 FILTER reg=2 reg2=0 oreg=0 n=0 label=-1 enode=-1 lbl=4194304,0 q=-1 regs=[] joints=[] next=12 alt=-
  12 BIND reg=2 reg2=0 oreg=5 n=1 label=31 enode=-1 lbl=0,0 q=-1 regs=[] joints=[] next=13 alt=-
  13 FILTER reg=5 reg2=0 oreg=0 n=0 label=-1 enode=-1 lbl=0,8 q=-1 regs=[] joints=[] next=14 alt=-
  14 BIND reg=5 reg2=0 oreg=6 n=1 label=32 enode=-1 lbl=0,0 q=-1 regs=[] joints=[] next=15 alt=-
  15 YIELD reg=0 reg2=0 oreg=0 n=2 label=-1 enode=-1 lbl=0,0 q=27 regs=[1,6] joints=[] next=- alt=-
tree regs=5 choices=0
  0 INIT reg=0 reg2=0 oreg=0 n=2 label=-1 enode=-1 lbl=0,0 q=-1 regs=[] joints=[] next=1 alt=-
  1 GET_CGR reg=0 reg2=0 oreg=3 n=2 label=33 enode=-1 lbl=4096,0 q=-1 regs=[2,1] joints=[] next=2 alt=-
  2 GET_CGR reg=0 reg2=0 oreg=4 n=1 label=31 enode=-1 lbl=4194304,0 q=-1 regs=[1] joints=[] next=3 alt=-
  3 YIELD reg=0 reg2=0 oreg=0 n=2 label=-1 enode=-1 lbl=0,0 q=33 regs=[2,1] joints=[] next=- alt=-
tree regs=5 choices=1
  0 INIT reg=0 reg2=0 oreg=0 n=1 label=-1 enode=-1 lbl=0,0 q=-1 regs=[] joints=[] next=1 alt=-
  1 CONTINUE reg=0 reg2=0 oreg=2 n=2 label=33 enode=-1 lbl=4096,0 q=-1 regs=[] joints=[2/-1/1/-1/0,0/-1/0/-1/0] next=2 alt=-
  2 COMPARE reg=1 reg2=2 oreg=0 n=0 label=-1 enode=-1 lbl=0,0 q=-1 regs=[] joints=[] next=3 alt=-
  3 GET_CGR reg=0 reg2=0 oreg=4 n=2 label=33 enode=-1 lbl=4096,0 q=-1 regs=[3,1] joints=[] next=4 alt=-
  4 YIELD reg=0 reg2=0 oreg=0 n=2 label=-1 enode=-1 lbl=0,0 q=33 regs=[3,1] joints=[] next=- alt=-
";

    /// Each instruction, numbered in the order a walk of next before alt reaches it.
    fn dump_tree(context: &Context, code: &CodeTrees, tree: TreeId, out: &mut String) {
        let tree = code.tree(tree);
        let mut numbers: HashMap<InstrId, usize> = HashMap::new();
        let mut order = Vec::new();
        let mut stack = vec![tree.root];
        while let Some(instr) = stack.pop() {
            if numbers.contains_key(&instr) {
                continue;
            }
            numbers.insert(instr, order.len());
            order.push(instr);
            if let Some(alt) = code.instr(instr).alt {
                stack.push(alt);
            }
            if let Some(next) = code.instr(instr).next {
                stack.push(next);
            }
        }
        let number = |instr: Option<InstrId>| {
            instr.map_or("-".to_string(), |instr| numbers[&instr].to_string())
        };
        let owner = |node: Option<u32>| node.map_or(-1, |node| context.node(node).owner);
        writeln!(
            out,
            "tree regs={} choices={}",
            tree.num_regs, tree.num_choices
        )
        .unwrap();
        for id in order {
            let instr = code.instr(id);
            let joints: Vec<String> = instr
                .joints
                .iter()
                .map(|joint| {
                    format!(
                        "{}/{}/{}/{}/{}",
                        joint.kind,
                        owner(joint.enode),
                        joint.reg,
                        joint.decl,
                        joint.arg_pos
                    )
                })
                .collect();
            let regs: Vec<String> = instr.regs.iter().map(u32::to_string).collect();
            writeln!(
                out,
                "  {} {} reg={} reg2={} oreg={} n={} label={} enode={} lbl={},{} q={} regs=[{}] joints=[{}] next={} alt={}",
                number(Some(id)),
                OP_NAMES[instr.op as usize],
                instr.reg,
                instr.reg2,
                instr.oreg,
                instr.num_args,
                instr.label,
                owner(instr.enode),
                instr.lbl_low,
                instr.lbl_high,
                instr.quantifier,
                regs.join(","),
                joints.join(","),
                number(instr.next),
                number(instr.alt),
            )
            .unwrap();
        }
    }

    fn forall(context: &mut Context, sort: Sort, body: Expr, terms: &[Expr]) -> Expr {
        let pattern = context.m.mk_pattern(terms).unwrap();
        context
            .m
            .mk_quantifier(QuantifierData {
                is_forall: true,
                sorts: vec![sort; 2],
                names: vec![SmtSymbol::Name("x0".into()), SmtSymbol::Name("x1".into())],
                body,
                patterns: vec![pattern],
                weight: 0,
                qid: String::new(),
            })
            .unwrap()
    }

    #[test]
    fn compiles_and_grows_code_trees_as_the_typescript() {
        let limits = Limits::new(f64::INFINITY, None, None);
        let m = AstManager::new(ResourceLimit::new(&limits));
        let mut context = Context::new(
            m,
            SmtParams {
                is_mbqi: false,
                relevancy_level: 2,
            },
        )
        .unwrap();
        context.setup_context().unwrap();
        let u = context.m.mk_sort("U");
        let func = |context: &mut Context, name: &str, domain: &[Sort], range: Sort| {
            context
                .m
                .mk_func_decl(SmtSymbol::Name(name.into()), domain, range, false)
        };
        let f = func(&mut context, "f", &[u, u], u);
        let g = func(&mut context, "g", &[u], u);
        let h = func(&mut context, "h", &[u], u);
        let r = func(&mut context, "r", &[u, u], SORT_BOOL);
        let x = context.m.mk_var(1, u);
        let y = context.m.mk_var(0, u);
        let a_decl = func(&mut context, "a", &[], u);
        let m = &mut context.m;
        let a = m.mk_app(a_decl, &[], u).unwrap();
        let gx = m.mk_app(g, &[x], u).unwrap();
        let p1 = m.mk_app(f, &[gx, y], u).unwrap();
        let p2 = m.mk_app(f, &[gx, x], u).unwrap();
        let hx = m.mk_app(h, &[x], u).unwrap();
        let p3 = m.mk_app(f, &[hx, a], u).unwrap();
        let hx = m.mk_app(h, &[x], u).unwrap();
        let ghx = m.mk_app(g, &[hx], u).unwrap();
        let p4 = m.mk_app(f, &[y, ghx], u).unwrap();
        let mut quantifiers = Vec::new();
        for pattern in [p1, p2, p3, p4] {
            let body = context.m.mk_eq(pattern, y).unwrap();
            quantifiers.push(forall(&mut context, u, body, &[pattern]));
        }
        let mam = MamKind::Eager;
        let mut out = String::new();
        let tree = context
            .compiler_mk_tree(mam, quantifiers[0], &[p1], 0, false)
            .unwrap();
        dump_tree(&context, &context.qmanager.mam(mam).code, tree, &mut out);
        for (quantifier, pattern) in quantifiers[1..].iter().zip([p2, p3, p4]) {
            context
                .compiler_insert(mam, tree, *quantifier, &[pattern], 0, false)
                .unwrap();
            dump_tree(&context, &context.qmanager.mam(mam).code, tree, &mut out);
        }
        // A multi-pattern: r(x, y), r(y, x) and g(x).
        let m = &mut context.m;
        let rxy = m.mk_app(r, &[x, y], SORT_BOOL).unwrap();
        let ryx = m.mk_app(r, &[y, x], SORT_BOOL).unwrap();
        let not_rxy = m.mk_not(rxy).unwrap();
        let body = m.mk_or(&[not_rxy, ryx]).unwrap();
        let q5 = forall(&mut context, u, body, &[rxy, ryx, gx]);
        for (first_index, is_filtering) in [(0, false), (2, true)] {
            let tree = context
                .compiler_mk_tree(mam, q5, &[rxy, ryx, gx], first_index, is_filtering)
                .unwrap();
            dump_tree(&context, &context.qmanager.mam(mam).code, tree, &mut out);
        }
        assert_eq!(out, EXPECTED);
    }
}
