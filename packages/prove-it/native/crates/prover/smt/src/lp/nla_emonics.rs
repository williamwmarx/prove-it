// Ported from Z3 (src/math/lp/monic.h, src/math/lp/emonics.h, src/math/lp/emonics.cpp), MIT
// license, see z3-license.txt. The monomials v := v1 * ... * vn of nla, canonized over the
// variable equivalences, with the cyclic use lists of their variables and the congruence classes
// of monomials equal up to sign.
//
// Rust API notes:
// - A monic is handed out as its index in `Emonics::monics` (a `usize`, "monic index"), never as a
//   reference that outlives the call: `get_use_list`, `get_products_of`, `get_sign_equiv_monics`
//   and `find_canonical` give monic indices, the methods that take a TS `Monic` to change it
//   (`set_propagated`, `set_bound_propagated`, `get_products_of_monic`, `get_sign_equiv_monics`)
//   take a monic index, and `get(lp_var)`/`monics[index]` read one. A monic index stays valid
//   until the scope that added the monic is popped, as the TS `Monic` object does.
// - TS `Emonics` holds its `VarEqs`; here nla owns both, and the methods that use the variable
//   equivalences take them as an argument. `Emonics` is the merge handler of `VarEqs`: pass
//   `&mut emons` to `VarEqs::merge_plus`/`merge_minus`/`merge`.
// - The TS generators are cursors whose `next` takes the `Emonics`, so that a caller can change
//   nla between steps: `let mut list = emons.get_use_list(column, &var_eqs); while let Some(index)
//   = list.next(&emons) { … }`. As in TS, each step reads the cells or the class cycle when it is
//   taken. The setup (the root lookup, reserving the use lists, a new visited stamp) runs when the
//   cursor is made, where TS runs it at the first step; every TS caller iterates at once.
// - Other nla files push undo closures on `emons.trail`; here they push a `CoreUndo` with
//   `push_core_undo`, and `pop` returns those it pops, in LIFO order, for nla to apply.
use std::collections::HashMap;

use crate::lp::nla_var_eqs::{
    VarEqs, find_in, get_signed_var_var, is_signed_var_negated, mk_signed_var, negate_signed_var,
};
use crate::lp::union_find::{TrailStack, UnionFind, UnionFindHandler, UnionFindUndo};

// The var2index entry of a variable that is not a monic's (TS -1).
const NULL_INDEX: usize = usize::MAX;

#[derive(Clone, Debug)]
pub struct Monic {
    pub variable: usize,
    pub vars: Vec<usize>,
    // The roots of the variables, sorted, and the parity of their signs.
    pub rvars: Vec<usize>,
    pub rsign: bool,
    pub visited: u64,
    pub is_propagated: bool,
    pub is_bound_propagated: bool,
}

impl Monic {
    pub fn new(variable: usize, vars: &[usize]) -> Monic {
        let mut sorted = vars.to_vec();
        sorted.sort();
        Monic {
            variable,
            vars: sorted,
            rvars: Vec::new(),
            rsign: false,
            visited: 0,
            is_propagated: false,
            is_bound_propagated: false,
        }
    }

    pub fn size(&self) -> usize {
        self.vars.len()
    }

    pub fn contains_var(&self, lp_var: usize) -> bool {
        self.vars.contains(&lp_var)
    }
}

// A cell of a cyclic use list: the index of a monic, and the next cell (an index in `cells`).
struct Cell {
    index: usize,
    next: usize,
}

#[derive(Clone, Copy)]
struct HeadTail {
    head: Option<usize>,
    tail: Option<usize>,
}

// The undos of nla's other parts that TS pushes as closures on `emons.trail` (nla-core.ts
// setUseNraModel, nla-divisions.ts pushDivision). They touch nla's state, not the monics, so nla
// applying them after `Emonics::pop` returns, in the order it returns them, is equivalent to the
// TS applying them interleaved with the monics' undos.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum CoreUndo {
    // isUsingNraModel = !isUsing, carrying the isUsing that setUseNraModel was called with.
    SetUseNraModel(bool),
    // divisions.pop() of Divisions' idivisions, boundedDivisions and divisibility.
    PopIdivision,
    PopBoundedDivision,
    PopDivisibility,
}

// What the closures on the trail captured.
pub enum EmonicsUndo {
    UnionFind(UnionFindUndo),
    PopMonic,
    SetPropagated(usize),
    SetBoundPropagated(usize),
    Core(CoreUndo),
}

impl From<UnionFindUndo> for EmonicsUndo {
    fn from(undo: UnionFindUndo) -> EmonicsUndo {
        EmonicsUndo::UnionFind(undo)
    }
}

pub struct Emonics {
    pub trail: TrailStack<EmonicsUndo>,
    union_find: UnionFind,
    pub monics: Vec<Monic>,
    var2index: Vec<usize>,
    visited_stamp: u64,
    use_lists: Vec<HeadTail>,
    // The cells of the use lists. TS allocates a cell per insertion and drops none; nor does this.
    cells: Vec<Cell>,
    // The congruence table: the monics of each rooted variable list, the first its representative.
    cg_table: HashMap<Vec<usize>, Vec<usize>>,
}

impl Default for Emonics {
    fn default() -> Emonics {
        Emonics::new()
    }
}

// The handlers of var_eqs' union-find, over signed variables.
impl UnionFindHandler for Emonics {
    fn after_merge_eh(
        &mut self,
        union_find: &UnionFind,
        r2: usize,
        r1: usize,
        _v2: usize,
        _v1: usize,
    ) {
        if get_signed_var_var(r1) != get_signed_var_var(r2)
            && find_in(union_find, negate_signed_var(r1))
                != find_in(union_find, negate_signed_var(r2))
        {
            return;
        }
        self.reserve_use_lists(get_signed_var_var(r2).max(get_signed_var_var(r1)) + 1);
        self.rehash_cg(get_signed_var_var(r1), union_find);
        self.merge_cells(get_signed_var_var(r2), get_signed_var_var(r1));
    }

    fn unmerge_eh(&mut self, union_find: &UnionFind, r2: usize, r1: usize) {
        if get_signed_var_var(r1) != get_signed_var_var(r2)
            && find_in(union_find, negate_signed_var(r1))
                == find_in(union_find, negate_signed_var(r2))
        {
            return;
        }
        self.unmerge_cells(get_signed_var_var(r2), get_signed_var_var(r1));
        self.rehash_cg(get_signed_var_var(r1), union_find);
    }
}

impl Emonics {
    pub fn new() -> Emonics {
        Emonics {
            trail: TrailStack::new(),
            union_find: UnionFind::new(),
            monics: Vec::new(),
            var2index: Vec::new(),
            visited_stamp: 0,
            use_lists: Vec::new(),
            cells: Vec::new(),
            cg_table: HashMap::new(),
        }
    }

    pub fn num_monics(&self) -> usize {
        self.monics.len()
    }

    pub fn get(&self, lp_var: usize) -> &Monic {
        &self.monics[self.get_index(lp_var)]
    }

    // The monic index of a monic variable, what TS `get` returns as an object.
    pub fn get_index(&self, lp_var: usize) -> usize {
        self.var2index[lp_var]
    }

    pub fn is_monic_var(&self, lp_var: usize) -> bool {
        self.var2index
            .get(lp_var)
            .is_some_and(|index| *index != NULL_INDEX)
    }

    pub fn push(&mut self, var_eqs: &mut VarEqs) {
        self.trail.push_scope();
        var_eqs.push();
    }

    // Returns the popped undos of nla's other parts, in LIFO order, for nla to apply.
    pub fn pop(&mut self, count: usize, var_eqs: &mut VarEqs) -> Vec<CoreUndo> {
        let mut core_undos = Vec::new();
        for _ in 0..count {
            var_eqs.pop(1, self);
            let size = self.trail.pop_scope(1);
            while let Some(undo) = self.trail.pop_above(size) {
                match undo {
                    EmonicsUndo::UnionFind(undo) => self.union_find.undo(undo, &mut ()),
                    EmonicsUndo::PopMonic => self.pop_monic(var_eqs),
                    EmonicsUndo::SetPropagated(index) => self.monics[index].is_propagated = false,
                    EmonicsUndo::SetBoundPropagated(index) => {
                        self.monics[index].is_bound_propagated = false;
                    }
                    EmonicsUndo::Core(undo) => core_undos.push(undo),
                }
            }
        }
        core_undos
    }

    pub fn push_core_undo(&mut self, undo: CoreUndo) {
        self.trail.push(EmonicsUndo::Core(undo));
    }

    pub fn add(&mut self, lp_var: usize, vars: &[usize], var_eqs: &mut VarEqs) {
        var_eqs.push();
        let index = self.monics.len();
        self.monics.push(Monic::new(lp_var, vars));
        self.do_canonize(index, var_eqs.union_find());
        self.trail.push(EmonicsUndo::PopMonic);
        let mut last_var = None;
        for rvar_index in 0..self.monics[index].rvars.len() {
            let rvar = self.monics[index].rvars[rvar_index];
            if Some(rvar) == last_var {
                continue;
            }
            self.reserve_use_lists(rvar + 1);
            self.insert_cell(rvar, index);
            last_var = Some(rvar);
        }
        while self.var2index.len() < lp_var {
            self.var2index.push(NULL_INDEX);
        }
        if lp_var == self.var2index.len() {
            self.var2index.push(index);
        } else {
            self.var2index[lp_var] = index;
        }
        self.insert_cg_mon(index, var_eqs.union_find());
        var_eqs.push();
    }

    fn pop_monic(&mut self, var_eqs: &mut VarEqs) {
        var_eqs.pop(1, self);
        let index = self.monics.len() - 1;
        self.remove_cg_mon(index);
        let variable = self.monics[index].variable;
        self.var2index[variable] = NULL_INDEX;
        self.do_canonize(index, var_eqs.union_find());
        let mut last_var = None;
        for rvar_index in 0..self.monics[index].rvars.len() {
            let rvar = self.monics[index].rvars[rvar_index];
            if Some(rvar) == last_var {
                continue;
            }
            self.remove_cell(rvar);
            last_var = Some(rvar);
        }
        var_eqs.pop(1, self);
        self.monics.pop();
    }

    pub fn set_propagated(&mut self, monic: usize) {
        let target = self.get_index(self.monics[monic].variable);
        self.monics[target].is_propagated = true;
        self.trail.push(EmonicsUndo::SetPropagated(target));
    }

    pub fn set_bound_propagated(&mut self, monic: usize) {
        let target = self.get_index(self.monics[monic].variable);
        self.monics[target].is_bound_propagated = true;
        self.trail.push(EmonicsUndo::SetBoundPropagated(target));
    }

    fn reserve_use_lists(&mut self, size: usize) {
        while self.use_lists.len() < size {
            self.use_lists.push(HeadTail {
                head: None,
                tail: None,
            });
        }
    }

    fn inc_visited(&mut self) {
        self.visited_stamp += 1;
    }

    fn set_visited(&mut self, monic: usize) {
        let target = self.get_index(self.monics[monic].variable);
        self.monics[target].visited = self.visited_stamp;
    }

    fn is_visited(&self, monic: usize) -> bool {
        self.get(self.monics[monic].variable).visited == self.visited_stamp
    }

    fn remove_cell(&mut self, list: usize) {
        let (Some(head), Some(tail)) = (self.use_lists[list].head, self.use_lists[list].tail)
        else {
            return;
        };
        let old_head = self.cells[head].next;
        if old_head == head {
            self.use_lists[list].head = None;
            self.use_lists[list].tail = None;
            return;
        }
        self.use_lists[list].head = Some(old_head);
        self.cells[tail].next = old_head;
    }

    fn insert_cell(&mut self, list: usize, index: usize) {
        let cell = self.cells.len();
        self.cells.push(Cell { index, next: cell });
        if let Some(head) = self.use_lists[list].head {
            self.cells[cell].next = head;
        }
        self.use_lists[list].head = Some(cell);
        let tail = *self.use_lists[list].tail.get_or_insert(cell);
        self.cells[tail].next = cell;
    }

    fn merge_cells(&mut self, root: usize, other: usize) {
        if root == other {
            return;
        }
        let other_list = self.use_lists[other];
        if self.use_lists[root].head.is_none() {
            self.use_lists[root] = other_list;
            return;
        }
        let (Some(other_head), Some(other_tail), Some(root_tail)) =
            (other_list.head, other_list.tail, self.use_lists[root].tail)
        else {
            return;
        };
        self.cells[root_tail].next = other_head;
        self.cells[other_tail].next = self.use_lists[root]
            .head
            .expect("a use list with a tail has a head");
        self.use_lists[root].head = Some(other_head);
    }

    fn unmerge_cells(&mut self, root: usize, other: usize) {
        if root == other {
            return;
        }
        let other_list = self.use_lists[other];
        let (Some(other_head), Some(other_tail)) = (other_list.head, other_list.tail) else {
            return;
        };
        if self.use_lists[root].tail == Some(other_tail) {
            self.use_lists[root].head = None;
            self.use_lists[root].tail = None;
            return;
        }
        let Some(root_tail) = self.use_lists[root].tail else {
            return;
        };
        let root_head = self.cells[other_tail].next;
        self.use_lists[root].head = Some(root_head);
        self.cells[root_tail].next = root_head;
        self.cells[other_tail].next = other_head;
    }

    fn get_head(&mut self, lp_var: usize, var_eqs: &VarEqs) -> Option<usize> {
        let root = get_signed_var_var(var_eqs.find_var(lp_var));
        self.reserve_use_lists(root + 1);
        self.use_lists[root].head
    }

    // The monics in the use list of a variable's root, around the cycle from its head.
    pub fn get_use_list(&mut self, lp_var: usize, var_eqs: &VarEqs) -> UseList {
        UseList {
            head: self.get_head(lp_var, var_eqs),
            cell: None,
        }
    }

    pub fn find_canonical(&self, vars: &[usize]) -> Option<usize> {
        let mut key = vars.to_vec();
        key.sort();
        self.cg_table
            .get(&key)
            .and_then(|table| table.first())
            .map(|variable| self.get_index(*variable))
    }

    pub fn is_canonical_monic(&self, lp_var: usize) -> bool {
        // A TS var2index hole (undefined) reads as canonical and -1 as not, by the way JS compares
        // them.
        match self.var2index.get(lp_var) {
            None => true,
            Some(&NULL_INDEX) => false,
            Some(&index) => {
                index >= self.union_find.num_vars() || self.union_find.find(index) == index
            }
        }
    }

    fn remove_cg(&mut self, lp_var: usize) {
        let Some(first) = self.use_lists[lp_var].head else {
            return;
        };
        self.inc_visited();
        let mut cell = first;
        loop {
            let monic = self.cells[cell].index;
            cell = self.cells[cell].next;
            if !self.is_visited(monic) {
                self.set_visited(monic);
                self.remove_cg_mon(monic);
            }
            if cell == first {
                return;
            }
        }
    }

    fn remove_cg_mon(&mut self, monic: usize) {
        let variable = self.monics[monic].variable;
        let Some(table) = self.cg_table.get_mut(&self.monics[monic].rvars) else {
            return;
        };
        if table.len() == 1 {
            self.cg_table.remove(&self.monics[monic].rvars);
            return;
        }
        // HACK: TS splices at indexOf, which removes the last entry when the variable is absent.
        let position = table
            .iter()
            .position(|entry| *entry == variable)
            .unwrap_or(table.len() - 1);
        table.remove(position);
    }

    fn insert_cg(&mut self, lp_var: usize, var_eqs: &UnionFind) {
        let Some(first) = self.use_lists[lp_var].head else {
            return;
        };
        self.inc_visited();
        let mut cell = first;
        loop {
            let monic = self.cells[cell].index;
            cell = self.cells[cell].next;
            if !self.is_visited(monic) {
                self.set_visited(monic);
                self.insert_cg_mon(monic, var_eqs);
            }
            if cell == first {
                return;
            }
        }
    }

    fn insert_cg_mon(&mut self, monic: usize, var_eqs: &UnionFind) {
        self.do_canonize(monic, var_eqs);
        let variable = self.monics[monic].variable;
        let Some(table) = self.cg_table.get_mut(&self.monics[monic].rvars) else {
            self.cg_table
                .insert(self.monics[monic].rvars.clone(), vec![variable]);
            return;
        };
        if table.contains(&variable) {
            return;
        }
        let representative = table[0];
        table.push(variable);
        let monic_index = self.var2index[variable];
        let representative_index = self.var2index[representative];
        let max_index = monic_index.max(representative_index);
        while self.union_find.num_vars() <= max_index {
            self.union_find.mk_var(&mut self.trail);
        }
        self.union_find
            .merge(&mut self.trail, &mut (), monic_index, representative_index);
    }

    fn rehash_cg(&mut self, lp_var: usize, var_eqs: &UnionFind) {
        self.remove_cg(lp_var);
        self.insert_cg(lp_var, var_eqs);
    }

    fn do_canonize(&mut self, monic: usize, var_eqs: &UnionFind) {
        let target = &mut self.monics[monic];
        target.rsign = false;
        target.rvars = Vec::new();
        for lp_var in &target.vars {
            let root = find_in(var_eqs, mk_signed_var(*lp_var, false));
            target.rsign = target.rsign != is_signed_var_negated(root);
            target.rvars.push(get_signed_var_var(root));
        }
        target.rvars.sort();
    }

    pub fn ensure_canonized(&mut self, var_eqs: &VarEqs) {
        for index in 0..self.monics.len() {
            self.do_canonize(index, var_eqs.union_find());
        }
    }

    // canonize_divides: whether the rooted variables of the first are a sub-multiset of the second's.
    pub fn canonize_divides(&self, divisor: &Monic, product: &Monic) -> bool {
        if divisor.size() > product.size() {
            return false;
        }
        let mut divisor_index = 0;
        let mut product_index = 0;
        loop {
            if divisor_index == divisor.size() {
                return true;
            }
            if product_index == product.size() {
                return false;
            }
            let divisor_var = divisor.rvars[divisor_index];
            let product_var = product.rvars[product_index];
            if divisor_var == product_var {
                divisor_index += 1;
                product_index += 1;
            } else if divisor_var < product_var {
                return false;
            } else {
                product_index += 1;
            }
        }
    }

    // get_products_of: every monic using the variable, each once.
    pub fn get_products_of(&mut self, lp_var: usize, var_eqs: &VarEqs) -> ProductsOf {
        self.inc_visited();
        ProductsOf {
            factor: None,
            use_list: self.get_use_list(lp_var, var_eqs),
        }
    }

    // get_products_of: the monics, other than the given one, that it divides, each once.
    pub fn get_products_of_monic(&mut self, factor: usize, var_eqs: &VarEqs) -> ProductsOf {
        self.inc_visited();
        ProductsOf {
            factor: Some(factor),
            use_list: self.get_use_list(self.monics[factor].vars[0], var_eqs),
        }
    }

    // enum_sign_equiv_monics: the monics equal to this one up to sign, around its class's cycle.
    pub fn get_sign_equiv_monics(&self, monic: usize) -> SignEquivMonics {
        SignEquivMonics {
            start: self.var2index[self.monics[monic].variable],
            index: None,
        }
    }
}

// The cursor of `Emonics::get_use_list`: monic indices.
pub struct UseList {
    head: Option<usize>,
    // The cell last given, none before the first step.
    cell: Option<usize>,
}

impl UseList {
    pub fn next(&mut self, emons: &Emonics) -> Option<usize> {
        let head = self.head?;
        let cell = match self.cell {
            None => head,
            Some(cell) => emons.cells[cell].next,
        };
        if self.cell.is_some() && cell == head {
            self.head = None;
            return None;
        }
        self.cell = Some(cell);
        Some(emons.cells[cell].index)
    }
}

// The cursor of `Emonics::get_products_of` and `get_products_of_monic`: monic indices.
pub struct ProductsOf {
    factor: Option<usize>,
    use_list: UseList,
}

impl ProductsOf {
    pub fn next(&mut self, emons: &mut Emonics) -> Option<usize> {
        loop {
            let monic = self.use_list.next(emons)?;
            if let Some(factor) = self.factor
                && (emons.monics[factor].variable == emons.monics[monic].variable
                    || !emons.canonize_divides(&emons.monics[factor], &emons.monics[monic]))
            {
                continue;
            }
            if emons.is_visited(monic) {
                continue;
            }
            emons.set_visited(monic);
            return Some(monic);
        }
    }
}

// The cursor of `Emonics::get_sign_equiv_monics`: monic indices.
pub struct SignEquivMonics {
    start: usize,
    // The index last given, none before the first step.
    index: Option<usize>,
}

impl SignEquivMonics {
    pub fn next(&mut self, emons: &Emonics) -> Option<usize> {
        let Some(index) = self.index else {
            self.index = Some(self.start);
            return Some(self.start);
        };
        if index >= emons.union_find.num_vars() {
            return None;
        }
        let next = emons.union_find.next(index);
        if next == self.start {
            return None;
        }
        self.index = Some(next);
        Some(next)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lp::dependency::mk_leaf;
    use crate::lp::explanation::Explanation;
    use crate::lp::nla_var_eqs::mk_signed_var;

    fn get_variables(emons: &Emonics, indices: &[usize]) -> String {
        let variables: Vec<String> = indices
            .iter()
            .map(|index| emons.monics[*index].variable.to_string())
            .collect();
        variables.join(",")
    }

    // What the TS printed for the same state: the canonized monics, the use lists of 1..5, the
    // canonical monic of [4, 2], is_canonical_monic of 10..13 and 20, the sign-equivalent monics of
    // 11, the products of the variable 2 and those of the monic 12.
    fn show(emons: &mut Emonics, var_eqs: &VarEqs) -> String {
        let monics: Vec<String> = emons
            .monics
            .iter()
            .map(|monic| {
                let rvars: Vec<String> = monic.rvars.iter().map(usize::to_string).collect();
                format!("{}:{}:{}", monic.variable, rvars.join(","), monic.rsign)
            })
            .collect();
        let mut use_lists = Vec::new();
        for lp_var in 1..=5 {
            let mut list = emons.get_use_list(lp_var, var_eqs);
            let mut indices = Vec::new();
            while let Some(index) = list.next(emons) {
                indices.push(index);
            }
            use_lists.push(get_variables(emons, &indices));
        }
        let canonical = emons
            .find_canonical(&[4, 2])
            .map_or("undefined".to_string(), |index| {
                emons.monics[index].variable.to_string()
            });
        let is_canonical: Vec<String> = [10, 11, 12, 13, 20]
            .into_iter()
            .map(|lp_var| emons.is_canonical_monic(lp_var).to_string())
            .collect();
        let mut sign_equiv = emons.get_sign_equiv_monics(emons.get_index(11));
        let mut sign_equiv_indices = Vec::new();
        while let Some(index) = sign_equiv.next(emons) {
            sign_equiv_indices.push(index);
        }
        let mut products = emons.get_products_of(2, var_eqs);
        let mut product_indices = Vec::new();
        while let Some(index) = products.next(emons) {
            product_indices.push(index);
        }
        let mut monic_products = emons.get_products_of_monic(emons.get_index(12), var_eqs);
        let mut monic_product_indices = Vec::new();
        while let Some(index) = monic_products.next(emons) {
            monic_product_indices.push(index);
        }
        format!(
            "{} {} {canonical} {} {} {} {}",
            monics.join(" "),
            use_lists.join("|"),
            is_canonical.join(","),
            get_variables(emons, &sign_equiv_indices),
            get_variables(emons, &product_indices),
            get_variables(emons, &monic_product_indices),
        )
    }

    fn get_explanation(explanation: &Explanation) -> String {
        let indices: Vec<String> = explanation.iter().map(|index| index.to_string()).collect();
        indices.join(",")
    }

    // Expected values from running nla-var-eqs.ts and nla-emonics.ts on the same steps.
    #[test]
    fn canonizes_monics_over_variable_equalities_and_pops() {
        let mut var_eqs = VarEqs::new();
        let mut emons = Emonics::new();
        emons.add(10, &[3, 1, 2], &mut var_eqs);
        emons.add(11, &[4, 2], &mut var_eqs);
        emons.add(12, &[5, 1], &mut var_eqs);
        assert_eq!(
            show(&mut emons, &var_eqs),
            "10:1,2,3:false 11:2,4:false 12:1,5:false 12,10|11,10|10|11|12 11 \
             true,true,true,true,true 11 11,10 "
        );
        emons.push(&mut var_eqs);
        var_eqs.merge_minus(4, 3, vec![mk_leaf(7), None, mk_leaf(9)], &mut emons);
        var_eqs.merge_plus(5, 2, vec![mk_leaf(8)], &mut emons);
        assert_eq!(
            show(&mut emons, &var_eqs),
            "10:1,2,3:false 11:2,3:true 12:1,2:false 12,10|12,11,10|11,10|11,10|12,11,10 \
             undefined true,true,true,true,true 11 12,11,10 10"
        );
        emons.push(&mut var_eqs);
        var_eqs.merge_plus(3, 1, vec![mk_leaf(6)], &mut emons);
        emons.set_propagated(emons.get_index(12));
        assert_eq!(
            show(&mut emons, &var_eqs),
            "10:2,3,3:false 11:2,3:true 12:2,3:false \
             12,10,11,10|12,11,10|12,10,11,10|12,10,11,10|12,11,10 undefined \
             true,true,false,true,true 11,12 12,11,10 10,11"
        );
        let mut explanation = Explanation::new();
        var_eqs.explain(
            mk_signed_var(4, false),
            mk_signed_var(1, true),
            &mut explanation,
        );
        assert_eq!(get_explanation(&explanation), "6,7");
        assert_eq!(var_eqs.find(mk_signed_var(5, false)), 4);
        assert_eq!(var_eqs.get_class(mk_signed_var(1, false)), [2, 9, 6]);
        let mut explanation = Explanation::new();
        var_eqs.explain_var(4, &mut explanation);
        assert_eq!(get_explanation(&explanation), "7");
        emons.add(13, &[2, 4], &mut var_eqs);
        assert_eq!(
            show(&mut emons, &var_eqs),
            "10:2,3,3:false 11:2,3:true 12:2,3:false 13:2,3:true \
             13,12,10,11,10|13,12,11,10|13,12,10,11,10|13,12,10,11,10|13,12,11,10 undefined \
             true,true,false,false,true 11,13,12 13,12,11,10 13,10,11"
        );
        emons.push_core_undo(CoreUndo::PopIdivision);
        emons.push_core_undo(CoreUndo::SetUseNraModel(true));
        assert_eq!(
            emons.pop(1, &mut var_eqs),
            [CoreUndo::SetUseNraModel(true), CoreUndo::PopIdivision]
        );
        assert_eq!(
            show(&mut emons, &var_eqs),
            "10:1,2,3:false 11:2,3:true 12:1,2:false 12,10|12,11,10|11,10|11,10|12,11,10 \
             undefined true,true,true,false,true 11 12,11,10 10"
        );
        assert!(!emons.get(12).is_propagated);
        assert!(emons.pop(1, &mut var_eqs).is_empty());
        assert_eq!(
            show(&mut emons, &var_eqs),
            "10:1,2,3:false 11:2,4:false 12:1,5:false 12,10|11,10|10|11|12 11 \
             true,true,true,false,true 11 11,10 "
        );
    }
}
