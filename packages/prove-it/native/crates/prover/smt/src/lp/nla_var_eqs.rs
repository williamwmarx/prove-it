// Ported from Z3 (src/math/lp/var_eqs.h, src/math/lp/nla_defs.h), MIT license, see z3-license.txt.
// Equivalences between signed lp variables, x = y or x = -y, with the bounds that justify them. A
// signed variable is the index 2 * var + sign.
//
// TS installs the merge handler once (`setMergeHandler`, which `Emonics` calls); here the methods
// that merge or pop take it: `merge`, `merge_plus`, `merge_minus` and `pop` take
// `&mut impl UnionFindHandler`, which nla passes as its `Emonics` (`&mut self.emons`).
use crate::lp::dependency::Dependency;
use crate::lp::explanation::Explanation;
use crate::lp::union_find::{TrailStack, UnionFind, UnionFindHandler, UnionFindUndo};

pub fn mk_signed_var(lp_var: usize, is_negated: bool) -> usize {
    lp_var * 2 + usize::from(is_negated)
}

pub fn get_signed_var_var(signed_var: usize) -> usize {
    signed_var >> 1
}

pub fn is_signed_var_negated(signed_var: usize) -> bool {
    signed_var & 1 == 1
}

pub fn negate_signed_var(signed_var: usize) -> usize {
    signed_var ^ 1
}

// VarEqs::find over its union-find, for the merge handlers, which run while the VarEqs is borrowed.
pub fn find_in(union_find: &UnionFind, signed_var: usize) -> usize {
    if signed_var >= union_find.num_vars() {
        signed_var
    } else {
        union_find.find(signed_var)
    }
}

// An eq_justification: its dependencies up to the first null.
pub type EqJustification = Vec<Dependency>;

struct EqEdge {
    signed_var: usize,
    justification: EqJustification,
}

struct VarFrame {
    signed_var: usize,
    index: usize,
}

#[derive(Default)]
pub struct VarEqs {
    trail: TrailStack<UnionFindUndo>,
    eq_trail: Vec<(usize, usize)>,
    eq_trail_scopes: Vec<usize>,
    eqs: Vec<Vec<EqEdge>>,
    is_marked: Vec<bool>,
    union_find: UnionFind,
}

impl VarEqs {
    pub fn new() -> VarEqs {
        VarEqs::default()
    }

    pub fn union_find(&self) -> &UnionFind {
        &self.union_find
    }

    pub fn push(&mut self) {
        self.eq_trail_scopes.push(self.eq_trail.len());
        self.trail.push_scope();
    }

    pub fn pop(&mut self, count: usize, handler: &mut impl UnionFindHandler) {
        let size = self.eq_trail_scopes[self.eq_trail_scopes.len() - count];
        for index in (size..self.eq_trail.len()).rev() {
            let pair = self.eq_trail[index];
            self.eqs[pair.0].pop();
            self.eqs[pair.1].pop();
            self.eqs[negate_signed_var(pair.0)].pop();
            self.eqs[negate_signed_var(pair.1)].pop();
        }
        self.eq_trail.truncate(size);
        self.eq_trail_scopes
            .truncate(self.eq_trail_scopes.len() - count);
        let trail_size = self.trail.pop_scope(count);
        while let Some(undo) = self.trail.pop_above(trail_size) {
            self.union_find.undo(undo, handler);
        }
    }

    pub fn merge(
        &mut self,
        v1: usize,
        v2: usize,
        justification: EqJustification,
        handler: &mut impl UnionFindHandler,
    ) {
        if v1 == v2 || get_signed_var_var(self.find(v1)) == get_signed_var_var(self.find(v2)) {
            return;
        }
        let max_index = v1.max(v2) + 2;
        while self.eqs.len() < max_index {
            self.eqs.push(Vec::new());
        }
        while self.union_find.num_vars() <= max_index {
            self.union_find.mk_var(&mut self.trail);
        }
        self.eq_trail.push((v1, v2));
        self.union_find.merge(&mut self.trail, handler, v1, v2);
        self.union_find.merge(
            &mut self.trail,
            handler,
            negate_signed_var(v1),
            negate_signed_var(v2),
        );
        self.eqs[v1].push(EqEdge {
            signed_var: v2,
            justification: justification.clone(),
        });
        self.eqs[v2].push(EqEdge {
            signed_var: v1,
            justification: justification.clone(),
        });
        self.eqs[negate_signed_var(v1)].push(EqEdge {
            signed_var: negate_signed_var(v2),
            justification: justification.clone(),
        });
        self.eqs[negate_signed_var(v2)].push(EqEdge {
            signed_var: negate_signed_var(v1),
            justification,
        });
    }

    pub fn merge_plus(
        &mut self,
        first: usize,
        second: usize,
        justification: EqJustification,
        handler: &mut impl UnionFindHandler,
    ) {
        self.merge(
            mk_signed_var(first, false),
            mk_signed_var(second, false),
            justification,
            handler,
        );
    }

    pub fn merge_minus(
        &mut self,
        first: usize,
        second: usize,
        justification: EqJustification,
        handler: &mut impl UnionFindHandler,
    ) {
        self.merge(
            mk_signed_var(first, false),
            mk_signed_var(second, true),
            justification,
            handler,
        );
    }

    pub fn find(&self, signed_var: usize) -> usize {
        find_in(&self.union_find, signed_var)
    }

    pub fn find_var(&self, lp_var: usize) -> usize {
        self.find(mk_signed_var(lp_var, false))
    }

    pub fn is_root(&self, lp_var: usize) -> bool {
        get_signed_var_var(self.find_var(lp_var)) == lp_var
    }

    // explain_bfs: the justifications along a shortest path from v1 to v2.
    pub fn explain(&mut self, v1: usize, v2: usize, explanation: &mut Explanation) {
        if v1 == v2 {
            return;
        }
        let mut todo = vec![VarFrame {
            signed_var: v1,
            index: 0,
        }];
        let mut justifications: Vec<&[Dependency]> = vec![&[]];
        let mut marked_trail = vec![v1];
        set_marked(&mut self.is_marked, v1);
        let mut head = 0;
        loop {
            let signed_var = todo[head].signed_var;
            if signed_var == v2 {
                break;
            }
            for edge in self.eqs[signed_var].iter().rev() {
                if self.is_marked.get(edge.signed_var) == Some(&true) {
                    continue;
                }
                todo.push(VarFrame {
                    signed_var: edge.signed_var,
                    index: head,
                });
                justifications.push(&edge.justification);
                marked_trail.push(edge.signed_var);
                set_marked(&mut self.is_marked, edge.signed_var);
            }
            head += 1;
        }
        while head != 0 {
            for dep in justifications[head] {
                if dep.is_none() {
                    break;
                }
                explanation.push_dependency(dep);
            }
            head = todo[head].index;
        }
        for signed_var in marked_trail {
            self.is_marked[signed_var] = false;
        }
    }

    pub fn explain_var(&mut self, lp_var: usize, explanation: &mut Explanation) {
        let signed_var = mk_signed_var(lp_var, false);
        self.explain(self.find(signed_var), signed_var, explanation);
    }

    // The members of the class of a signed variable, from the variable around the union-find cycle.
    pub fn get_class(&self, signed_var: usize) -> Vec<usize> {
        if signed_var >= self.union_find.num_vars() {
            return vec![signed_var];
        }
        let mut members = Vec::new();
        let mut current = signed_var;
        loop {
            members.push(current);
            current = self.union_find.next(current);
            if current == signed_var {
                return members;
            }
        }
    }
}

// isMarked is a sparse TS array whose holes read as false.
fn set_marked(is_marked: &mut Vec<bool>, signed_var: usize) {
    if is_marked.len() <= signed_var {
        is_marked.resize(signed_var + 1, false);
    }
    is_marked[signed_var] = true;
}
