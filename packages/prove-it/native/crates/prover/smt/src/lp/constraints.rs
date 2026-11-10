// Ported from Z3 (src/math/lp/lar_constraints.h), MIT license, see z3-license.txt. The bounds
// that the theory asserts on columns, each with a leaf dependency on its own index, and the set of
// active ones, both undone by pop.
use crate::lp::numeric_pair::Impq;
use crate::util::dependency::{Dependency, mk_leaf};

// lconstraint_kind: flipping negates the kind, and halving a non-strict kind gives the strict one.
pub type ConstraintKind = i32;
pub const KIND_LE: ConstraintKind = -2;
pub const KIND_LT: ConstraintKind = -1;
pub const KIND_EQ: ConstraintKind = 0;
pub const KIND_GT: ConstraintKind = 1;
pub const KIND_GE: ConstraintKind = 2;
// NE: a kind of nla's inequalities, never of a bound the theory asserts.
pub const KIND_NE: ConstraintKind = 3;

pub struct LarConstraint {
    pub column: usize,
    pub kind: ConstraintKind,
    pub rhs: Impq,
    pub dep: Dependency,
    pub is_active: bool,
    // Made for the atom of an nla lemma.
    pub is_auxiliary: bool,
}

struct ConstraintScope {
    size: usize,
    active_size: usize,
}

#[derive(Default)]
pub struct ConstraintSet {
    pub constraints: Vec<LarConstraint>,
    active: Vec<usize>,
    scopes: Vec<ConstraintScope>,
    // m_is_auxiliary_mode: whether new constraints are auxiliary.
    pub is_auxiliary_mode: bool,
}

impl ConstraintSet {
    pub fn add(&mut self, column: usize, kind: ConstraintKind, rhs: Impq) -> usize {
        let index = self.constraints.len();
        self.constraints.push(LarConstraint {
            column,
            kind,
            rhs,
            dep: mk_leaf(index as u32),
            is_active: false,
            is_auxiliary: self.is_auxiliary_mode,
        });
        index
    }

    pub fn activate(&mut self, index: usize) {
        let constraint = &mut self.constraints[index];
        if constraint.is_active {
            return;
        }
        constraint.is_active = true;
        self.active.push(index);
    }

    pub fn push_scope(&mut self) {
        self.scopes.push(ConstraintScope {
            size: self.constraints.len(),
            active_size: self.active.len(),
        });
    }

    pub fn pop_scope(&mut self, count: usize) {
        let scope = self.scopes.len() - count;
        let size = self.scopes[scope].size;
        let active_size = self.scopes[scope].active_size;
        self.scopes.truncate(scope);
        for index in (active_size..self.active.len()).rev() {
            self.constraints[self.active[index]].is_active = false;
        }
        self.active.truncate(active_size);
        self.constraints.truncate(size);
    }
}
