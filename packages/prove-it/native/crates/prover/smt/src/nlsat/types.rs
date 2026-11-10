// Ported from Z3 (src/nlsat/nlsat_types.h, src/nlsat/nlsat_clause.h), MIT license, see
// z3-license.txt. The atoms and clauses of nlsat. A literal is 2 * boolVar + sign, where sign 1
// negates the atom.
use std::cell::Cell;
use std::rc::Rc;

use super::Dependency;
use super::polynomial::{Polynomial, Var};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum IneqKind {
    Eq,
    Lt,
    Gt,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum RootKind {
    RootEq,
    RootLt,
    RootGt,
    RootLe,
    RootGe,
}

/// TS `Atom["kind"]`: the kind of either sort of atom.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum AtomKind {
    Ineq(IneqKind),
    Root(RootKind),
}

// p1 * ... * pn kind 0, where isEven[i] marks a factor of even degree, which only its zeros
// matter for. maxVar is the largest maximal variable of the factors.
pub struct IneqAtom {
    pub kind: IneqKind,
    pub bool_var: u32,
    pub max_var: Cell<Var>,
    pub polynomials: Vec<Polynomial>,
    pub is_even: Vec<bool>,
}

// x kind root[index](p): the index-th real root of p, from 1, as a polynomial in x at the values of
// the variables below x. maxVar is x.
pub struct RootAtom {
    pub kind: RootKind,
    pub bool_var: u32,
    pub max_var: Cell<Var>,
    pub index: u32,
    pub polynomial: Polynomial,
}

pub enum Atom {
    Ineq(IneqAtom),
    Root(RootAtom),
}

/// Atoms are shared: the atom table updates `max_var` in place.
pub type AtomRef = Rc<Atom>;

impl Atom {
    pub fn bool_var(&self) -> u32 {
        match self {
            Atom::Ineq(atom) => atom.bool_var,
            Atom::Root(atom) => atom.bool_var,
        }
    }

    pub fn max_var(&self) -> Var {
        match self {
            Atom::Ineq(atom) => atom.max_var.get(),
            Atom::Root(atom) => atom.max_var.get(),
        }
    }

    pub fn kind(&self) -> AtomKind {
        match self {
            Atom::Ineq(atom) => AtomKind::Ineq(atom.kind),
            Atom::Root(atom) => AtomKind::Root(atom.kind),
        }
    }
}

// A clause, with the assumptions it depends on. isActive marks a learned clause that took part in
// a conflict since the last garbage collection.
pub struct Clause {
    pub id: u32,
    pub literals: Vec<u32>,
    pub is_learned: bool,
    pub assumptions: Dependency,
    pub is_active: Cell<bool>,
}

pub type ClauseRef = Rc<Clause>;

pub fn is_ineq_atom(atom: &Atom) -> bool {
    matches!(atom, Atom::Ineq(_))
}
