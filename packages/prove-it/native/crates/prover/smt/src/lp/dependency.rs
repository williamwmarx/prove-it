//! Ported from Z3 (src/util/dependency.h), MIT license, through `lp/dependency.ts`. The witnesses
//! of bounds: a DAG whose leaves are constraint indices. Without proofs, lar_solver's
//! evidence_manager is the plain u_dependency_manager.
//!
//! A node is shared by `Rc`, and two dependencies are the same node when `Rc::ptr_eq`, as the
//! TypeScript compares objects with `===`. The marks the TypeScript keeps in the nodes are a set
//! local to `linearize`.

use std::collections::HashSet;
use std::rc::Rc;

pub enum DependencyNode {
    Leaf(u32),
    Join(Rc<DependencyNode>, Rc<DependencyNode>),
}

/// `null` is `None`.
pub type Dependency = Option<Rc<DependencyNode>>;

pub fn mk_leaf(value: u32) -> Dependency {
    Some(Rc::new(DependencyNode::Leaf(value)))
}

pub fn mk_join(first: &Dependency, second: &Dependency) -> Dependency {
    match (first, second) {
        (None, _) => second.clone(),
        (_, None) => first.clone(),
        (Some(left), Some(right)) if Rc::ptr_eq(left, right) => first.clone(),
        (Some(left), Some(right)) => Some(Rc::new(DependencyNode::Join(
            Rc::clone(left),
            Rc::clone(right),
        ))),
    }
}

/// linearize: the leaves in breadth-first order, each once, from the given roots.
pub fn linearize(roots: &[Dependency]) -> Vec<u32> {
    // Only looked up, never iterated, so its order cannot matter.
    let mut marked: HashSet<*const DependencyNode> = HashSet::new();
    let mut todo: Vec<&DependencyNode> = Vec::new();
    for root in roots.iter().flatten() {
        if marked.insert(Rc::as_ptr(root)) {
            todo.push(root);
        }
    }
    let mut values = Vec::new();
    let mut head = 0;
    while head < todo.len() {
        match todo[head] {
            DependencyNode::Leaf(value) => values.push(*value),
            DependencyNode::Join(first, second) => {
                for child in [first, second] {
                    if marked.insert(Rc::as_ptr(child)) {
                        todo.push(child);
                    }
                }
            }
        }
        head += 1;
    }
    values
}
