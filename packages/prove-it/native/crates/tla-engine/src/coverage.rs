//! TLC's cost model (`tlc2.tool.coverage`) as the engine's search counts it with `-coverage`: the
//! tree of wrappers `CostModelCreator` builds of SANY's `OpApplNode`s for each action, invariant
//! and constraint, which tla-trace builds ([`Plan`]), and the counts the search adds to it as it
//! evaluates ([`Counted`]), which tla-trace prints as `CostModelCreator.report` does
//! (design/coverage.md). The counting variant of the compiled code is `compile/coverage.rs`; it is
//! compiled only when a search asks for coverage, so a search without it runs the code it always
//! ran.

use std::collections::HashMap;

use tla_ir::NodeId;

/// A wrapper of the cost model, by its position in the tree.
pub type Cm = u32;

/// `CostModel.DO_NOT_RECORD`: what TLC evaluates without counting, such as what it computes as
/// it starts.
pub const NO_CM: Cm = u32::MAX;

/// What the cost model's lookup asks of a node of SANY's semantic graph.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SanyKind {
    /// An `OpApplNode`, which a wrapper wraps.
    Appl,
    /// A `LetInNode`, which a root finds by its body.
    Let(u32),
    /// A literal or `@`, which no wrapper wraps.
    Other,
}

/// A node of SANY's semantic graph, numbered as tla-trace numbers them: what the cost model's
/// lookup asks of it, and its operands, which name the nodes SANY makes of an IR node's parts.
#[derive(Clone, Debug)]
pub struct SanyNode {
    pub kind: SanyKind,
    /// The operands, `None` for the missing condition of an OTHER arm.
    pub args: Vec<Option<u32>>,
}

/// A wrapper of an `OpApplNode` (`OpApplNodeWrapper`), or a root (`ActionWrapper`).
#[derive(Clone, Debug)]
pub struct Wrapper {
    /// The wrapped node, none for a root.
    pub node: Option<u32>,
    pub root: Cm,
    /// The children by their node, in the order added (`LinkedHashMap`).
    pub children: Vec<(u32, Cm)>,
    child_index: HashMap<u32, usize>,
    /// The wrappers of the definitions of the LET whose body this wraps.
    pub lets: Vec<(u32, Cm)>,
    /// For an application of a RECURSIVE operator: the nearest application of it above.
    pub recursive: Option<Cm>,
    pub is_primed: bool,
    pub is_unchanged: bool,
}

/// The cost model's tree: every root's wrappers, with no counts.
#[derive(Clone, Debug, Default)]
pub struct Tree {
    pub wrappers: Vec<Wrapper>,
}

impl Tree {
    pub fn add(&mut self, node: Option<u32>, root: Cm) -> Cm {
        self.wrappers.push(Wrapper {
            node,
            root,
            children: Vec::new(),
            child_index: HashMap::new(),
            lets: Vec::new(),
            recursive: None,
            is_primed: false,
            is_unchanged: false,
        });
        (self.wrappers.len() - 1) as Cm
    }

    /// `addChild`: a child already there is replaced in its place, as `LinkedHashMap.put` does
    /// with assertions off.
    pub fn add_child(&mut self, parent: Cm, key: u32, child: Cm) {
        let wrapper = &mut self.wrappers[parent as usize];
        match wrapper.child_index.get(&key) {
            Some(&position) => wrapper.children[position].1 = child,
            None => {
                wrapper.child_index.insert(key, wrapper.children.len());
                wrapper.children.push((key, child));
            }
        }
    }

    pub fn child(&self, parent: Cm, key: u32) -> Option<Cm> {
        let wrapper = &self.wrappers[parent as usize];
        // Most wrappers have a few children, which a scan finds sooner than a hash.
        if wrapper.children.len() <= 8 {
            return wrapper
                .children
                .iter()
                .find(|(child, _)| *child == key)
                .map(|&(_, cm)| cm);
        }
        wrapper
            .child_index
            .get(&key)
            .map(|&position| wrapper.children[position].1)
    }

    pub fn root_of(&self, cm: Cm) -> Cm {
        if cm == NO_CM {
            cm
        } else {
            self.wrappers[cm as usize].root
        }
    }

    /// `CostModel.get`: the wrapper of `node` under `cm`, or `Err(cm)` where TLC's lookup fails,
    /// which TLC reports and then counts into `cm`.
    pub fn get(&self, cm: Cm, node: u32, kind: SanyKind) -> Result<Cm, Cm> {
        if cm == NO_CM {
            return Ok(cm);
        }
        let wrapper = &self.wrappers[cm as usize];
        if wrapper.node.is_none() {
            // An ActionWrapper finds a LET's body for the LET.
            let key = match kind {
                SanyKind::Let(body) => body,
                _ => node,
            };
            return Ok(self.child(cm, key).unwrap_or(cm));
        }
        if wrapper.node == Some(node) || kind != SanyKind::Appl {
            return Ok(cm);
        }
        if let Some(child) = self.child(cm, node) {
            return Ok(child);
        }
        if let Some(recursive) = wrapper.recursive
            && let Some(child) = self.child(recursive, node)
        {
            return Ok(child);
        }
        if let Some(&(_, child)) = wrapper.lets.iter().find(|(key, _)| *key == node) {
            return Ok(child);
        }
        Err(cm)
    }
}

/// What a search counts with `-coverage`: the tree, SANY's nodes it wraps and which of them each
/// IR node is, and each root of the model with the IR node TLC evaluates for it.
#[derive(Clone, Debug, Default)]
pub struct Plan {
    pub tree: Tree,
    pub nodes: Vec<SanyNode>,
    /// The SANY node each IR node translates to, by the IR node a reference resolves to.
    pub of_ir: HashMap<NodeId, u32>,
    /// The initial predicates, in TLC's order.
    pub inits: Vec<(NodeId, Cm)>,
    /// The root of each of the IR's actions, in its order.
    pub actions: Vec<Cm>,
    pub invariants: Vec<(NodeId, Cm)>,
    pub action_constraints: Vec<(NodeId, Cm)>,
    pub constraints: Vec<(NodeId, Cm)>,
}

impl Plan {
    /// The wrapper TLC's evaluation of the SANY node counts into under `cm`, or why the counting
    /// variant can't follow it.
    pub fn get(&self, cm: Cm, node: u32) -> Result<Cm, String> {
        self.tree
            .get(cm, node, self.nodes[node as usize].kind)
            .map_err(|_| "a lookup of the cost model TLC fails".to_string())
    }
}

/// What the search counted: each wrapper's count and secondary count, and the estimate of how
/// many distinct values each variable took, in the IR's order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Counted {
    pub counts: Vec<u64>,
    pub secondary: Vec<u64>,
    pub values: Vec<i64>,
}

/// `HyperLogLog(10)`, TLC's estimate of how many distinct values a variable took
/// (`CountDistinct`).
#[derive(Clone, Debug)]
pub struct HyperLogLog {
    registers: Vec<i32>,
}

const BITS: u32 = 10;

impl Default for HyperLogLog {
    fn default() -> HyperLogLog {
        HyperLogLog {
            registers: vec![0; 1 << BITS],
        }
    }
}

impl HyperLogLog {
    pub fn add(&mut self, hash: u64) {
        let index = (hash >> (64 - BITS)) as usize;
        let w = ((hash << BITS) | (1u64 << (BITS - 1))).leading_zeros() as i32 + 1;
        self.registers[index] = self.registers[index].max(w);
    }

    pub fn count(&self) -> i64 {
        let m = self.registers.len() as f64;
        let alpha = 0.7213 / (1.0 + 1.079 / m);
        let mut z = 0.0;
        for &register in &self.registers {
            // Java's int shift takes its distance modulo 32.
            z += 1.0 / f64::from(1i32.wrapping_shl(register as u32));
        }
        let mut estimate = alpha * m * m / z;
        if estimate <= 2.5 * m {
            let zeros = self
                .registers
                .iter()
                .filter(|&&register| register == 0)
                .count();
            if zeros != 0 {
                estimate = m * (m / zeros as f64).ln();
            }
        } else if estimate > 1.0 / 30.0 * 2f64.powi(64) {
            estimate = -(2f64.powi(64)) * (1.0 - estimate / 2f64.powi(64)).ln();
        }
        // `(int) estimate`, which Java saturates.
        i64::from(estimate as i32)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn counts_few_values_exactly() {
        let mut estimate = HyperLogLog::default();
        assert_eq!(estimate.count(), 0);
        estimate.add(0);
        estimate.add(1 << 63);
        assert_eq!(estimate.count(), 2);
    }

    #[test]
    fn finds_a_child_by_its_node_and_a_lets_body_from_a_root() {
        let mut tree = Tree::default();
        let root = tree.add(None, 0);
        let child = tree.add(Some(7), root);
        tree.add_child(root, 7, child);
        assert_eq!(tree.get(root, 7, SanyKind::Appl), Ok(child));
        assert_eq!(tree.get(root, 3, SanyKind::Let(7)), Ok(child));
        assert_eq!(tree.get(child, 7, SanyKind::Appl), Ok(child));
        assert_eq!(tree.get(child, 8, SanyKind::Other), Ok(child));
        assert_eq!(tree.get(child, 9, SanyKind::Appl), Err(child));
        assert_eq!(tree.get(NO_CM, 9, SanyKind::Appl), Ok(NO_CM));
    }
}
