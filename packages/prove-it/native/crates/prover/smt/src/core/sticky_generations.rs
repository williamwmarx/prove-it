//! Ported from Z3 (src/smt/smt_context.cpp), MIT license, see z3-license.txt, through
//! `sticky-generations.ts`. m_sticky_generation_updates: the generations that update_generation
//! lowered, by node. Only a node of the same declaration can be congruent to another, so the updates
//! are grouped by declaration. Each group keeps its updates in the order of insertion, as a Map
//! does, in arrays that iterate without allocating. A deleted update leaves a hole until holes are
//! half of its group.

use std::collections::HashMap;

use super::enode::{EnodeId, Enodes};

/// The updates of a declaration in the order of insertion, where a deleted one is `None`.
#[derive(Clone, Debug)]
pub struct Group {
    pub nodes: Vec<Option<EnodeId>>,
    pub generations: Vec<u32>,
    /// Only looked up, never iterated.
    indices: HashMap<EnodeId, usize>,
    num_holes: usize,
}

#[derive(Clone, Debug, Default)]
pub struct StickyGenerations {
    /// Only looked up, never iterated.
    groups: HashMap<u32, Group>,
}

impl StickyGenerations {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn set(&mut self, enodes: &Enodes, node: EnodeId, generation: u32) {
        let decl = enodes.get(node).decl;
        let Some(group) = self.groups.get_mut(&decl) else {
            self.groups.insert(
                decl,
                Group {
                    nodes: vec![Some(node)],
                    generations: vec![generation],
                    indices: HashMap::from([(node, 0)]),
                    num_holes: 0,
                },
            );
            return;
        };
        if let Some(index) = group.indices.get(&node) {
            group.generations[*index] = generation;
            return;
        }
        group.indices.insert(node, group.nodes.len());
        group.nodes.push(Some(node));
        group.generations.push(generation);
    }

    pub fn delete(&mut self, enodes: &Enodes, node: EnodeId) {
        let Some(group) = self.groups.get_mut(&enodes.get(node).decl) else {
            return;
        };
        let Some(index) = group.indices.remove(&node) else {
            return;
        };
        group.nodes[index] = None;
        group.num_holes += 1;
        if 2 * group.num_holes > group.nodes.len() {
            compact(group);
        }
    }

    /// The updates of the declaration in the order of insertion, where a deleted one is `None`.
    pub fn get_group(&self, decl: u32) -> Option<&Group> {
        self.groups.get(&decl)
    }
}

fn compact(group: &mut Group) {
    let mut size = 0;
    for index in 0..group.nodes.len() {
        let Some(node) = group.nodes[index] else {
            continue;
        };
        group.nodes[size] = Some(node);
        group.generations[size] = group.generations[index];
        group.indices.insert(node, size);
        size += 1;
    }
    group.nodes.truncate(size);
    group.generations.truncate(size);
    group.num_holes = 0;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn keeps_the_updates_of_a_declaration_in_order_and_compacts_holes() {
        let mut enodes = Enodes::new();
        let nodes: Vec<EnodeId> = (0..4)
            .map(|owner| {
                enodes.mk(
                    owner,
                    7,
                    0,
                    None,
                    None,
                    Vec::new(),
                    0,
                    false,
                    false,
                    false,
                    true,
                    0,
                )
            })
            .collect();
        let other = enodes.mk(
            9,
            8,
            0,
            None,
            None,
            Vec::new(),
            0,
            false,
            false,
            false,
            true,
            0,
        );
        let mut sticky = StickyGenerations::new();
        for (generation, node) in nodes.iter().enumerate() {
            sticky.set(&enodes, *node, generation as u32 + 10);
        }
        sticky.set(&enodes, nodes[1], 5);
        assert!(sticky.get_group(8).is_none());
        sticky.set(&enodes, other, 1);
        sticky.delete(&enodes, nodes[0]);
        let group = sticky.get_group(7);
        assert_eq!(
            group.map(|group| group.nodes.clone()),
            Some(vec![None, Some(nodes[1]), Some(nodes[2]), Some(nodes[3])])
        );
        sticky.delete(&enodes, nodes[2]);
        sticky.delete(&enodes, nodes[2]);
        sticky.delete(&enodes, nodes[1]);
        let group = sticky.get_group(7);
        assert_eq!(
            group.map(|group| (group.nodes.clone(), group.generations.clone())),
            Some((vec![Some(nodes[3])], vec![13]))
        );
        sticky.set(&enodes, nodes[0], 2);
        sticky.set(&enodes, nodes[3], 4);
        let group = sticky.get_group(7);
        assert_eq!(
            group.map(|group| (group.nodes.clone(), group.generations.clone())),
            Some((vec![Some(nodes[3]), Some(nodes[0])], vec![4, 2]))
        );
    }
}
