//! Ported from Isabelle2025's Pure/net.ML, discrimination nets. Copyright (c) 1986-2025 University
//! of Cambridge, Technische Universitaet Muenchen, and contributors, see LICENSE.

use std::rc::Rc;

use super::list::{List, cons, list_iter};
use super::name::bound_name;
use super::table::{
    Table, delete_table, empty_table, fast_string_ord, fold_table, is_empty_table, lookup_table,
    update_table,
};
use super::term::{Name, Term, TermNode, head_of};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NetKey {
    Comb,
    Var,
    Atom(Name),
}

pub struct NetNode<Item> {
    pub comb: Net<Item>,
    pub var: Net<Item>,
    pub atoms: Table<Name, Net<Item>>,
}

impl<Item> Clone for NetNode<Item> {
    fn clone(&self) -> Self {
        NetNode {
            comb: self.comb.clone(),
            var: self.var.clone(),
            atoms: self.atoms.clone(),
        }
    }
}

/// A persistent net: updates share the parts they leave as they were.
pub enum Net<Item> {
    Leaf(Rc<Vec<Item>>),
    Net(Rc<NetNode<Item>>),
}

impl<Item> Clone for Net<Item> {
    fn clone(&self) -> Self {
        match self {
            Net::Leaf(items) => Net::Leaf(items.clone()),
            Net::Net(node) => Net::Net(node.clone()),
        }
    }
}

pub fn empty_net<Item>() -> Net<Item> {
    Net::Leaf(Rc::new(Vec::new()))
}

fn is_empty_net<Item>(net: &Net<Item>) -> bool {
    matches!(net, Net::Leaf(items) if items.is_empty())
}

fn make_node<Item>() -> NetNode<Item> {
    NetNode {
        comb: empty_net(),
        var: empty_net(),
        atoms: empty_table(fast_string_ord),
    }
}

/// Net.key_of_term: preorder keys, with any term headed by a variable or an abstraction as a Var.
pub fn key_of_term(term: &Term) -> Vec<NetKey> {
    fn add(keys: &mut Vec<NetKey>, current: &Term) {
        let head = head_of(current);
        if head.is_var() || head.is_abs() {
            keys.push(NetKey::Var);
            return;
        }
        rands(keys, current);
    }
    fn rands(keys: &mut Vec<NetKey>, inner: &Term) {
        match &**inner {
            TermNode::App { fun, arg, .. } => {
                keys.push(NetKey::Comb);
                rands(keys, fun);
                add(keys, arg);
            }
            TermNode::Const { name, .. } | TermNode::Free { name, .. } => {
                keys.push(NetKey::Atom(name.clone()))
            }
            TermNode::Bound { index } => keys.push(NetKey::Atom(bound_name(*index))),
            _ => {}
        }
    }
    let mut keys = Vec::new();
    add(&mut keys, term);
    keys
}

/// Net.insert: raises nothing on a duplicate here; insert_safe semantics with eq. It walks down
/// the keys and rebuilds the path bottom-up, so a long key list can't exhaust the stack. `None`
/// where the item is already there.
pub fn insert_net<Item: Clone>(
    is_equal: impl Fn(&Item, &Item) -> bool,
    keys: &[NetKey],
    item: Item,
    net: &Net<Item>,
) -> Option<Net<Item>> {
    let mut path: Vec<NetNode<Item>> = Vec::new();
    let mut node = net.clone();
    for key in keys {
        let expanded = match &node {
            Net::Net(expanded) => (**expanded).clone(),
            Net::Leaf(_) => make_node(),
        };
        node = match key {
            NetKey::Comb => expanded.comb.clone(),
            NetKey::Var => expanded.var.clone(),
            NetKey::Atom(name) => lookup_table(&expanded.atoms, name)
                .cloned()
                .unwrap_or_else(empty_net),
        };
        path.push(expanded);
    }
    let items: &[Item] = match &node {
        Net::Leaf(items) => items,
        Net::Net(_) => &[],
    };
    if items.iter().any(|other| is_equal(other, &item)) {
        return None;
    }
    let leaf = Net::Leaf(Rc::new([vec![item], items.to_vec()].concat()));
    Some(
        path.into_iter()
            .zip(keys)
            .rev()
            .fold(leaf, |child, (expanded, key)| {
                Net::Net(Rc::new(match key {
                    NetKey::Comb => NetNode {
                        comb: child,
                        ..expanded
                    },
                    NetKey::Var => NetNode {
                        var: child,
                        ..expanded
                    },
                    NetKey::Atom(name) => NetNode {
                        atoms: update_table(&expanded.atoms, name.clone(), child),
                        ..expanded
                    },
                }))
            }),
    )
}

pub fn insert_term_net<Item: Clone>(term: &Term, item: Item, net: &Net<Item>) -> Net<Item> {
    insert_net(|_, _| false, &key_of_term(term), item, net).unwrap_or_else(|| net.clone())
}

fn new_net<Item>(node: NetNode<Item>) -> Net<Item> {
    if is_empty_net(&node.comb) && is_empty_net(&node.var) && is_empty_table(&node.atoms) {
        empty_net()
    } else {
        Net::Net(Rc::new(node))
    }
}

/// Net.delete: `None` where Isabelle raises DELETE.
fn delete_net<Item: Clone>(
    is_equal: &impl Fn(&Item, &Item) -> bool,
    keys: &[NetKey],
    item: &Item,
    net: &Net<Item>,
) -> Option<Net<Item>> {
    let node = match net {
        Net::Leaf(items) => {
            if !keys.is_empty() || !items.iter().any(|other| is_equal(other, item)) {
                return None;
            }
            let kept = items
                .iter()
                .filter(|other| !is_equal(other, item))
                .cloned()
                .collect();
            return Some(Net::Leaf(Rc::new(kept)));
        }
        Net::Net(node) => node,
    };
    let (key, rest) = keys.split_first()?;
    match key {
        NetKey::Comb => {
            let comb = delete_net(is_equal, rest, item, &node.comb)?;
            Some(new_net(NetNode {
                comb,
                ..(**node).clone()
            }))
        }
        NetKey::Var => {
            let var = delete_net(is_equal, rest, item, &node.var)?;
            Some(new_net(NetNode {
                var,
                ..(**node).clone()
            }))
        }
        NetKey::Atom(name) => {
            let existing = lookup_table(&node.atoms, name)?;
            let child = delete_net(is_equal, rest, item, existing)?;
            let atoms = if is_empty_net(&child) {
                delete_table(&node.atoms, name)
            } else {
                update_table(&node.atoms, name.clone(), child)
            };
            Some(new_net(NetNode {
                atoms,
                ..(**node).clone()
            }))
        }
    }
}

pub fn delete_term_safe<Item: Clone>(
    is_equal: impl Fn(&Item, &Item) -> bool,
    term: &Term,
    item: &Item,
    net: &Net<Item>,
) -> Net<Item> {
    delete_net(&is_equal, &key_of_term(term), item, net).unwrap_or_else(|| net.clone())
}

/// The lists of nets that matching conses up, as Isabelle's lists.
type Nets<Item> = List<Net<Item>>;

fn to_array<Item>(nets: &Nets<Item>) -> Vec<Net<Item>> {
    list_iter(nets).cloned().collect()
}

fn net_skip<Item>(net: &Net<Item>, nets: Nets<Item>) -> Nets<Item> {
    let Net::Net(node) = net else {
        return nets;
    };
    let children = to_array(&net_skip(&node.comb, None));
    let result = fold_table(
        |_name, child: &Net<Item>, tail| cons(child.clone(), tail),
        &node.atoms,
        cons(node.var.clone(), nets),
    );
    children
        .iter()
        .rev()
        .fold(result, |result, child| net_skip(child, result))
}

fn look1<Item>(atoms: &Table<Name, Net<Item>>, name: &Name, nets: Nets<Item>) -> Nets<Item> {
    match lookup_table(atoms, name) {
        None => nets,
        Some(net) => cons(net.clone(), nets),
    }
}

fn rands<Item>(is_unif: bool, term: &Term, net: &Net<Item>, nets: Nets<Item>) -> Nets<Item> {
    let Net::Net(node) = net else {
        return nets;
    };
    match &**term {
        TermNode::App { fun, arg, .. } => {
            let children = to_array(&rands(is_unif, fun, &node.comb, None));
            children
                .iter()
                .rev()
                .fold(nets, |result, child| matching(is_unif, arg, child, result))
        }
        TermNode::Const { name, .. } | TermNode::Free { name, .. } => {
            look1(&node.atoms, name, nets)
        }
        TermNode::Bound { index } => look1(&node.atoms, &bound_name(*index), nets),
        _ => nets,
    }
}

fn matching<Item>(is_unif: bool, term: &Term, net: &Net<Item>, nets: Nets<Item>) -> Nets<Item> {
    let Net::Net(node) = net else {
        return nets;
    };
    let head = head_of(term);
    if head.is_var() || head.is_abs() {
        return if is_unif {
            net_skip(net, nets)
        } else {
            cons(node.var.clone(), nets)
        };
    }
    rands(is_unif, term, net, cons(node.var.clone(), nets))
}

fn extract_leaves<Item: Clone>(nets: &Nets<Item>) -> Vec<Item> {
    let mut items = Vec::new();
    for net in list_iter(nets) {
        if let Net::Leaf(leaf) = net {
            items.extend(leaf.iter().cloned());
        }
    }
    items
}

pub fn match_term_net<Item: Clone>(net: &Net<Item>, term: &Term) -> Vec<Item> {
    extract_leaves(&matching(false, term, net, None))
}

pub fn unify_term_net<Item: Clone>(net: &Net<Item>, term: &Term) -> Vec<Item> {
    extract_leaves(&matching(true, term, net, None))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pure::term_ord::tests::sample_terms;

    // Expected values from running net.ts with bun on the same terms.
    #[test]
    fn matches_and_unifies() {
        let terms = sample_terms();
        let net = terms
            .iter()
            .enumerate()
            .fold(empty_net(), |net, (index, term)| {
                insert_term_net(term, index, &net)
            });
        let all = vec![9, 17, 16, 13, 7, 6, 8, 12, 3, 2, 1, 15, 14, 0, 11, 10, 5, 4];
        let consts = vec![15, 14, 0, 11, 10, 5, 4];
        let matched: Vec<Vec<usize>> = terms
            .iter()
            .map(|term| match_term_net(&net, term))
            .collect();
        assert_eq!(
            matched,
            [
                consts.clone(),
                vec![1, 11, 10, 5, 4],
                vec![2, 11, 10, 5, 4],
                vec![3, 11, 10, 5, 4],
                vec![11, 10, 5, 4],
                vec![11, 10, 5, 4],
                vec![6, 8, 11, 10, 5, 4],
                vec![7, 8, 11, 10, 5, 4],
                vec![8, 11, 10, 5, 4],
                vec![9, 17, 11, 10, 5, 4],
                vec![11, 10, 5, 4],
                vec![11, 10, 5, 4],
                vec![12, 11, 10, 5, 4],
                vec![13, 8, 11, 10, 5, 4],
                consts.clone(),
                consts.clone(),
                vec![16, 11, 10, 5, 4],
                vec![17, 11, 10, 5, 4],
            ]
        );
        let unified: Vec<Vec<usize>> = terms
            .iter()
            .map(|term| unify_term_net(&net, term))
            .collect();
        assert_eq!(
            unified,
            [
                consts.clone(),
                vec![1, 11, 10, 5, 4],
                vec![2, 11, 10, 5, 4],
                vec![3, 11, 10, 5, 4],
                all.clone(),
                all.clone(),
                vec![6, 8, 11, 10, 5, 4],
                vec![7, 8, 11, 10, 5, 4],
                vec![13, 7, 6, 8, 11, 10, 5, 4],
                vec![9, 17, 11, 10, 5, 4],
                all.clone(),
                all,
                vec![12, 11, 10, 5, 4],
                vec![13, 8, 11, 10, 5, 4],
                consts.clone(),
                consts,
                vec![17, 16, 11, 10, 5, 4],
                vec![9, 17, 16, 11, 10, 5, 4],
            ]
        );
        let deleted = [6, 8, 4, 12, 99].iter().fold(net, |net, &item: &usize| {
            delete_term_safe(
                |left, right| left == right,
                &terms[item % terms.len()],
                &item,
                &net,
            )
        });
        let all = vec![9, 17, 16, 13, 7, 3, 2, 1, 15, 14, 0, 11, 10, 5];
        let consts = vec![15, 14, 0, 11, 10, 5];
        let unified: Vec<Vec<usize>> = terms
            .iter()
            .map(|term| unify_term_net(&deleted, term))
            .collect();
        assert_eq!(
            unified,
            [
                consts.clone(),
                vec![1, 11, 10, 5],
                vec![2, 11, 10, 5],
                vec![3, 11, 10, 5],
                all.clone(),
                all.clone(),
                vec![11, 10, 5],
                vec![7, 11, 10, 5],
                vec![13, 7, 11, 10, 5],
                vec![9, 17, 11, 10, 5],
                all.clone(),
                all,
                vec![11, 10, 5],
                vec![13, 11, 10, 5],
                consts.clone(),
                consts,
                vec![17, 16, 11, 10, 5],
                vec![9, 17, 16, 11, 10, 5],
            ]
        );
    }

    #[test]
    fn keys_terms_in_preorder() {
        let terms = sample_terms();
        let atom = |name: &str| NetKey::Atom(name.into());
        assert_eq!(
            key_of_term(&terms[16]),
            [
                NetKey::Comb,
                NetKey::Comb,
                atom("g"),
                NetKey::Var,
                atom(":000")
            ]
        );
        assert_eq!(
            key_of_term(&terms[17]),
            [
                NetKey::Comb,
                NetKey::Comb,
                atom("g"),
                atom("c"),
                NetKey::Var
            ]
        );
    }
}
