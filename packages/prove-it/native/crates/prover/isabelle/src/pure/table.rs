//! Ported from Isabelle2025's Pure/General/table.ML. Copyright (c) 1986-2025 University of
//! Cambridge, Technische Universitaet Muenchen, and contributors, see LICENSE.
//!
//! Persistent tables ordered by a comparison function. Isabelle's tables are 2-3 trees; any
//! balanced search tree visits keys in the same order, which is all that the ports rely on.
//! Updates share the untouched nodes, so cloning a table is cheap and leaves the original as it is.

use std::cmp::Ordering;
use std::rc::Rc;

use super::term::Name;

/// The TypeScript's `Compare`, whose callers only look at the sign of the result.
pub type Compare<Key> = fn(&Key, &Key) -> Ordering;

struct Node<Key, Value> {
    key: Key,
    value: Value,
    left: Link<Key, Value>,
    right: Link<Key, Value>,
    height: usize,
}

type Link<Key, Value> = Option<Rc<Node<Key, Value>>>;

pub struct Table<Key, Value> {
    compare: Compare<Key>,
    root: Link<Key, Value>,
}

impl<Key, Value> Clone for Table<Key, Value> {
    fn clone(&self) -> Self {
        Table {
            compare: self.compare,
            root: self.root.clone(),
        }
    }
}

fn get_height<Key, Value>(node: &Link<Key, Value>) -> usize {
    node.as_ref().map_or(0, |node| node.height)
}

fn make_node<Key, Value>(
    key: Key,
    value: Value,
    left: Link<Key, Value>,
    right: Link<Key, Value>,
) -> Link<Key, Value> {
    let height = get_height(&left).max(get_height(&right)) + 1;
    Some(Rc::new(Node {
        key,
        value,
        left,
        right,
        height,
    }))
}

fn balance<Key: Clone, Value: Clone>(
    key: Key,
    value: Value,
    left: Link<Key, Value>,
    right: Link<Key, Value>,
) -> Link<Key, Value> {
    let left_height = get_height(&left);
    let right_height = get_height(&right);
    if left_height > right_height + 1
        && let Some(left) = &left
    {
        if get_height(&left.left) >= get_height(&left.right) {
            return make_node(
                left.key.clone(),
                left.value.clone(),
                left.left.clone(),
                make_node(key, value, left.right.clone(), right),
            );
        }
        let Some(middle) = &left.right else {
            return make_node(key, value, Some(left.clone()), right);
        };
        return make_node(
            middle.key.clone(),
            middle.value.clone(),
            make_node(
                left.key.clone(),
                left.value.clone(),
                left.left.clone(),
                middle.left.clone(),
            ),
            make_node(key, value, middle.right.clone(), right),
        );
    }
    if right_height > left_height + 1
        && let Some(right) = &right
    {
        if get_height(&right.right) >= get_height(&right.left) {
            return make_node(
                right.key.clone(),
                right.value.clone(),
                make_node(key, value, left, right.left.clone()),
                right.right.clone(),
            );
        }
        let Some(middle) = &right.left else {
            return make_node(key, value, left, Some(right.clone()));
        };
        return make_node(
            middle.key.clone(),
            middle.value.clone(),
            make_node(key, value, left, middle.left.clone()),
            make_node(
                right.key.clone(),
                right.value.clone(),
                middle.right.clone(),
                right.right.clone(),
            ),
        );
    }
    make_node(key, value, left, right)
}

pub fn empty_table<Key, Value>(compare: Compare<Key>) -> Table<Key, Value> {
    Table {
        compare,
        root: None,
    }
}

pub fn is_empty_table<Key, Value>(table: &Table<Key, Value>) -> bool {
    table.root.is_none()
}

pub fn lookup_table<'table, Key, Value>(
    table: &'table Table<Key, Value>,
    key: &Key,
) -> Option<&'table Value> {
    let mut node = &table.root;
    while let Some(current) = node {
        match (table.compare)(key, &current.key) {
            Ordering::Equal => return Some(&current.value),
            Ordering::Less => node = &current.left,
            Ordering::Greater => node = &current.right,
        }
    }
    None
}

pub fn has_key<Key, Value>(table: &Table<Key, Value>, key: &Key) -> bool {
    lookup_table(table, key).is_some()
}

fn insert_node<Key: Clone, Value: Clone>(
    compare: Compare<Key>,
    key: Key,
    value: Value,
    node: &Link<Key, Value>,
) -> Link<Key, Value> {
    let Some(node) = node else {
        return make_node(key, value, None, None);
    };
    match compare(&key, &node.key) {
        Ordering::Equal => make_node(key, value, node.left.clone(), node.right.clone()),
        Ordering::Less => balance(
            node.key.clone(),
            node.value.clone(),
            insert_node(compare, key, value, &node.left),
            node.right.clone(),
        ),
        Ordering::Greater => balance(
            node.key.clone(),
            node.value.clone(),
            node.left.clone(),
            insert_node(compare, key, value, &node.right),
        ),
    }
}

pub fn update_table<Key: Clone, Value: Clone>(
    table: &Table<Key, Value>,
    key: Key,
    value: Value,
) -> Table<Key, Value> {
    Table {
        compare: table.compare,
        root: insert_node(table.compare, key, value, &table.root),
    }
}

/// The least node of a tree and the rest of it.
fn remove_min<Key: Clone, Value: Clone>(
    node: &Rc<Node<Key, Value>>,
) -> (Rc<Node<Key, Value>>, Link<Key, Value>) {
    let Some(left) = &node.left else {
        return (node.clone(), node.right.clone());
    };
    let (minimum, left) = remove_min(left);
    (
        minimum,
        balance(
            node.key.clone(),
            node.value.clone(),
            left,
            node.right.clone(),
        ),
    )
}

pub fn delete_table<Key: Clone, Value: Clone>(
    table: &Table<Key, Value>,
    key: &Key,
) -> Table<Key, Value> {
    fn remove<Key: Clone, Value: Clone>(
        compare: Compare<Key>,
        key: &Key,
        node: &Link<Key, Value>,
    ) -> Link<Key, Value> {
        let node = node.as_ref()?;
        match compare(key, &node.key) {
            Ordering::Less => balance(
                node.key.clone(),
                node.value.clone(),
                remove(compare, key, &node.left),
                node.right.clone(),
            ),
            Ordering::Greater => balance(
                node.key.clone(),
                node.value.clone(),
                node.left.clone(),
                remove(compare, key, &node.right),
            ),
            Ordering::Equal => {
                let Some(right) = &node.right else {
                    return node.left.clone();
                };
                let (minimum, right) = remove_min(right);
                balance(
                    minimum.key.clone(),
                    minimum.value.clone(),
                    node.left.clone(),
                    right,
                )
            }
        }
    }
    Table {
        compare: table.compare,
        root: remove(table.compare, key, &table.root),
    }
}

pub fn min_table<Key, Value>(table: &Table<Key, Value>) -> Option<(&Key, &Value)> {
    let mut node = table.root.as_ref()?;
    while let Some(left) = &node.left {
        node = left;
    }
    Some((&node.key, &node.value))
}

fn fold_node<Key, Value, State>(
    visit: &mut impl FnMut(&Key, &Value, State) -> State,
    node: &Link<Key, Value>,
    state: State,
) -> State {
    match node {
        None => state,
        Some(node) => {
            let state = fold_node(visit, &node.left, state);
            let state = visit(&node.key, &node.value, state);
            fold_node(visit, &node.right, state)
        }
    }
}

/// Table.fold: visits the entries in key order.
pub fn fold_table<Key, Value, State>(
    mut visit: impl FnMut(&Key, &Value, State) -> State,
    table: &Table<Key, Value>,
    state: State,
) -> State {
    fold_node(&mut visit, &table.root, state)
}

/// The entries in key order, as Table.dest lists them.
pub fn table_entries<Key: Clone, Value: Clone>(table: &Table<Key, Value>) -> Vec<(Key, Value)> {
    fold_table(
        |key, value, mut entries: Vec<(Key, Value)>| {
            entries.push((key.clone(), value.clone()));
            entries
        },
        table,
        Vec::new(),
    )
}

/// fast_string_ord: shorter strings first, then by code units.
pub fn fast_string_ord(left: &Name, right: &Name) -> Ordering {
    left.len()
        .cmp(&right.len())
        .then_with(|| left.as_bytes().cmp(right.as_bytes()))
}

fn string_ord(left: &str, right: &str) -> Ordering {
    left.as_bytes().cmp(right.as_bytes())
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IndexKey {
    pub name: Name,
    pub index: i32,
}

/// Term_Ord.fast_indexname_ord: by index, then by fast_string_ord on the name.
pub fn fast_indexname_ord(left: &IndexKey, right: &IndexKey) -> Ordering {
    left.index
        .cmp(&right.index)
        .then_with(|| fast_string_ord(&left.name, &right.name))
}

/// Term_Ord.indexname_ord: by index, then by string_ord on the name.
pub fn indexname_ord(left: &IndexKey, right: &IndexKey) -> Ordering {
    left.index
        .cmp(&right.index)
        .then_with(|| string_ord(&left.name, &right.name))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn name(text: &str) -> Name {
        text.into()
    }

    fn keys(table: &Table<Name, i32>) -> Vec<String> {
        table_entries(table)
            .into_iter()
            .map(|(key, value)| format!("{key}={value}"))
            .collect()
    }

    // Expected values from running table.ts with bun.
    #[test]
    fn orders_by_fast_string_ord_and_deletes() {
        let words = ["b", "aa", "a", "ccc", "ab", "c", "ba", "a", "zz", "d"];
        let table = words
            .iter()
            .enumerate()
            .fold(empty_table(fast_string_ord), |table, (index, word)| {
                update_table(&table, name(word), index as i32)
            });
        assert_eq!(
            keys(&table),
            [
                "a=7", "b=0", "c=5", "d=9", "aa=1", "ab=4", "ba=6", "zz=8", "ccc=3"
            ]
        );
        let deleted = ["ab", "a", "q", "ccc"]
            .iter()
            .fold(table.clone(), |table, word| {
                delete_table(&table, &name(word))
            });
        assert_eq!(
            keys(&deleted),
            ["b=0", "c=5", "d=9", "aa=1", "ba=6", "zz=8"]
        );
        assert_eq!(lookup_table(&table, &name("ab")), Some(&4));
        assert_eq!(lookup_table(&deleted, &name("ab")), None);
        assert_eq!(
            min_table(&deleted).map(|(key, _)| key.to_string()),
            Some("b".into())
        );
    }

    #[test]
    fn stays_balanced() {
        let table = (0..1000).fold(
            empty_table(|left: &i32, right: &i32| left.cmp(right)),
            |table, key| update_table(&table, key, ()),
        );
        assert!(get_height(&table.root) <= 15);
        let table = (0..1000)
            .step_by(2)
            .fold(table, |table, key| delete_table(&table, &key));
        assert_eq!(
            table_entries(&table)
                .into_iter()
                .map(|(key, _)| key)
                .collect::<Vec<_>>(),
            (1..1000).step_by(2).collect::<Vec<_>>()
        );
    }

    #[test]
    fn orders_indexnames() {
        let key = |text: &str, index| IndexKey {
            name: name(text),
            index,
        };
        assert_eq!(
            fast_indexname_ord(&key("b", 0), &key("aa", 0)),
            Ordering::Less
        );
        assert_eq!(
            indexname_ord(&key("b", 0), &key("aa", 0)),
            Ordering::Greater
        );
        assert_eq!(indexname_ord(&key("z", 0), &key("a", 1)), Ordering::Less);
    }
}
