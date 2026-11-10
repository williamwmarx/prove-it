// Ported from Zenon's node.ml and heap.ml, as shipped in tlapm. Copyright 2001-2004 INRIA, see
// LICENSE.
//! Tableau nodes and the queue that orders them. The search keeps the queue of every open branch,
//! so the queue is persistent: inserting or removing returns a new queue and shares the rest.

use std::rc::Rc;

use crate::expr::{Expr, Kind};
use crate::proof::{Rule, RuleName};

#[derive(Clone, Debug)]
pub enum Priority {
    Prop,
    Arity,
    ArityEq,
    Instance(Expr),
}

#[derive(Debug)]
pub struct Node {
    pub conclusions: Vec<Expr>,
    pub rule: Rule,
    pub priority: Priority,
    pub goalness: i64,
    pub branches: Vec<Vec<Expr>>,
}

/// `makeNode`.
pub fn make_node(
    conclusions: Vec<Expr>,
    rule: Rule,
    priority: Priority,
    goalness: i64,
    branches: Vec<Vec<Expr>>,
) -> Rc<Node> {
    Rc::new(Node {
        conclusions,
        rule,
        priority,
        goalness,
        branches,
    })
}

struct Cons<T> {
    head: T,
    tail: List<T>,
}

/// A persistent list, as OCaml's.
pub struct List<T>(Option<Rc<Cons<T>>>);

impl<T> Clone for List<T> {
    fn clone(&self) -> Self {
        List(self.0.clone())
    }
}

/// Drops the cells one by one, since a branch's queue can hold millions of them.
impl<T> Drop for List<T> {
    fn drop(&mut self) {
        let mut cell = self.0.take();
        while let Some(shared) = cell {
            match Rc::try_unwrap(shared) {
                Ok(mut owned) => cell = owned.tail.0.take(),
                Err(_) => break,
            }
        }
    }
}

impl<T> Default for List<T> {
    fn default() -> Self {
        List(None)
    }
}

impl<T: Clone> List<T> {
    fn cons(head: T, tail: &List<T>) -> List<T> {
        List(Some(Rc::new(Cons {
            head,
            tail: tail.clone(),
        })))
    }

    fn is_empty(&self) -> bool {
        self.0.is_none()
    }

    fn head(&self) -> Option<&T> {
        self.0.as_ref().map(|cell| &cell.head)
    }

    fn split(&self) -> Option<(T, List<T>)> {
        self.0
            .as_ref()
            .map(|cell| (cell.head.clone(), cell.tail.clone()))
    }

    fn iter(&self) -> impl Iterator<Item = &T> {
        std::iter::successors(self.0.as_deref(), |cell| cell.tail.0.as_deref())
            .map(|cell| &cell.head)
    }

    fn reverse(&self) -> List<T> {
        self.iter().fold(List::default(), |result, item| {
            List::cons(item.clone(), &result)
        })
    }

    fn last(&self) -> Option<&T> {
        self.iter().last()
    }
}

/// A node in the instance heap, with the size of the term that instantiates its formula.
#[derive(Clone)]
struct Entry {
    node: Rc<Node>,
    size: i64,
}

struct Tree {
    entry: Entry,
    left: Option<Rc<Tree>>,
    right: Option<Rc<Tree>>,
}

/// Zenon's Heap: a persistent binary heap that alternates insertion paths.
#[derive(Clone, Default)]
struct Heap {
    tree: Option<Rc<Tree>>,
    path: u64,
}

const META_WEIGHT: i64 = 5;
const TAU_DIVISOR: i64 = 8;

fn get_instance_size(term: &Expr) -> i64 {
    term.size + term.metas.len() as i64 * META_WEIGHT + term.taus / TAU_DIVISOR
}

fn insert_tree(tree: &Option<Rc<Tree>>, entry: Entry, path: u64) -> Rc<Tree> {
    let Some(tree) = tree else {
        return Rc::new(Tree {
            entry,
            left: None,
            right: None,
        });
    };
    let is_smaller = entry.size < tree.entry.size;
    let (here, next) = if is_smaller {
        (entry, tree.entry.clone())
    } else {
        (tree.entry.clone(), entry)
    };
    let next_path = path / 2;
    Rc::new(if path.is_multiple_of(2) {
        Tree {
            entry: here,
            left: Some(insert_tree(&tree.left, next, next_path)),
            right: tree.right.clone(),
        }
    } else {
        Tree {
            entry: here,
            left: tree.left.clone(),
            right: Some(insert_tree(&tree.right, next, next_path)),
        }
    })
}

fn insert_heap(heap: &Heap, entry: Entry) -> Heap {
    Heap {
        tree: Some(insert_tree(&heap.tree, entry, heap.path)),
        path: heap.path + 1,
    }
}

fn remove_tree(tree: &Tree) -> (Entry, Option<Rc<Tree>>) {
    let (Some(left), Some(right)) = (&tree.left, &tree.right) else {
        return (
            tree.entry.clone(),
            tree.left.clone().or_else(|| tree.right.clone()),
        );
    };
    let is_left_first = left.entry.size < right.entry.size;
    let (first, second) = if is_left_first {
        (left, right)
    } else {
        (right, left)
    };
    let removed = remove_tree(first);
    (
        tree.entry.clone(),
        Some(Rc::new(Tree {
            entry: removed.0,
            left: removed.1,
            right: Some(second.clone()),
        })),
    )
}

fn remove_heap(heap: &Heap) -> Option<(Rc<Node>, Heap)> {
    let removed = remove_tree(heap.tree.as_ref()?);
    Some((
        removed.0.node,
        Heap {
            tree: removed.1,
            path: heap.path,
        },
    ))
}

type Sizes = List<(i64, Heap)>;

#[derive(Clone)]
pub struct Queue {
    prop1: List<Rc<Node>>,
    prop2: List<Rc<Node>>,
    unary: List<Rc<Node>>,
    binary: List<Rc<Node>>,
    nary: List<Rc<Node>>,
    eq_front: List<Rc<Node>>,
    eq_back: List<Rc<Node>>,
    eq_count: i64,
    inst_state: u64,
    inst_size: Sizes,
    inst_front: List<Rc<Node>>,
    inst_back: List<Rc<Node>>,
    /// The nodes inserted since the root. Removed nodes still count, because the queues of the
    /// branches above keep them.
    pub inserted_count: u64,
}

const SMALL_INSTANCES: u64 = 16;
const OLD_INSTANCES: u64 = 2;
const MAX_INSTANCES: u64 = SMALL_INSTANCES + OLD_INSTANCES;
const EQUALITY_COUNT: i64 = 10;

impl Default for Queue {
    /// `EMPTY_QUEUE`.
    fn default() -> Self {
        Queue {
            prop1: List::default(),
            prop2: List::default(),
            unary: List::default(),
            binary: List::default(),
            nary: List::default(),
            eq_front: List::default(),
            eq_back: List::default(),
            eq_count: EQUALITY_COUNT,
            inst_state: 0,
            inst_size: List::default(),
            inst_front: List::default(),
            inst_back: List::default(),
            inserted_count: 0,
        }
    }
}

fn insert_by_goalness(list: &Sizes, entry: Entry) -> Sizes {
    let goalness = entry.node.goalness;
    let heap = list
        .iter()
        .find(|cell| cell.0 == goalness)
        .map(|cell| cell.1.clone())
        .unwrap_or_default();
    let inserted = (goalness, insert_heap(&heap, entry));
    fn insert(rest: &Sizes, goalness: i64, inserted: (i64, Heap)) -> Sizes {
        match rest.split() {
            None => List::cons(inserted, &List::default()),
            Some((head, tail)) if head.0 == goalness => List::cons(inserted, &tail),
            Some((head, _)) if head.0 > goalness => List::cons(inserted, rest),
            Some((head, tail)) => List::cons(head, &insert(&tail, goalness, inserted)),
        }
    }
    insert(list, goalness, inserted)
}

fn can_instantiate(meta: &Expr, expression: &Expr) -> bool {
    match expression.kind {
        Kind::Var | Kind::True | Kind::False => true,
        Kind::Meta => !expression.args[0].metas.contains(meta),
        kind if kind.is_binder() => can_instantiate(meta, &expression.args[1]),
        _ => expression
            .args
            .iter()
            .all(|inner| can_instantiate(meta, inner)),
    }
}

/// `insertNode`.
pub fn insert_node(previous: &Queue, node: Rc<Node>) -> Queue {
    let mut queue = previous.clone();
    queue.inserted_count += 1;
    match node.priority {
        Priority::Prop => {
            if node.branches.len() < 2 {
                queue.prop1 = List::cons(node, &queue.prop1);
            } else {
                queue.prop2 = List::cons(node, &queue.prop2);
            }
        }
        Priority::Arity => match node.branches.len() {
            0 => queue.prop1 = List::cons(node, &queue.prop1),
            1 => queue.unary = List::cons(node, &queue.unary),
            2 => queue.binary = List::cons(node, &queue.binary),
            _ => queue.nary = List::cons(node, &queue.nary),
        },
        Priority::ArityEq => queue.eq_back = List::cons(node, &queue.eq_back),
        Priority::Instance(_) => {
            let rule = &node.rule;
            let quantified = match rule.name {
                RuleName::All => Some(&rule.args[0]),
                RuleName::NotEx if rule.args[0].kind == Kind::Not => Some(&rule.args[0].args[0]),
                _ => None,
            };
            if let Some(quantified) = quantified
                && can_instantiate(quantified, &rule.args[1])
            {
                let size = get_instance_size(&rule.args[1]);
                queue.inst_size = insert_by_goalness(
                    &queue.inst_size,
                    Entry {
                        node: node.clone(),
                        size,
                    },
                );
            }
            queue.inst_back = List::cons(node, &queue.inst_back);
        }
    }
    queue
}

fn remove_at(goalness: i64, list: &Sizes) -> Option<(Rc<Node>, Sizes)> {
    let (head, tail) = list.split()?;
    if head.0 < goalness {
        let removed = remove_at(goalness, &tail)?;
        return Some((removed.0, List::cons(head, &removed.1)));
    }
    match remove_heap(&head.1) {
        None => remove_at(goalness, &tail),
        Some(removed) => Some((removed.0, List::cons((head.0, removed.1), &tail))),
    }
}

/// On even states, the smallest instance of the most goal-directed formulas; on odd states, the
/// smallest instance overall.
fn remove_by_goalness(state: u64, list: &Sizes) -> Option<(Rc<Node>, Sizes)> {
    if state.is_multiple_of(2) {
        return remove_at(0, list);
    }
    let mut best = 0;
    let mut best_size: Option<i64> = None;
    for cell in list.iter() {
        if let Some(tree) = &cell.1.tree
            && best_size.is_none_or(|size| tree.entry.size < size)
        {
            best = cell.0;
            best_size = Some(tree.entry.size);
        }
    }
    remove_at(best, list)
}

fn is_empty_sizes(list: &Sizes) -> bool {
    list.iter().all(|cell| cell.1.tree.is_none())
}

fn remove_equality(queue: &Queue) -> Option<(Rc<Node>, Queue)> {
    if let Some((head, tail)) = queue.eq_front.split() {
        let mut queue = queue.clone();
        queue.eq_front = tail;
        return Some((head, queue));
    }
    let (head, tail) = queue.eq_back.reverse().split()?;
    let mut queue = queue.clone();
    queue.eq_front = tail;
    queue.eq_back = List::default();
    Some((head, queue))
}

fn remove_instance(queue: Queue) -> Option<(Rc<Node>, Queue)> {
    if queue.inst_state < SMALL_INSTANCES {
        if let Some(removed) = remove_by_goalness(queue.inst_state, &queue.inst_size) {
            let mut next = queue;
            next.inst_state += 1;
            next.inst_size = removed.1;
            return Some((removed.0, next));
        }
        let mut next = queue;
        next.inst_state = SMALL_INSTANCES;
        return remove_instance(next);
    }
    if let Some((head, tail)) = queue.inst_front.split() {
        let mut next = queue;
        next.inst_front = tail;
        next.inst_state = (next.inst_state + 1) % MAX_INSTANCES;
        return Some((head, next));
    }
    if queue.inst_back.is_empty() {
        if is_empty_sizes(&queue.inst_size) {
            return None;
        }
        let mut next = queue;
        next.inst_state = 0;
        return remove_instance(next);
    }
    let mut next = queue;
    next.inst_front = next.inst_back.reverse();
    next.inst_back = List::default();
    remove_instance(next)
}

/// `removeNode`: the next node to expand, and the queue without it.
pub fn remove_node(queue: &Queue) -> Option<(Rc<Node>, Queue)> {
    let take = |select: fn(&mut Queue) -> &mut List<Rc<Node>>| {
        let mut next = queue.clone();
        let (head, tail) = select(&mut next).split()?;
        *select(&mut next) = tail;
        Some((head, next))
    };
    if !queue.prop1.is_empty() {
        return take(|queue| &mut queue.prop1);
    }
    if !queue.prop2.is_empty() {
        return take(|queue| &mut queue.prop2);
    }
    if !queue.unary.is_empty() {
        return take(|queue| &mut queue.unary);
    }
    if !queue.binary.is_empty() {
        return take(|queue| &mut queue.binary);
    }
    if !queue.nary.is_empty() {
        return take(|queue| &mut queue.nary);
    }
    if queue.eq_count > 0 {
        let mut counted = queue.clone();
        counted.eq_count -= 1;
        return remove_equality(&counted).or_else(|| remove_instance(counted));
    }
    let mut reset = queue.clone();
    reset.eq_count = EQUALITY_COUNT;
    remove_instance(reset.clone()).or_else(|| remove_equality(&reset))
}

/// `getQueueHead`: the node [`remove_node`] would take first, ignoring the counters.
pub fn get_queue_head(queue: &Queue) -> Option<Rc<Node>> {
    queue
        .prop1
        .head()
        .or_else(|| queue.prop2.head())
        .or_else(|| queue.unary.head())
        .or_else(|| queue.binary.head())
        .or_else(|| queue.nary.head())
        .or_else(|| queue.eq_front.head())
        .or_else(|| queue.eq_back.last())
        .or_else(|| queue.inst_front.head())
        .or_else(|| queue.inst_back.last())
        .cloned()
}
