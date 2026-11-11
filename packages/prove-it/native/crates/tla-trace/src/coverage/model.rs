//! TLC's cost model (`tlc2.tool.coverage`): a tree of wrappers of SANY's `OpApplNode`s for each
//! action, invariant and constraint, as `CostModelCreator` walks the semantic graph from it, with
//! the counts `Tool` adds as it evaluates, and the report `CostModelCreator.report` prints.

use std::collections::{HashMap, HashSet};

use tla_engine::coverage::{SanyKind, Tree, Wrapper};
use tla_ir::SourceRange;

use super::FastMap;
use super::sem::{Code, DefId, Op, SId, SKind, Sem};
use crate::Unsupported;

pub(crate) use tla_engine::coverage::{Cm, NO_CM};

/// A node's location, as TLC's wrappers compare them.
pub(crate) type Place = (u32, i32, i32, i32, i32);

pub(crate) fn place(range: SourceRange) -> Place {
    (
        range.module,
        range.start_line,
        range.start_column,
        range.end_line,
        range.end_column,
    )
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Relation {
    Init,
    Next,
    Prop,
    Constraint,
}

/// What a root (`ActionWrapper`) reports itself as.
pub(crate) struct Root {
    pub relation: Relation,
    /// `printLocation`: `<Name declaration>`, or with the action's place where its definition's
    /// body isn't the action.
    pub label: String,
}

/// The cost model: the engine's tree of wrappers, which the engine's search counts into too, with
/// the counts the port adds as it evaluates.
pub(crate) struct Model {
    pub tree: Tree,
    pub counts: Vec<u64>,
    pub secondary: Vec<u64>,
    pub labels: FastMap<Cm, Root>,
    /// The lookups that failed, which TLC reports (`TLC_COVERAGE_MISMATCH`).
    pub mismatch: Option<String>,
}

/// What the cost model's lookup asks of a node.
pub(crate) fn kind_of(sem: &Sem, node: SId) -> SanyKind {
    match &sem.node(node).kind {
        SKind::Appl { .. } => SanyKind::Appl,
        SKind::Let { body, .. } => SanyKind::Let(*body),
        _ => SanyKind::Other,
    }
}

impl Model {
    pub fn new() -> Model {
        Model {
            tree: Tree::default(),
            counts: Vec::new(),
            secondary: Vec::new(),
            labels: FastMap::default(),
            mismatch: None,
        }
    }

    fn add(&mut self, node: Option<SId>, root: Cm) -> Cm {
        self.counts.push(0);
        self.secondary.push(0);
        self.tree.add(node, root)
    }

    fn wrapper(&mut self, cm: Cm) -> &mut Wrapper {
        &mut self.tree.wrappers[cm as usize]
    }

    /// `CostModel.get`: the wrapper of `node` under `cm`, or `cm` where TLC's lookup fails.
    pub fn get(&mut self, cm: Cm, node: SId, sem: &Sem) -> Cm {
        self.tree
            .get(cm, node, kind_of(sem, node))
            .unwrap_or_else(|cm| {
                self.mismatch.get_or_insert_with(|| {
                    format!("a lookup of the cost model TLC fails, at {node}")
                });
                cm
            })
    }

    pub fn increment(&mut self, cm: Cm) {
        if cm != NO_CM {
            self.counts[cm as usize] += 1;
        }
    }

    pub fn add_count(&mut self, cm: Cm, count: u64) {
        if cm != NO_CM {
            self.counts[cm as usize] += count;
        }
    }

    pub fn add_secondary(&mut self, cm: Cm, count: u64) {
        if cm != NO_CM {
            self.secondary[cm as usize] += count;
        }
    }

    pub fn root_of(&self, cm: Cm) -> Cm {
        self.tree.root_of(cm)
    }
}

/// `CostModelCreator`: builds the tree of a root, walking the semantic graph from `pred`.
pub(crate) struct Creator<'m, 's, 'ir> {
    pub model: &'m mut Model,
    pub sem: &'s Sem<'ir>,
    /// The locations of the primed nodes (`getPrimedLocs`), which mark a wrapper primed.
    pub primed: &'s HashSet<Place>,
    /// The nodes standing for a LET's definitions, which set the LET's body's lets.
    lets: HashMap<SId, SId>,
    stack: Vec<Cm>,
    root: Cm,
    is_substitution: bool,
    /// The RECURSIVE definitions being walked, which the walk doesn't enter again
    /// (`CoverageHashTable`).
    walking: Vec<DefId>,
}

impl<'m, 's, 'ir> Creator<'m, 's, 'ir> {
    /// The tree of a root, with its label.
    pub fn create(
        model: &'m mut Model,
        sem: &'s Sem<'ir>,
        primed: &'s HashSet<Place>,
        pred: SId,
        label: Root,
    ) -> Result<Cm, Unsupported> {
        let root = model.add(None, 0);
        model.wrapper(root).root = root;
        model.labels.insert(root, label);
        let mut creator = Creator {
            model,
            sem,
            primed,
            lets: HashMap::new(),
            stack: vec![root],
            root,
            is_substitution: false,
            walking: Vec::new(),
        };
        creator.walk(pred)?;
        Ok(root)
    }

    fn walk(&mut self, id: SId) -> Result<(), Unsupported> {
        match &self.sem.node(id).kind {
            SKind::Num(_) | SKind::Str(_) | SKind::At => Ok(()),
            SKind::Let { defs, body } => {
                for &def in defs {
                    let def_body = self.sem.def(def).body.expect("a translated definition");
                    self.lets.insert(def_body, *body);
                }
                // SANY walks a LET's definitions from its context, a Hashtable, in that order.
                for def in hashtable_order(self.sem, defs) {
                    self.walk_def(def)?;
                }
                self.walk(*body)
            }
            SKind::Appl { .. } => self.walk_appl(id),
        }
    }

    fn walk_def(&mut self, def: DefId) -> Result<(), Unsupported> {
        let is_recursive = self.sem.def(def).is_recursive;
        if is_recursive && self.walking.contains(&def) {
            return Ok(());
        }
        if is_recursive {
            self.walking.push(def);
        }
        let body = self.sem.def(def).body.expect("a translated definition");
        let result = self.walk(body);
        if is_recursive {
            self.walking.pop();
        }
        result
    }

    fn walk_appl(&mut self, id: SId) -> Result<(), Unsupported> {
        let SKind::Appl {
            op, args, bounds, ..
        } = &self.sem.node(id).kind
        else {
            unreachable!("an application")
        };
        let range = self.sem.node(id).range;
        let is_standard =
            range.is_some_and(|range| is_standard_module(self.sem.text(range.module)));
        if is_standard {
            return Err(Unsupported("a node of a standard module".into()));
        }
        let wrapper = self.model.add(Some(id), self.root);
        self.model.wrapper(wrapper).is_unchanged = *op == Op::Code(Code::Unchanged);
        if !self.is_substitution && range.is_some_and(|range| self.primed.contains(&place(range))) {
            self.model.wrapper(wrapper).is_primed = true;
        }
        // The body of a LET's definition: the LET's body's wrappers on the stack take it.
        if let Some(&in_body) = self.lets.get(&id) {
            for &on_stack in &self.stack {
                if self.model.tree.wrappers[on_stack as usize].node == Some(in_body) {
                    let lets = &mut self.model.wrapper(on_stack).lets;
                    match lets.iter_mut().find(|(key, _)| *key == id) {
                        Some(entry) => entry.1 = wrapper,
                        None => lets.push((id, wrapper)),
                    }
                }
            }
        }
        // A declared constant the configuration replaces with a definition: TLC evaluates the
        // definition's body, a tree of its own.
        if let Op::Substituted(def) = op {
            let body = self.sem.def(*def).body.expect("a translated definition");
            let mut substitution = Creator {
                model: &mut *self.model,
                sem: self.sem,
                primed: self.primed,
                lets: HashMap::new(),
                stack: Vec::new(),
                root: self.root,
                is_substitution: true,
                walking: Vec::new(),
            };
            let dummy = substitution.model.add(None, self.root);
            substitution.stack.push(dummy);
            substitution.walk(body)?;
            let children = &self.model.tree.wrappers[dummy as usize].children;
            let Some(&(key, child)) = children.first().filter(|_| children.len() == 1) else {
                return Err(Unsupported(
                    "a constant replaced by a definition whose body is no application".into(),
                ));
            };
            self.model.tree.add_child(wrapper, key, child);
        }
        // An application of a RECURSIVE operator looks up what it doesn't find under the
        // nearest application of the same operator on the stack.
        if let Op::Def(def) = op
            && self.sem.def(*def).is_recursive
        {
            let recursive = self.stack.iter().rev().copied().find(|&on_stack| {
                self.model.tree.wrappers[on_stack as usize].node.is_some_and(|node| {
                    matches!(&self.sem.node(node).kind, SKind::Appl { op: Op::Def(other), .. } if other == def)
                })
            });
            self.model.wrapper(wrapper).recursive = recursive;
        }
        let parent = *self.stack.last().expect("a parent");
        self.model.tree.add_child(parent, id, wrapper);
        self.stack.push(wrapper);
        // The operator, then the operands, then the bounds' sets.
        if let Op::Def(def) = op {
            self.walk_def(*def)?;
        }
        for arg in args.iter().flatten() {
            self.walk(*arg)?;
        }
        for bound in bounds {
            self.walk(bound.set)?;
        }
        self.stack.pop();
        Ok(())
    }
}

/// `StandardModules`: the modules whose nodes the cost model leaves out.
pub(crate) fn is_standard_module(module: &str) -> bool {
    matches!(
        module,
        "FiniteSets"
            | "Sequences"
            | "Bags"
            | "Naturals"
            | "Integers"
            | "Reals"
            | "RealTime"
            | "Randomization"
            | "TLC"
    )
}

/// The order a `java.util.Hashtable` of the names enumerates them in, as SANY's `Context` holds a
/// LET's definitions: by bucket from the last, each bucket newest first.
fn hashtable_order(sem: &Sem, defs: &[DefId]) -> Vec<DefId> {
    let mut capacity = 11usize;
    let mut table: Vec<Vec<(i32, DefId)>> = vec![Vec::new(); capacity];
    for (count, &def) in defs.iter().enumerate() {
        let hash = java_hash(sem.text(sem.def(def).name));
        // A name defined twice replaces the first, which SANY rejects anyway.
        if count as f64 >= capacity as f64 * 0.75 {
            let new_capacity = capacity * 2 + 1;
            let mut new_table: Vec<Vec<(i32, DefId)>> = vec![Vec::new(); new_capacity];
            for bucket in table.iter().rev() {
                for &(hash, def) in bucket {
                    let index = (hash & 0x7fff_ffff) as usize % new_capacity;
                    new_table[index].insert(0, (hash, def));
                }
            }
            table = new_table;
            capacity = new_capacity;
        }
        let index = (hash & 0x7fff_ffff) as usize % capacity;
        table[index].insert(0, (hash, def));
    }
    table
        .iter()
        .rev()
        .flat_map(|bucket| bucket.iter().map(|&(_, def)| def))
        .collect()
}

/// `String.hashCode`.
pub(crate) fn java_hash(text: &str) -> i32 {
    text.encode_utf16().fold(0i32, |hash, unit| {
        hash.wrapping_mul(31).wrapping_add(i32::from(unit))
    })
}

// --- the report ---

/// A line of the report: its message code and text.
pub(crate) type Line = (u32, String);

pub(crate) fn describe(sem: &Sem, range: Option<SourceRange>) -> String {
    match range {
        Some(range) => format!(
            "line {}, col {} to line {}, col {} of module {}",
            range.start_line,
            range.start_column,
            range.end_line,
            range.end_column,
            sem.text(range.module)
        ),
        None => "line 0, col 0 to line 0, col 0 of module ".into(),
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Pair {
    primary: u64,
    secondary: u64,
}

impl Pair {
    fn is_zero(self) -> bool {
        self.primary == 0 && self.secondary == 0
    }

    // `Objects.hash(primary, secondary)`.
    fn hash(self) -> i32 {
        let long = |value: u64| (value ^ (value >> 32)) as i32;
        31i32
            .wrapping_add(long(self.primary))
            .wrapping_mul(31)
            .wrapping_add(long(self.secondary))
    }
}

/// A `java.util.HashSet` of pairs, which keeps the order Java iterates them in: by bucket, each
/// bucket in the order its pairs came.
struct JavaSet {
    buckets: Vec<Vec<Pair>>,
    size: usize,
}

impl JavaSet {
    fn new() -> JavaSet {
        JavaSet {
            buckets: vec![Vec::new(); 16],
            size: 0,
        }
    }

    fn index(pair: Pair, capacity: usize) -> usize {
        let hash = pair.hash() as u32;
        ((hash ^ (hash >> 16)) as usize) & (capacity - 1)
    }

    fn insert(&mut self, pair: Pair) {
        let index = JavaSet::index(pair, self.buckets.len());
        if self.buckets[index].contains(&pair) {
            return;
        }
        self.buckets[index].push(pair);
        self.size += 1;
        if self.size > self.buckets.len() * 3 / 4 {
            let capacity = self.buckets.len() * 2;
            let mut buckets = vec![Vec::new(); capacity];
            for bucket in &self.buckets {
                for &pair in bucket {
                    buckets[JavaSet::index(pair, capacity)].push(pair);
                }
            }
            self.buckets = buckets;
        }
    }

    fn iter(&self) -> impl Iterator<Item = Pair> + '_ {
        self.buckets.iter().flatten().copied()
    }

    fn len(&self) -> usize {
        self.size
    }

    fn remove(&mut self, pair: Pair) {
        for bucket in &mut self.buckets {
            if let Some(position) = bucket.iter().position(|&held| held == pair) {
                bucket.remove(position);
                self.size -= 1;
            }
        }
    }
}

pub(crate) struct Printer<'m, 's, 'ir> {
    pub tree: &'m Tree,
    pub counts: &'m [u64],
    pub secondary: &'m [u64],
    pub labels: &'m FastMap<Cm, Root>,
    pub sem: &'s Sem<'ir>,
    pub lines: Vec<Line>,
    /// Whether a line names an expression the IR holds without a place, which SANY has.
    pub is_unplaced: bool,
}

impl Printer<'_, '_, '_> {
    /// `ActionWrapper.report`.
    pub fn report_root(&mut self, root: Cm) {
        let node = &self.tree.wrappers[root as usize];
        let label = &self.labels[&root];
        let (count, secondary) = (self.counts[root as usize], self.secondary[root as usize]);
        self.lines.push(match label.relation {
            Relation::Prop => (2774, label.label.clone()),
            Relation::Init => (
                2773,
                format!("{}: {}:{}", label.label, count, count + secondary),
            ),
            Relation::Constraint => (
                2778,
                format!("{}: {}:{}", label.label, secondary, count + secondary),
            ),
            Relation::Next => (2772, format!("{}: {}:{}", label.label, secondary, count)),
        });
        for &(_, child) in &node.children {
            self.print(child, 0);
        }
    }

    fn pair(&self, cm: Cm) -> Pair {
        Pair {
            primary: self.counts[cm as usize],
            secondary: self.secondary[cm as usize],
        }
    }

    // `collectAndFreezeEvalCounts`, at the end of the run, where the counts no longer change: the
    // node's own counts and its children's, each child's set added in its own order.
    fn collect(&self, cm: Cm) -> JavaSet {
        let node = &self.tree.wrappers[cm as usize];
        let own = self.pair(cm);
        let mut result = JavaSet::new();
        if !own.is_zero() || node.is_primed || node.is_unchanged {
            result.insert(own);
        }
        for &(_, child) in &node.children {
            for pair in self.collect(child).iter() {
                result.insert(pair);
            }
        }
        result
    }

    fn collect_children(&self, cm: Cm) -> JavaSet {
        let mut result = JavaSet::new();
        for &(_, child) in &self.tree.wrappers[cm as usize].children {
            for pair in self.collect(child).iter() {
                result.insert(pair);
            }
        }
        result
    }

    fn print_line(&mut self, cm: Cm, level: usize, pair: Pair) {
        let range = self.tree.wrappers[cm as usize]
            .node
            .and_then(|node| self.sem.node(node).range);
        self.is_unplaced |= range.is_none();
        let place = format!("{}{}", "|".repeat(level), describe(self.sem, range));
        self.lines.push(if pair.secondary > 0 {
            (
                2775,
                format!("  {place}: {}:{}", pair.primary, pair.secondary),
            )
        } else {
            (2221, format!("  {place}: {}", pair.primary))
        });
    }

    fn print_self(&mut self, cm: Cm, level: usize) {
        let pair = self.pair(cm);
        self.print_line(cm, level, pair);
    }

    // `printSelf(level, count)`: the count alone, whatever the secondary.
    fn print_count(&mut self, cm: Cm, level: usize, count: u64) {
        self.print_line(
            cm,
            level,
            Pair {
                primary: count,
                secondary: 0,
            },
        );
    }

    fn print_children(&mut self, cm: Cm, level: usize) {
        let children: Vec<Cm> = self.tree.wrappers[cm as usize]
            .children
            .iter()
            .map(|&(_, child)| child)
            .collect();
        for child in children {
            self.print(child, level);
        }
    }

    /// `OpApplNodeWrapper.print`, and `UnchangedOpApplNodeWrapper.print`.
    fn print(&mut self, cm: Cm, level: usize) {
        let node = &self.tree.wrappers[cm as usize];
        let is_primed = node.is_primed || node.is_unchanged;
        let mut collected = self.collect_children(cm);
        if node.is_unchanged {
            collected.remove(Pair {
                primary: 0,
                secondary: 0,
            });
            match collected.iter().next() {
                None => self.print_self(cm, level),
                Some(first) => {
                    let count = self.counts[cm as usize].max(first.primary);
                    self.print_count(cm, level, count);
                }
            }
            return;
        }
        let own = self.pair(cm);
        if collected.len() == 0 {
            if own.primary == 0 && !is_primed {
                return;
            }
            self.print_self(cm, level);
            return;
        }
        if collected.len() == 1 {
            let children = collected.iter().next().expect("one");
            if children.primary < own.primary {
                self.print_self(cm, level);
                self.print_children(cm, level + 1);
                return;
            }
            if !is_primed && own.is_zero() && !children.is_zero() {
                self.print_line(cm, level, children);
                return;
            }
            if own.is_zero() && children.is_zero() {
                let mut level = level;
                if is_primed {
                    self.print_self(cm, level);
                    level += 1;
                }
                self.print_children(cm, level);
                return;
            }
            if own == children {
                self.print_self(cm, level);
                return;
            }
        }
        let mut level = level;
        if !own.is_zero() || is_primed {
            self.print_self(cm, level);
            level += 1;
        }
        self.print_children(cm, level);
    }
}
