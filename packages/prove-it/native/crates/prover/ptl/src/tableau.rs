//! Decides satisfiability of propositional linear temporal logic over infinite traces, the logic LS4
//! decides: `ptl/tableau.ts`. A tableau node is the set of formulas that must hold now. A SAT call
//! per step picks the atoms and the formulas the next node must hold, and the formula is
//! satisfiable when a reachable strongly connected component can fulfill every eventuality it
//! postpones.

use std::collections::HashMap;

use prove_decide::Verdict;

use crate::sat::{Solution, Solver};

/// A formula as LS4's input writes it, each node at an index of `Formulas`.
#[derive(Clone, Copy, Debug)]
pub enum Formula {
    Atom(usize),
    Not(usize),
    Next(usize),
    Always(usize),
    Eventually(usize),
    And(usize, usize),
    Or(usize, usize),
    Implies(usize, usize),
    Equiv(usize, usize),
}

/// A parsed formula: its nodes, its atoms' names, and the node at its root.
pub struct Formulas {
    pub nodes: Vec<Formula>,
    pub atoms: Vec<String>,
    pub root: usize,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Junction {
    And,
    Or,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Modal {
    Next,
    Always,
    Eventually,
}

/// Formulas in negation normal form, numbered so that equal formulas share a number.
enum Normal {
    Constant(bool),
    Literal { atom: usize, is_positive: bool },
    Junction(Junction, Vec<usize>),
    Modal(Modal, usize),
}

#[derive(Default)]
struct Table {
    normals: Vec<Normal>,
    numbers: HashMap<String, usize>,
}

impl Table {
    fn intern(&mut self, key: String, normal: Normal) -> usize {
        if let Some(&existing) = self.numbers.get(&key) {
            return existing;
        }
        self.numbers.insert(key, self.normals.len());
        self.normals.push(normal);
        self.normals.len() - 1
    }

    fn get_constant(&mut self, value: bool) -> usize {
        self.intern(value.to_string(), Normal::Constant(value))
    }

    fn get_junction(&mut self, kind: Junction, operands: &[usize]) -> usize {
        let absorbing = kind == Junction::Or;
        let mut children: Vec<usize> = Vec::new();
        let mut add = |child: usize| {
            if !children.contains(&child) {
                children.push(child);
            }
        };
        for &operand in operands {
            match &self.normals[operand] {
                Normal::Constant(value) => {
                    if *value == absorbing {
                        return operand;
                    }
                }
                Normal::Junction(inner, grandchildren) if *inner == kind => {
                    grandchildren.iter().for_each(|&child| add(child));
                }
                _ => add(operand),
            }
        }
        children.sort();
        match children.len() {
            0 => self.get_constant(!absorbing),
            1 => children[0],
            _ => {
                let name = if kind == Junction::And { "And" } else { "Or" };
                let numbers: Vec<String> = children.iter().map(usize::to_string).collect();
                let key = format!("{name}({})", numbers.join(","));
                self.intern(key, Normal::Junction(kind, children))
            }
        }
    }

    fn get_modal(&mut self, kind: Modal, body: usize) -> usize {
        match self.normals[body] {
            Normal::Constant(_) => return body,
            Normal::Modal(inner, _) if kind != Modal::Next && inner == kind => return body,
            _ => {}
        }
        let name = match kind {
            Modal::Next => "Next",
            Modal::Always => "Always",
            Modal::Eventually => "Eventually",
        };
        self.intern(format!("{name}({body})"), Normal::Modal(kind, body))
    }
}

struct Normalizer<'a> {
    formulas: &'a Formulas,
    table: Table,
    /// The number of each node, by whether it is negated, once normalized.
    memo: [Vec<Option<usize>>; 2],
}

impl Normalizer<'_> {
    fn normalize(&mut self, node: usize, is_negated: bool) -> usize {
        if let Some(cached) = self.memo[usize::from(is_negated)][node] {
            return cached;
        }
        let junction = |is_and: bool| {
            if is_and { Junction::And } else { Junction::Or }
        };
        let result = match self.formulas.nodes[node] {
            Formula::Atom(atom) => {
                let sign = if is_negated { "-" } else { "+" };
                let key = format!("{sign}{}", self.formulas.atoms[atom]);
                let normal = Normal::Literal {
                    atom,
                    is_positive: !is_negated,
                };
                self.table.intern(key, normal)
            }
            Formula::Not(body) => self.normalize(body, !is_negated),
            Formula::Next(body) => {
                let body = self.normalize(body, is_negated);
                self.table.get_modal(Modal::Next, body)
            }
            Formula::Always(body) | Formula::Eventually(body) => {
                let is_always = matches!(self.formulas.nodes[node], Formula::Always(_));
                let kind = if is_always == is_negated {
                    Modal::Eventually
                } else {
                    Modal::Always
                };
                let body = self.normalize(body, is_negated);
                self.table.get_modal(kind, body)
            }
            Formula::And(left, right) | Formula::Or(left, right) => {
                let is_and = matches!(self.formulas.nodes[node], Formula::And(..));
                let left = self.normalize(left, is_negated);
                let right = self.normalize(right, is_negated);
                self.table
                    .get_junction(junction(is_and != is_negated), &[left, right])
            }
            Formula::Implies(left, right) => {
                let left = self.normalize(left, !is_negated);
                let right = self.normalize(right, is_negated);
                self.table
                    .get_junction(junction(is_negated), &[left, right])
            }
            Formula::Equiv(left, right) => {
                let first_left = self.normalize(left, !is_negated);
                let first_right = self.normalize(right, is_negated);
                let first = self
                    .table
                    .get_junction(junction(is_negated), &[first_left, first_right]);
                let second_left = self.normalize(left, is_negated);
                let second_right = self.normalize(right, !is_negated);
                let second = self
                    .table
                    .get_junction(junction(is_negated), &[second_left, second_right]);
                self.table
                    .get_junction(junction(!is_negated), &[first, second])
            }
        };
        self.memo[usize::from(is_negated)][node] = Some(result);
        result
    }
}

/// A way to satisfy a node's formulas now: the formulas the next node must hold, and the
/// eventualities left pending.
struct Step {
    next: Vec<usize>,
    pending: Vec<usize>,
}

struct Edge {
    target: usize,
    pending: Vec<usize>,
}

/// Variables by key, in the order they were made, as a JavaScript `Map` iterates.
#[derive(Default)]
struct Variables {
    entries: Vec<(usize, i32)>,
    positions: HashMap<usize, usize>,
}

impl Variables {
    fn get(&mut self, key: usize, counter: &mut i32) -> i32 {
        if let Some(&position) = self.positions.get(&key) {
            return self.entries[position].1;
        }
        *counter += 1;
        self.positions.insert(key, self.entries.len());
        self.entries.push((key, *counter));
        *counter
    }
}

/// Encodes a node's formulas as clauses, Plaisted-Greenbaum: a formula's literal implies the
/// formula, which suffices in normal form.
struct Encoder<'a> {
    normals: &'a [Normal],
    clauses: Vec<Vec<i32>>,
    atoms: Variables,
    nexts: Variables,
    pendings: Variables,
    literals: HashMap<usize, i32>,
    counter: i32,
}

impl Encoder<'_> {
    fn create_variable(&mut self) -> i32 {
        self.counter += 1;
        self.counter
    }

    fn encode(&mut self, formula: usize) -> i32 {
        if let Some(&cached) = self.literals.get(&formula) {
            return cached;
        }
        let literal = match &self.normals[formula] {
            Normal::Constant(value) => {
                let variable = self.create_variable();
                self.clauses
                    .push(vec![if *value { variable } else { -variable }]);
                variable
            }
            Normal::Literal { atom, is_positive } => {
                let variable = self.atoms.get(*atom, &mut self.counter);
                if *is_positive { variable } else { -variable }
            }
            Normal::Modal(Modal::Next, body) => self.nexts.get(*body, &mut self.counter),
            Normal::Junction(Junction::And, children) => {
                let variable = self.create_variable();
                for &child in children {
                    let child = self.encode(child);
                    self.clauses.push(vec![-variable, child]);
                }
                variable
            }
            Normal::Junction(Junction::Or, children) => {
                let variable = self.create_variable();
                let mut clause = vec![-variable];
                for &child in children {
                    clause.push(self.encode(child));
                }
                self.clauses.push(clause);
                variable
            }
            Normal::Modal(Modal::Always, body) => {
                let variable = self.create_variable();
                let body = self.encode(*body);
                self.clauses.push(vec![-variable, body]);
                let next = self.nexts.get(formula, &mut self.counter);
                self.clauses.push(vec![-variable, next]);
                variable
            }
            Normal::Modal(Modal::Eventually, body) => {
                let variable = self.create_variable();
                let body = self.encode(*body);
                let next = self.nexts.get(formula, &mut self.counter);
                self.clauses.push(vec![-variable, body, next]);
                let pending = self.pendings.get(formula, &mut self.counter);
                self.clauses.push(vec![-next, body, pending]);
                variable
            }
        };
        self.literals.insert(formula, literal);
        literal
    }
}

/// Every way to satisfy the formulas now, keeping only the steps that require the fewest next
/// formulas and leave the fewest eventualities pending. A step that requires more of both can only
/// do what a smaller one can, so dropping it keeps the decision complete. None once `is_expired`
/// turns true.
fn get_steps(
    normals: &[Normal],
    formulas: &[usize],
    is_expired: &mut dyn FnMut() -> bool,
) -> Option<Vec<Step>> {
    let mut encoder = Encoder {
        normals,
        clauses: Vec::new(),
        atoms: Variables::default(),
        nexts: Variables::default(),
        pendings: Variables::default(),
        literals: HashMap::new(),
        counter: 0,
    };
    for &formula in formulas {
        let literal = encoder.encode(formula);
        encoder.clauses.push(vec![literal]);
    }
    let choices: Vec<i32> = encoder
        .nexts
        .entries
        .iter()
        .chain(&encoder.pendings.entries)
        .map(|entry| entry.1)
        .collect();
    let mut solver = Solver::new(encoder.counter as usize);
    for clause in &encoder.clauses {
        solver.add_clause(clause);
    }
    let mut steps = Vec::new();
    loop {
        let model = match solver.solve(&[], is_expired) {
            Solution::Model(model) => model,
            Solution::Unsat => return Some(steps),
            Solution::Unknown => return None,
        };
        let is_set = |model: &[i8], variable: i32| model[variable as usize] == 1;
        // Drops each chosen variable that a model with no other choice can do without. A variable
        // one pass keeps stays needed as the set shrinks, so the set that remains is minimal.
        let mut minimal = model;
        for &choice in &choices {
            if !is_set(&minimal, choice) {
                continue;
            }
            let mut assumptions = vec![-choice];
            assumptions.extend(
                choices
                    .iter()
                    .filter(|&&other| !is_set(&minimal, other))
                    .map(|&other| -other),
            );
            match solver.solve(&assumptions, is_expired) {
                Solution::Unknown => return None,
                Solution::Unsat => {}
                Solution::Model(smaller) => minimal = smaller,
            }
        }
        let get_chosen = |variables: &Variables| -> Vec<usize> {
            variables
                .entries
                .iter()
                .filter(|entry| is_set(&minimal, entry.1))
                .map(|entry| entry.0)
                .collect()
        };
        steps.push(Step {
            next: get_chosen(&encoder.nexts),
            pending: get_chosen(&encoder.pendings),
        });
        let blocking: Vec<i32> = choices
            .iter()
            .filter(|&&choice| is_set(&minimal, choice))
            .map(|&choice| -choice)
            .collect();
        solver.add_clause(&blocking);
    }
}

/// The tableau's nodes, each a sorted set of formulas, numbered as they are found.
#[derive(Default)]
struct Nodes {
    nodes: Vec<Vec<usize>>,
    numbers: HashMap<Vec<usize>, usize>,
}

impl Nodes {
    fn get(&mut self, formulas: &[usize]) -> usize {
        let mut sorted = formulas.to_vec();
        sorted.sort();
        sorted.dedup();
        if let Some(&existing) = self.numbers.get(&sorted) {
            return existing;
        }
        self.numbers.insert(sorted.clone(), self.nodes.len());
        self.nodes.push(sorted);
        self.nodes.len() - 1
    }
}

/// Tarjan's algorithm, checking each component as it closes.
struct Components<'a> {
    edges: &'a [Vec<Edge>],
    indices: Vec<Option<usize>>,
    lowlinks: Vec<usize>,
    components: Vec<Option<usize>>,
    stack: Vec<usize>,
    index: usize,
    component: usize,
}

impl Components<'_> {
    fn is_fair(&self, component: usize) -> bool {
        let inner: Vec<&Edge> = self
            .edges
            .iter()
            .enumerate()
            .filter(|(source, _)| self.components[*source] == Some(component))
            .flat_map(|(_, outgoing)| outgoing)
            .filter(|edge| self.components[edge.target] == Some(component))
            .collect();
        let Some((first, rest)) = inner.split_first() else {
            return false;
        };
        first
            .pending
            .iter()
            .all(|eventuality| rest.iter().any(|edge| !edge.pending.contains(eventuality)))
    }

    fn visit(&mut self, node: usize) -> bool {
        self.indices[node] = Some(self.index);
        self.lowlinks[node] = self.index;
        self.index += 1;
        self.stack.push(node);
        for edge in &self.edges[node] {
            match self.indices[edge.target] {
                None => {
                    if self.visit(edge.target) {
                        return true;
                    }
                    self.lowlinks[node] = self.lowlinks[node].min(self.lowlinks[edge.target]);
                }
                Some(index) if self.components[edge.target].is_none() => {
                    self.lowlinks[node] = self.lowlinks[node].min(index);
                }
                Some(_) => {}
            }
        }
        if Some(self.lowlinks[node]) != self.indices[node] {
            return false;
        }
        let component = self.component;
        self.component += 1;
        while let Some(member) = self.stack.pop() {
            self.components[member] = Some(component);
            if member == node {
                break;
            }
        }
        self.is_fair(component)
    }
}

/// Whether the formula is satisfiable, or unknown once `is_expired` turns true.
pub fn get_satisfiability(formulas: &Formulas, is_expired: &mut dyn FnMut() -> bool) -> Verdict {
    let mut normalizer = Normalizer {
        formulas,
        table: Table::default(),
        memo: [
            vec![None; formulas.nodes.len()],
            vec![None; formulas.nodes.len()],
        ],
    };
    let root = normalizer.normalize(formulas.root, false);
    let normals = normalizer.table.normals;
    let mut nodes = Nodes::default();
    nodes.get(&[root]);
    let mut edges: Vec<Vec<Edge>> = Vec::new();
    let mut node = 0;
    while node < nodes.nodes.len() {
        if is_expired() {
            return Verdict::Unknown;
        }
        let Some(steps) = get_steps(&normals, &nodes.nodes[node].clone(), is_expired) else {
            return Verdict::Unknown;
        };
        edges.push(
            steps
                .into_iter()
                .map(|step| Edge {
                    target: nodes.get(&step.next),
                    pending: step.pending,
                })
                .collect(),
        );
        node += 1;
    }
    let count = nodes.nodes.len();
    let mut components = Components {
        edges: &edges,
        indices: vec![None; count],
        lowlinks: vec![0; count],
        components: vec![None; count],
        stack: Vec::new(),
        index: 0,
        component: 0,
    };
    if components.visit(0) {
        Verdict::Sat
    } else {
        Verdict::Unsat
    }
}
