//! TLC's solutions of a temporal formula (`tableau.ts`): the negated properties and the fairness
//! in disjunctive normal form, each disjunct split into the checks TLC makes on a behavior graph
//! and a formula it builds a tableau of. Terms are hash-consed, so two terms are equal just when
//! their ids are, as `getTermKey` makes them equal by structure with each atom standing for itself.

use std::collections::HashMap;

use crate::Declined;

pub const CONSTANT_LEVEL: u8 = 0;
pub const VARIABLE_LEVEL: u8 = 1;
pub const ACTION_LEVEL: u8 = 2;
pub const TEMPORAL_LEVEL: u8 = 3;

const MAXIMUM_DISJUNCTS: u64 = 2_147_483_647;

pub type TermId = u32;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Kind {
    Boolean(bool),
    /// A state predicate, by the position of its atom.
    State(u32),
    Enabled(u32),
    /// An action predicate, with the atom of its fairness's ENABLED.
    Action {
        atom: u32,
        enabled: Option<u32>,
    },
    Not,
    Always,
    Eventually,
    Next,
    And,
    Or,
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct Term {
    kind: Kind,
    children: Vec<TermId>,
}

#[derive(Default)]
pub struct Terms {
    terms: Vec<Term>,
    ids: HashMap<Term, TermId>,
}

pub struct TableauNode {
    pub particle: Vec<TermId>,
    pub successors: Vec<u32>,
    pub state_predicates: Vec<TermId>,
}

pub struct Tableau {
    pub nodes: Vec<TableauNode>,
    pub initial_count: usize,
}

pub struct Model {
    pub eventually_always: Vec<usize>,
    pub infinitely_often_states: Vec<usize>,
    pub infinitely_often_actions: Vec<usize>,
}

pub struct Solution {
    pub tableau: Option<Tableau>,
    /// The promises, each an Eventually term.
    pub promises: Vec<TermId>,
    pub state_checks: Vec<TermId>,
    pub action_checks: Vec<TermId>,
    pub models: Vec<Model>,
}

#[derive(Default)]
struct Classification {
    eventually_always: Vec<TermId>,
    infinitely_often_states: Vec<TermId>,
    infinitely_often_actions: Vec<TermId>,
    formulas: Vec<TermId>,
}

struct Triple {
    whole: TermId,
    first: TermId,
    second: TermId,
}

fn is_member(items: &[TermId], term: TermId) -> bool {
    items.contains(&term)
}

// A particle is a set of terms, so its key ignores order and repeats.
fn particle_key(particle: &[TermId]) -> Vec<TermId> {
    let mut key = particle.to_vec();
    key.sort_unstable();
    key.dedup();
    key
}

impl Terms {
    pub fn kind(&self, term: TermId) -> Kind {
        self.terms[term as usize].kind
    }

    pub fn children(&self, term: TermId) -> &[TermId] {
        &self.terms[term as usize].children
    }

    pub fn body(&self, term: TermId) -> TermId {
        self.terms[term as usize].children[0]
    }

    pub fn create(&mut self, kind: Kind, children: Vec<TermId>) -> TermId {
        let term = Term { kind, children };
        if let Some(&id) = self.ids.get(&term) {
            return id;
        }
        let id = self.terms.len() as TermId;
        self.terms.push(term.clone());
        self.ids.insert(term, id);
        id
    }

    pub fn boolean(&mut self, value: bool) -> TermId {
        self.create(Kind::Boolean(value), Vec::new())
    }

    pub fn unary(&mut self, kind: Kind, body: TermId) -> TermId {
        self.create(kind, vec![body])
    }

    fn pair(&mut self, kind: Kind, left: TermId, right: TermId) -> TermId {
        self.create(kind, vec![left, right])
    }

    /// A conjunction or disjunction, with each operand of the same kind flattened into it.
    pub fn junction(&mut self, kind: Kind, operands: &[TermId]) -> TermId {
        let mut flattened = Vec::with_capacity(operands.len());
        self.flatten_into(kind, operands, &mut flattened);
        self.create(kind, flattened)
    }

    fn flatten_into(&self, kind: Kind, operands: &[TermId], flattened: &mut Vec<TermId>) {
        for &operand in operands {
            if self.kind(operand) == kind {
                self.flatten_into(kind, &self.terms[operand as usize].children, flattened);
            } else {
                flattened.push(operand);
            }
        }
    }

    pub fn level(&self, term: TermId) -> u8 {
        match self.kind(term) {
            Kind::Boolean(_) => CONSTANT_LEVEL,
            Kind::State(_) | Kind::Enabled(_) => VARIABLE_LEVEL,
            Kind::Action { .. } | Kind::Next => ACTION_LEVEL,
            Kind::Not => self.level(self.body(term)),
            Kind::Always | Kind::Eventually => TEMPORAL_LEVEL,
            Kind::And | Kind::Or => self
                .children(term)
                .iter()
                .map(|&operand| self.level(operand))
                .fold(CONSTANT_LEVEL, u8::max),
        }
    }

    fn contains(&self, term: TermId, test: fn(Kind) -> bool) -> bool {
        test(self.kind(term))
            || self
                .children(term)
                .iter()
                .any(|&child| self.contains(child, test))
    }

    fn contains_action(&self, term: TermId) -> bool {
        self.contains(term, |kind| matches!(kind, Kind::Action { .. }))
    }

    /// Whether an Always is anywhere in the term.
    pub fn contains_always(&self, term: TermId) -> bool {
        self.contains(term, |kind| kind == Kind::Always)
    }

    fn is_atom(&self, term: TermId) -> bool {
        matches!(
            self.kind(term),
            Kind::State(_) | Kind::Enabled(_) | Kind::Action { .. }
        )
    }

    fn is_state_atom(&self, term: TermId) -> bool {
        matches!(
            self.kind(term),
            Kind::State(_) | Kind::Enabled(_) | Kind::Boolean(_)
        )
    }

    fn map_children(
        &mut self,
        term: TermId,
        mut map: impl FnMut(&mut Self, TermId) -> Result<TermId, Declined>,
    ) -> Result<Vec<TermId>, Declined> {
        let children = self.children(term).to_vec();
        children.into_iter().map(|child| map(self, child)).collect()
    }

    fn push_negation(&mut self, term: TermId, is_negated: bool) -> TermId {
        match self.kind(term) {
            Kind::Boolean(value) => {
                if is_negated {
                    self.boolean(!value)
                } else {
                    term
                }
            }
            Kind::State(_) | Kind::Enabled(_) | Kind::Action { .. } | Kind::Next => {
                if is_negated {
                    self.unary(Kind::Not, term)
                } else {
                    term
                }
            }
            Kind::Not => self.push_negation(self.body(term), !is_negated),
            kind @ (Kind::And | Kind::Or) => {
                let operands = self
                    .map_children(term, |terms, operand| {
                        Ok(terms.push_negation(operand, is_negated))
                    })
                    .unwrap_or_default();
                self.junction(if is_negated { dual(kind) } else { kind }, &operands)
            }
            kind @ (Kind::Always | Kind::Eventually) => {
                let unary = if is_negated == (kind == Kind::Always) {
                    Kind::Eventually
                } else {
                    Kind::Always
                };
                let body = self.push_negation(self.body(term), is_negated);
                self.unary(unary, body)
            }
        }
    }

    fn negate(&mut self, term: TermId) -> TermId {
        match self.kind(term) {
            Kind::Boolean(value) => self.boolean(!value),
            Kind::Not => self.body(term),
            kind @ (Kind::And | Kind::Or) => {
                let operands = self
                    .map_children(term, |terms, operand| Ok(terms.negate(operand)))
                    .unwrap_or_default();
                self.junction(dual(kind), &operands)
            }
            Kind::Always => {
                let body = self.negate(self.body(term));
                self.unary(Kind::Eventually, body)
            }
            Kind::Eventually => {
                let body = self.negate(self.body(term));
                self.unary(Kind::Always, body)
            }
            _ => self.unary(Kind::Not, term),
        }
    }

    fn simplify(&mut self, term: TermId) -> TermId {
        match self.kind(term) {
            kind @ (Kind::And | Kind::Or) => {
                let absorbing = kind == Kind::Or;
                let mut operands = Vec::new();
                for operand in self.children(term).to_vec() {
                    let simplified = self.simplify(operand);
                    match self.kind(simplified) {
                        Kind::Boolean(value) if value == absorbing => {
                            return self.boolean(absorbing);
                        }
                        Kind::Boolean(_) => {}
                        _ => operands.push(simplified),
                    }
                }
                match operands.len() {
                    0 => self.boolean(!absorbing),
                    1 => operands[0],
                    _ => self.junction(kind, &operands),
                }
            }
            Kind::Not => {
                let body = self.simplify(self.body(term));
                match self.kind(body) {
                    Kind::Boolean(value) => self.boolean(!value),
                    _ => self.unary(Kind::Not, body),
                }
            }
            kind @ (Kind::Always | Kind::Eventually) => {
                let body = self.simplify(self.body(term));
                let body = if self.kind(body) == kind {
                    self.body(body)
                } else {
                    body
                };
                self.unary(kind, body)
            }
            _ => term,
        }
    }

    fn infinitely_often_body(&self, term: TermId) -> Option<TermId> {
        (self.kind(term) == Kind::Always && self.kind(self.body(term)) == Kind::Eventually)
            .then(|| self.body(self.body(term)))
    }

    fn operands_of(&self, term: TermId, kind: Kind) -> Vec<TermId> {
        if self.kind(term) == kind {
            self.children(term).to_vec()
        } else {
            vec![term]
        }
    }

    fn disjunctive_normal_form(&mut self, term: TermId) -> Result<TermId, Declined> {
        match self.kind(term) {
            Kind::And => {
                let mut items = Vec::new();
                let mut total: u64 = 1;
                for operand in self.children(term).to_vec() {
                    let normal = self.disjunctive_normal_form(operand)?;
                    match self.kind(normal) {
                        Kind::And => {
                            items.extend_from_slice(self.children(normal));
                            continue;
                        }
                        Kind::Or => {
                            total = total.saturating_mul(self.children(normal).len() as u64);
                            if total > MAXIMUM_DISJUNCTS {
                                return Err(Declined::from(
                                    "a temporal formula too large in disjunctive normal form",
                                ));
                            }
                        }
                        _ => {}
                    }
                    items.push(normal);
                }
                if total == 1 {
                    return Ok(self.create(Kind::And, items));
                }
                let total = total as usize;
                let mut conjunctions = vec![Vec::new(); total];
                let (mut groups, mut repeat) = (1, total);
                for item in items {
                    if self.kind(item) != Kind::Or {
                        for conjunction in &mut conjunctions {
                            conjunction.push(item);
                        }
                        continue;
                    }
                    let operands = self.children(item).to_vec();
                    repeat /= operands.len();
                    let mut position = 0;
                    for _ in 0..groups {
                        for &operand in &operands {
                            for _ in 0..repeat {
                                conjunctions[position].push(operand);
                                position += 1;
                            }
                        }
                    }
                    groups *= operands.len();
                }
                let disjuncts = conjunctions
                    .iter()
                    .map(|conjunction| self.junction(Kind::And, conjunction))
                    .collect();
                Ok(self.create(Kind::Or, disjuncts))
            }
            Kind::Or => {
                let mut infinitely_often = Vec::new();
                let mut disjuncts = Vec::new();
                for operand in self.children(term).to_vec() {
                    let normal = self.disjunctive_normal_form(operand)?;
                    for item in self.operands_of(normal, Kind::Or) {
                        match self.infinitely_often_body(item) {
                            Some(body) => infinitely_often.push(body),
                            None => disjuncts.push(item),
                        }
                    }
                }
                if !infinitely_often.is_empty() {
                    let body = if infinitely_often.len() == 1 {
                        infinitely_often[0]
                    } else {
                        self.junction(Kind::Or, &infinitely_often)
                    };
                    let eventually = self.unary(Kind::Eventually, body);
                    disjuncts.push(self.unary(Kind::Always, eventually));
                }
                Ok(self.junction(Kind::Or, &disjuncts))
            }
            Kind::Not if !self.is_atom(self.body(term)) => {
                let negated = self.negate(self.body(term));
                self.disjunctive_normal_form(negated)
            }
            _ => Ok(term),
        }
    }

    fn flatten_single_junctions(&mut self, term: TermId) -> TermId {
        match self.kind(term) {
            kind @ (Kind::And | Kind::Or) => {
                let operands = self.children(term).to_vec();
                if operands.len() == 1 {
                    return self.flatten_single_junctions(operands[0]);
                }
                let flattened: Vec<_> = operands
                    .into_iter()
                    .map(|operand| self.flatten_single_junctions(operand))
                    .collect();
                self.junction(kind, &flattened)
            }
            Kind::Not => {
                let body = self.body(term);
                if self.kind(body) == Kind::Not {
                    return self.flatten_single_junctions(self.body(body));
                }
                let body = self.flatten_single_junctions(body);
                self.unary(Kind::Not, body)
            }
            kind @ (Kind::Always | Kind::Eventually | Kind::Next) => {
                let body = self.flatten_single_junctions(self.body(term));
                self.unary(kind, body)
            }
            _ => term,
        }
    }

    fn make_binary(&mut self, term: TermId) -> TermId {
        match self.kind(term) {
            kind @ (Kind::And | Kind::Or) => {
                let operands = self.children(term).to_vec();
                if operands.len() == 1 {
                    return self.make_binary(operands[0]);
                }
                let middle = operands.len() / 2;
                let left = self.junction(kind, &operands[..middle]);
                let right = self.junction(kind, &operands[middle..]);
                let left = self.make_binary(left);
                let right = self.make_binary(right);
                self.pair(kind, left, right)
            }
            kind @ (Kind::Not | Kind::Always | Kind::Eventually | Kind::Next) => {
                let body = self.make_binary(self.body(term));
                self.unary(kind, body)
            }
            _ => term,
        }
    }

    fn extract_promises(&self, term: TermId, promises: &mut Vec<TermId>) {
        if self.kind(term) == Kind::Eventually && !is_member(promises, term) {
            promises.push(term);
        }
        for &child in self.children(term) {
            self.extract_promises(child, promises);
        }
    }

    fn is_locally_consistent(&self, terms: &[TermId]) -> bool {
        let negative: Vec<TermId> = terms
            .iter()
            .filter(|&&term| self.kind(term) == Kind::Not && self.is_state_atom(self.body(term)))
            .map(|&term| self.body(term))
            .collect();
        !terms
            .iter()
            .any(|&term| self.is_state_atom(term) && is_member(&negative, term))
    }

    fn positive_closure(&mut self, terms: &[TermId]) -> Result<Vec<TermId>, Declined> {
        let mut pending = terms.to_vec();
        let mut closure = Vec::new();
        while let Some(term) = pending.pop() {
            match self.kind(term) {
                Kind::Not => pending.push(self.body(term)),
                Kind::Next => {
                    closure.push(term);
                    pending.push(self.body(term));
                }
                Kind::Always | Kind::Eventually => {
                    let next = self.unary(Kind::Next, term);
                    closure.extend([term, next]);
                    pending.push(self.body(term));
                }
                Kind::And | Kind::Or => {
                    pending.extend_from_slice(self.children(term));
                    closure.push(term);
                }
                Kind::Action { .. } => {
                    return Err(Declined::from("an action in the tableau"));
                }
                _ => closure.push(term),
            }
        }
        Ok(closure)
    }

    fn expansion(
        &mut self,
        term: TermId,
        repeated: Kind,
        junction: Kind,
    ) -> Result<Option<(TermId, TermId)>, Declined> {
        let kind = self.kind(term);
        if kind == repeated {
            let next = self.unary(Kind::Next, term);
            return Ok(Some((self.body(term), next)));
        }
        if kind != junction {
            return Ok(None);
        }
        match self.children(term) {
            [first, second, ..] => Ok(Some((*first, *second))),
            _ => Err(Declined::from("a junction of one term in the tableau")),
        }
    }

    fn triples(
        &mut self,
        closure: &[TermId],
        repeated: Kind,
        junction: Kind,
    ) -> Result<Vec<Triple>, Declined> {
        let mut triples = Vec::new();
        for &term in closure {
            if let Some((first, second)) = self.expansion(term, repeated, junction)? {
                triples.push(Triple {
                    whole: term,
                    first,
                    second,
                });
            }
        }
        Ok(triples)
    }

    fn particle_closure(&mut self, terms: &[TermId]) -> Result<Vec<Vec<TermId>>, Declined> {
        let closure = self.positive_closure(terms)?;
        let alphas = self.triples(&closure, Kind::Always, Kind::And)?;
        let betas = self.triples(&closure, Kind::Eventually, Kind::Or)?;
        self.expand(terms.to_vec(), &alphas, &betas)
    }

    fn expand(
        &mut self,
        particle: Vec<TermId>,
        alphas: &[Triple],
        betas: &[Triple],
    ) -> Result<Vec<Vec<TermId>>, Declined> {
        if !self.is_locally_consistent(&particle) {
            return Ok(Vec::new());
        }
        let mut expanded = particle.clone();
        let mut index = 0;
        while index < expanded.len() {
            if let Some((first, second)) =
                self.expansion(expanded[index], Kind::Always, Kind::And)?
            {
                if !is_member(&expanded, first) {
                    expanded.push(first);
                }
                if !is_member(&expanded, second) {
                    expanded.push(second);
                }
            }
            index += 1;
        }
        let mut is_changed = true;
        while is_changed {
            is_changed = false;
            for alpha in alphas {
                if is_member(&expanded, alpha.first)
                    && is_member(&expanded, alpha.second)
                    && !is_member(&expanded, alpha.whole)
                {
                    expanded.push(alpha.whole);
                    is_changed = true;
                }
            }
        }
        if expanded.len() > particle.len() && !self.is_locally_consistent(&expanded) {
            return Ok(Vec::new());
        }
        self.expand_beta(expanded, alphas, betas)
    }

    fn expand_beta(
        &mut self,
        particle: Vec<TermId>,
        alphas: &[Triple],
        betas: &[Triple],
    ) -> Result<Vec<Vec<TermId>>, Declined> {
        for index in 0..particle.len() {
            let Some((first, second)) =
                self.expansion(particle[index], Kind::Eventually, Kind::Or)?
            else {
                continue;
            };
            if is_member(&particle, first) || is_member(&particle, second) {
                continue;
            }
            let mut with_first = particle.clone();
            with_first.push(first);
            let mut with_second = particle;
            with_second.push(second);
            let left = self.expand(with_first, alphas, betas)?;
            let right = self.expand(with_second, alphas, betas)?;
            let right_keys: Vec<Vec<TermId>> =
                right.iter().map(|item| particle_key(item)).collect();
            let mut union: Vec<Vec<TermId>> = left
                .into_iter()
                .filter(|item| !right_keys.contains(&particle_key(item)))
                .collect();
            union.extend(right);
            return Ok(union);
        }
        let beta = betas.iter().find(|triple| {
            (is_member(&particle, triple.first) || is_member(&particle, triple.second))
                && !is_member(&particle, triple.whole)
        });
        match beta {
            Some(beta) => {
                let mut with_whole = particle;
                with_whole.push(beta.whole);
                self.expand(with_whole, alphas, betas)
            }
            None => Ok(vec![particle]),
        }
    }

    fn tableau_node(&self, particle: Vec<TermId>) -> TableauNode {
        // Constant terms count, as after TLC 1.7.4.
        let state_predicates = particle
            .iter()
            .copied()
            .filter(|&term| self.level(term) <= VARIABLE_LEVEL)
            .collect();
        TableauNode {
            particle,
            successors: Vec::new(),
            state_predicates,
        }
    }

    fn tableau(&mut self, formula: TermId) -> Result<Tableau, Declined> {
        let mut nodes: Vec<TableauNode> = self
            .particle_closure(&[formula])?
            .into_iter()
            .map(|particle| self.tableau_node(particle))
            .collect();
        let initial_count = nodes.len();
        let mut indices: HashMap<Vec<TermId>, u32> = HashMap::new();
        for (index, node) in nodes.iter().enumerate() {
            indices
                .entry(particle_key(&node.particle))
                .or_insert(index as u32);
        }
        let mut index = 0;
        while index < nodes.len() {
            let implied: Vec<TermId> = nodes[index]
                .particle
                .iter()
                .filter(|&&term| self.kind(term) == Kind::Next)
                .map(|&term| self.body(term))
                .collect();
            for particle in self.particle_closure(&implied)? {
                let key = particle_key(&particle);
                let target = match indices.get(&key) {
                    Some(&existing) => existing,
                    None => {
                        let target = nodes.len() as u32;
                        indices.insert(key, target);
                        nodes.push(self.tableau_node(particle));
                        target
                    }
                };
                nodes[index].successors.push(target);
            }
            index += 1;
        }
        Ok(Tableau {
            nodes,
            initial_count,
        })
    }

    pub fn is_fulfilling(&self, particle: &[TermId], promise: TermId) -> bool {
        !is_member(particle, promise) || is_member(particle, self.body(promise))
    }

    fn classify(&self, term: TermId, classification: &mut Classification) -> Result<(), Declined> {
        if self.kind(term) == Kind::Eventually {
            let body = self.body(term);
            if self.kind(body) == Kind::Always && self.level(self.body(body)) < TEMPORAL_LEVEL {
                classification.eventually_always.push(self.body(body));
                return Ok(());
            }
        }
        if let Some(body) = self.infinitely_often_body(term) {
            let level = self.level(body);
            if level <= VARIABLE_LEVEL {
                classification.infinitely_often_states.push(body);
                return Ok(());
            }
            if level == ACTION_LEVEL {
                classification.infinitely_often_actions.push(body);
                return Ok(());
            }
        }
        if self.contains_action(term) {
            return Err(Declined::from(
                "a temporal formula with actions not of the forms <>[]A or []<>A",
            ));
        }
        classification.formulas.push(term);
        Ok(())
    }

    /// The solutions of the formula, as `getSolutions` finds them, or why there are none TLC
    /// checks: an error TLC reports before the search, which the interpreter reports.
    pub fn solutions(&mut self, formula: TermId) -> Result<Vec<Solution>, Declined> {
        let negated = self.push_negation(formula, false);
        let simplified = self.simplify(negated);
        let normal = self.disjunctive_normal_form(simplified)?;
        if self.kind(normal) == Kind::Boolean(false) {
            return Err(Declined::from("a tautology"));
        }
        let mut groups: Vec<(Option<TermId>, Vec<Classification>)> = Vec::new();
        for disjunct in self.operands_of(normal, Kind::Or) {
            let flattened = self.flatten_single_junctions(disjunct);
            let mut classification = Classification::default();
            for conjunct in self.operands_of(flattened, Kind::And) {
                self.classify(conjunct, &mut classification)?;
            }
            let formulas = std::mem::take(&mut classification.formulas);
            let temporal = match formulas.len() {
                0 => None,
                1 => Some(formulas[0]),
                _ => Some(self.junction(Kind::And, &formulas)),
            };
            match groups.iter_mut().find(|group| group.0 == temporal) {
                Some(group) => group.1.push(classification),
                None => groups.push((temporal, vec![classification])),
            }
        }
        let mut solutions = Vec::with_capacity(groups.len());
        for (formula, classifications) in groups {
            let binary = formula.map(|formula| self.make_binary(formula));
            let mut promises = Vec::new();
            if let Some(binary) = binary {
                self.extract_promises(binary, &mut promises);
            }
            let mut state_checks = Vec::new();
            let mut action_checks = Vec::new();
            let models = classifications
                .iter()
                .map(|classification| Model {
                    infinitely_often_actions: classification
                        .infinitely_often_actions
                        .iter()
                        .map(|&check| add_to_bin(&mut action_checks, check))
                        .collect(),
                    infinitely_often_states: classification
                        .infinitely_often_states
                        .iter()
                        .map(|&check| add_to_bin(&mut state_checks, check))
                        .collect(),
                    eventually_always: classification
                        .eventually_always
                        .iter()
                        .map(|&check| add_to_bin(&mut action_checks, check))
                        .collect(),
                })
                .collect();
            let tableau = match binary {
                Some(binary) => Some(self.tableau(binary)?),
                None => None,
            };
            solutions.push(Solution {
                tableau,
                promises,
                state_checks,
                action_checks,
                models,
            });
        }
        Ok(solutions)
    }
}

fn dual(kind: Kind) -> Kind {
    if kind == Kind::And {
        Kind::Or
    } else {
        Kind::And
    }
}

fn add_to_bin(bin: &mut Vec<TermId>, term: TermId) -> usize {
    match bin.iter().position(|&item| item == term) {
        Some(index) => index,
        None => {
            bin.push(term);
            bin.len() - 1
        }
    }
}
