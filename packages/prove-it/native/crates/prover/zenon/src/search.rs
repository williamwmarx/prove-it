// Ported from Zenon's prove.ml, as shipped in tlapm. Copyright 2002 INRIA, see LICENSE.
//! The tableau search. Each formula added to a branch suggests nodes, which wait in the queue by
//! priority. The search takes the next node, and refutes each of its branches in turn. A branch is
//! closed when it holds a formula and its negation. Zenon's mutually recursive search functions are
//! one loop here, with an explicit stack of frames.

use std::collections::HashSet;
use std::rc::Rc;

use prove_decide::Limits;

use crate::ZenonError;
use crate::expr::{Expr, Kind, difference, is_disjoint, union};
use crate::limits::get_limit_failure;
use crate::node::{Node, Queue, get_queue_head, make_node, remove_node};
use crate::ocaml::stable_sort;
use crate::parse::Definition;
use crate::phrase::Hypothesis;
use crate::proof::{Proof, ProofKey, Rule, RuleName};
use crate::rules::{SearchContext, add_nodes};

fn is_trivial(context: &SearchContext, formula: &Expr) -> bool {
    formula.kind == Kind::True
        || (formula.kind == Kind::Not && formula.args[0].kind == Kind::False)
        || (formula.is_relation()
            && formula.args[0] == formula.args[1]
            && context.relations.is_reflexive(&formula.symbol))
}

// Zenon's reduce_list: drops the formulas a branch already has, and reverses the rest.
fn reduce_branch(context: &SearchContext, branch: &[Expr]) -> Vec<Expr> {
    let exprs = &context.exprs;
    let index = &context.index;
    let relations = &context.relations;
    // Last first: each kept formula goes to the front of the branch.
    let mut kept: Vec<Expr> = Vec::new();
    let is_known =
        |kept: &[Expr], formula: &Expr| index.is_member(formula) || kept.contains(formula);
    for formula in branch {
        let is_negated = formula.kind == Kind::Not;
        if formula.kind == Kind::True
            || (is_negated && formula.args[0].kind == Kind::False)
            || (is_negated
                && formula.args[0].is_app_with_arity("TLA.in", 2)
                && formula.args[0].args[1].kind == Kind::Var
                && &*formula.args[0].args[1].symbol == "TLA.emptyset")
        {
            continue;
        }
        let atom = if is_negated {
            &formula.args[0]
        } else {
            formula
        };
        let is_relation = atom.is_relation();
        if formula.kind == Kind::App
            && is_relation
            && formula.args[0] == formula.args[1]
            && relations.is_reflexive(&formula.symbol)
        {
            continue;
        }
        if is_relation && relations.is_symmetric(&atom.symbol) {
            let swapped = exprs.eapp(&atom.symbol, &[atom.args[1].clone(), atom.args[0].clone()]);
            let reversed = if is_negated {
                exprs.enot(&swapped)
            } else {
                swapped
            };
            if !is_known(&kept, formula) && !is_known(&kept, &reversed) {
                kept.push(formula.clone());
            }
            continue;
        }
        if !is_known(&kept, formula) {
            kept.push(formula.clone());
        }
    }
    kept.reverse();
    kept
}

fn is_not_meta_equality(formula: &Expr) -> bool {
    if formula.is_app_with_arity("=", 2) {
        return !formula.args[0].is_meta() && !formula.args[1].is_meta();
    }
    if formula.kind == Kind::App && formula.args.len() == 3 && formula.args[0].kind == Kind::Var {
        return !(&*formula.args[0].symbol == "_" && formula.args[1].is_meta());
    }
    if formula.is_relation() {
        return !formula.args[1].is_meta();
    }
    if formula.kind == Kind::And || formula.kind == Kind::Or {
        return is_not_meta_equality(&formula.args[0]) || is_not_meta_equality(&formula.args[1]);
    }
    true
}

fn is_not_trivial(formula: &Expr) -> bool {
    if formula.kind == Kind::Not && formula.args[0].is_app_with_arity("=", 2) {
        let atom = &formula.args[0];
        return !atom.args[0].is_meta() && !atom.args[1].is_meta();
    }
    if formula.kind == Kind::Not && formula.args[0].is_app_with_arity("TLA.in", 2) {
        let atom = &formula.args[0];
        if atom.args[0].is_meta() && atom.args[1].kind == Kind::Var {
            return &*atom.args[1].symbol == "TLA.emptyset";
        }
        return true;
    }
    if formula.kind == Kind::And || formula.kind == Kind::Or {
        return is_not_trivial(&formula.args[0]) || is_not_trivial(&formula.args[1]);
    }
    true
}

fn count_metas(formulas: &[Expr]) -> usize {
    let mut metas = HashSet::new();
    for formula in formulas.iter().filter(|inner| is_not_meta_equality(inner)) {
        for meta in formula.metas.iter() {
            if meta.metas.is_empty() {
                metas.insert(meta.clone());
            }
        }
    }
    metas.len()
}

/// A branch's subproof once it is closed, `None` while it is open.
type BranchState = Option<Rc<Proof>>;

#[derive(Clone)]
struct Score {
    index: usize,
    nontrivial: usize,
    metas: usize,
    size: i64,
}

fn find_open_branch(search_node: &Node, states: &[BranchState]) -> Option<usize> {
    let last = states.len().checked_sub(1)?;
    if states[last].is_none() && search_node.branches[last].iter().any(is_not_meta_equality) {
        return Some(last);
    }
    let open: Vec<usize> = (0..=last)
        .filter(|position| states[*position].is_none())
        .collect();
    if open.len() <= 1 {
        return open.first().copied();
    }
    let scores: Vec<Score> = open
        .iter()
        .rev()
        .map(|position| {
            let formulas = &search_node.branches[*position];
            Score {
                index: *position,
                nontrivial: formulas
                    .iter()
                    .filter(|inner| is_not_trivial(inner))
                    .count(),
                metas: count_metas(formulas),
                size: formulas.iter().map(|formula| formula.size).sum(),
            }
        })
        .collect();
    let sorted = stable_sort(&scores, &|left: &Score, right: &Score| {
        if left.nontrivial == 0 {
            return std::cmp::Ordering::Greater;
        }
        if right.nontrivial == 0 {
            return std::cmp::Ordering::Less;
        }
        if left.metas != right.metas {
            return right.metas.cmp(&left.metas);
        }
        left.size.cmp(&right.size)
    });
    sorted.first().map(|score| score.index)
}

fn is_good_lemma(rule: &Rule) -> bool {
    !matches!(
        rule.name,
        RuleName::Close
            | RuleName::CloseRefl
            | RuleName::CloseSym
            | RuleName::False
            | RuleName::NotTrue
    )
}

struct Frame {
    node: Rc<Node>,
    queue: Queue,
    states: Vec<BranchState>,
    current: usize,
}

#[derive(Default)]
pub struct SearchStatistics {
    pub inferences: u64,
    pub proof_nodes: u64,
    /// The proofs that closed another branch from the lemma cache. Zenon counts the uses in mlrefc
    /// and prints each of these proofs once, as a lemma.
    pub reused_proofs: HashSet<ProofKey>,
}

/// The proof of the hypotheses' inconsistency, or why the search gave up: "exhausted",
/// "time limit", "step limit", "memory limit" or "aborted" (`SearchFailure`).
pub enum SearchOutcome {
    Proof(Rc<Proof>),
    Failure(&'static str),
}

// Zenon gives up once its heap passes 1 GB. The port bounds the nodes that the queues of the
// current branch hold instead. On the corpus files where Zenon runs out of memory, its heap passes
// 1 GB with 1.9 to 5.5 million of them, and no proof that Zenon finds needs more than 1.3 million.
const MAX_QUEUED_NODES: u64 = 1_900_000;

/// Where [`Search::unwind`] stops: at the root, with its proof, or at the frame to continue, with
/// the proof recorded.
enum Unwound {
    Root(Rc<Proof>),
    Frame(Frame),
}

struct Search<'a> {
    context: &'a mut SearchContext,
    statistics: &'a mut SearchStatistics,
    stack: Vec<Frame>,
    forms: Vec<(Expr, i64)>,
    form_index: usize,
    queue: Queue,
}

impl Search<'_> {
    fn make_result(
        &mut self,
        search_node: &Node,
        states: &[BranchState],
    ) -> Result<Rc<Proof>, ZenonError> {
        let mut conclusions: Vec<Expr> = Vec::new();
        let mut subproofs = Vec::new();
        for (branch_index, state) in states.iter().enumerate() {
            let Some(state) = state else {
                return Err(ZenonError::new("Zenon: an open branch in a closed node"));
            };
            subproofs.push(state.clone());
            conclusions = union(
                &difference(&state.conclusions, &search_node.branches[branch_index]),
                &conclusions,
            );
        }
        self.statistics.proof_nodes += 1;
        let proof = Rc::new(Proof {
            conclusions: union(&search_node.conclusions, &conclusions),
            rule: search_node.rule.clone(),
            uses: search_node.conclusions.clone(),
            subproofs,
        });
        if is_good_lemma(&search_node.rule) {
            self.context.index.add_lemma(proof.clone());
        }
        Ok(proof)
    }

    // Zenon's next_branch and unwind: descend into the next open branch of a node, or close the
    // node and pop frames until one has an open branch left.
    fn advance(
        &mut self,
        search_node: Rc<Node>,
        node_queue: Queue,
        states: Vec<BranchState>,
    ) -> Result<Option<Rc<Proof>>, ZenonError> {
        let mut current_node = search_node;
        let mut current_queue = node_queue;
        let mut current_states = states;
        loop {
            if let Some(open) = find_open_branch(&current_node, &current_states) {
                self.forms = current_node.branches[open]
                    .iter()
                    .map(|formula| (formula.clone(), current_node.goalness))
                    .collect();
                self.form_index = 0;
                self.queue = current_queue.clone();
                self.stack.push(Frame {
                    node: current_node,
                    queue: current_queue,
                    states: current_states,
                    current: open,
                });
                return Ok(None);
            }
            let result = self.make_result(&current_node, &current_states)?;
            match self.unwind(result) {
                Unwound::Root(closed) => return Ok(Some(closed)),
                Unwound::Frame(frame) => {
                    current_node = frame.node;
                    current_queue = frame.queue;
                    current_states = frame.states;
                }
            }
        }
    }

    // Pops the frames that the proof closes. Returns the proof when it closes the root, and the
    // frame to continue otherwise, with the proof recorded.
    fn unwind(&mut self, proof: Rc<Proof>) -> Unwound {
        loop {
            let Some(mut frame) = self.stack.pop() else {
                return Unwound::Root(proof);
            };
            let branch = &frame.node.branches[frame.current];
            for formula in branch.iter().rev() {
                if self.context.index.is_member(formula) {
                    self.context.index.remove(formula);
                }
            }
            if is_disjoint(branch, &proof.conclusions) {
                continue;
            }
            frame.states[frame.current] = Some(proof);
            return Unwound::Frame(frame);
        }
    }

    fn run(&mut self, limits: &Limits) -> Result<SearchOutcome, ZenonError> {
        loop {
            if let Some(failure) = get_limit_failure(limits) {
                return Ok(SearchOutcome::Failure(failure));
            }
            if self.queue.inserted_count > MAX_QUEUED_NODES {
                return Ok(SearchOutcome::Failure("memory limit"));
            }
            if let Some(entry) = self.forms.get(self.form_index).cloned() {
                self.form_index += 1;
                let formula = entry.0;
                if is_trivial(self.context, &formula) {
                    continue;
                }
                self.context.index.add(&formula, entry.1);
                self.queue = add_nodes(self.context, &self.queue, &formula, entry.1)?;
                continue;
            }
            let head = get_queue_head(&self.queue);
            let lemma = if head.is_none_or(|head| is_good_lemma(&head.rule)) {
                self.context.index.search_lemma()
            } else {
                None
            };
            if let Some(lemma) = lemma {
                self.statistics
                    .reused_proofs
                    .insert(ProofKey(lemma.clone()));
                let frame = match self.unwind(lemma) {
                    Unwound::Root(closed) => return Ok(SearchOutcome::Proof(closed)),
                    Unwound::Frame(frame) => frame,
                };
                if let Some(result) = self.advance(frame.node, frame.queue, frame.states)? {
                    return Ok(SearchOutcome::Proof(result));
                }
                continue;
            }
            // Zenon's next_node: the next node whose branches all add something new.
            loop {
                self.statistics.inferences += 1;
                let Some(removed) = remove_node(&self.queue) else {
                    return Ok(SearchOutcome::Failure("exhausted"));
                };
                self.queue = removed.1;
                let reduced: Vec<Vec<Expr>> = removed
                    .0
                    .branches
                    .iter()
                    .map(|branch| reduce_branch(self.context, branch))
                    .collect();
                if reduced.iter().any(Vec::is_empty) {
                    continue;
                }
                let states = vec![None; reduced.len()];
                let search_node = make_node(
                    removed.0.conclusions.clone(),
                    removed.0.rule.clone(),
                    removed.0.priority.clone(),
                    removed.0.goalness,
                    reduced,
                );
                if let Some(result) = self.advance(search_node, self.queue.clone(), states)? {
                    return Ok(SearchOutcome::Proof(result));
                }
                break;
            }
        }
    }
}

/// The proof of the hypotheses' inconsistency, or why the search gave up. `Err` is an error
/// that stops Zenon mid-search.
pub fn search(
    context: &mut SearchContext,
    definitions: &[Rc<Definition>],
    hypotheses: &[Hypothesis],
    limits: &Limits,
    statistics: &mut SearchStatistics,
) -> Result<SearchOutcome, ZenonError> {
    for definition in definitions {
        context.index.add_definition(definition.clone());
    }
    let mut initial: Vec<(Expr, i64)> = Vec::new();
    for hypothesis in hypotheses {
        if !initial.iter().any(|entry| entry.0 == hypothesis.formula) {
            initial.push((hypothesis.formula.clone(), hypothesis.goalness));
        }
    }
    initial.reverse();
    Search {
        context,
        statistics,
        stack: Vec::new(),
        forms: initial,
        form_index: 0,
        queue: Queue::default(),
    }
    .run(limits)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::eqrel::Relations;
    use crate::expr::Expressions;
    use crate::index_table::Index;
    use crate::parse::parse_zenon;
    use crate::phrase::separate;

    fn get_rules(proof: &Proof) -> String {
        std::iter::once(proof.rule.name.as_str().to_owned())
            .chain(proof.subproofs.iter().map(|inner| get_rules(inner)))
            .collect::<Vec<_>>()
            .join(" ")
    }

    fn get_digest(text: &str) -> u32 {
        text.bytes().fold(0x811c_9dc5, |hash: u32, byte| {
            (hash ^ u32::from(byte)).wrapping_mul(0x0100_0193)
        })
    }

    /// The outcome, steps, nodes searched, proof nodes, reused proofs, expressions created, most
    /// formulas on a branch, and the proof's rules in preorder (their length and digest when long).
    fn run(text: &str, step_limit: u64) -> String {
        let exprs = Expressions::new();
        let phrases = parse_zenon(&exprs, text).expect("a valid .znn text");
        let separated = separate(&["="], &phrases);
        let mut relations = Relations::new();
        for hypothesis in &separated.hypotheses {
            relations.analyse(&exprs, &hypothesis.formula);
        }
        let mut hypotheses = Vec::new();
        for hypothesis in &separated.hypotheses {
            if !relations.is_subsumed(&exprs, &hypothesis.formula) {
                hypotheses.push(hypothesis.clone());
            }
        }
        let mut context = SearchContext {
            index: Index::new(),
            relations,
            exprs,
        };
        let limits = Limits::new(f64::INFINITY, Some(step_limit), None);
        let mut statistics = SearchStatistics::default();
        let outcome = search(
            &mut context,
            &separated.definitions,
            &hypotheses,
            &limits,
            &mut statistics,
        )
        .expect("no Zenon error");
        let (name, rules) = match outcome {
            SearchOutcome::Proof(proof) => ("proof", get_rules(&proof)),
            SearchOutcome::Failure(failure) => (failure, String::new()),
        };
        let rules = if rules.len() > 300 {
            format!("{}:{}", rules.len(), get_digest(&rules))
        } else {
            rules
        };
        format!(
            "{name} {} {} {} {} {} {} {rules}",
            limits.steps(),
            statistics.inferences,
            statistics.proof_nodes,
            statistics.reused_proofs.len(),
            context.exprs.get_created_count(),
            context.index.get_top_formula_count(),
        )
        .trim_end()
        .to_owned()
    }

    #[test]
    fn closes_a_branch_on_true_negated() {
        assert_eq!(run("$goal T.", 100), "proof 2 1 1 0 2 1 not_true");
    }
}
