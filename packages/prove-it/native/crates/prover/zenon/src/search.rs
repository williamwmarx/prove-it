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

/// The proof of the hypotheses' inconsistency, or why the search gave up. `Err` is a
/// `TlaZenonError` that stops Zenon mid-search.
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

    // The expected values come from the TypeScript search with the TLA+ extension switched off and
    // without the built-in TLA+ definitions: the extension builds expressions even where it adds no
    // node, which changes the counts of created expressions.
    const CASES: [(&str, &str); 16] = [
        (
            r#"$hyp "h" (A. ((x) (=> (P x) (Q x))))
$hyp "h2" (P a)
$goal (Q a)"#,
            "proof 16 7 4 0 27 8 all impl close close",
        ),
        (
            r#"$hyp "trans" (A. ((x y z) (=> (/\ (R x y) (R y z)) (R x z))))
$hyp "sym" (A. ((x y) (=> (R x y) (R y x))))
$hyp "r1" (R a b)
$hyp "r2" (R c b)
$goal (R a c)"#,
            "proof 10 3 3 0 55 5 trans close_refl close_sym",
        ),
        (
            r#"$hyp "e1" (= x "a")
$hyp "e2" (= y "b")
$goal (-. (= x y))"#,
            "proof 8 4 4 0 23 4 not_not definition definition stringequal",
        ),
        (
            r#"$hyp "e1" (= "a" x)
$hyp "e2" (= y "b")
$hyp "e3" (= x z)
$goal (-. (= z y))"#,
            "proof 10 4 4 0 28 6 not_not definition stringdifflr close_sym",
        ),
        (
            r#"$def "d" (Double x) (/\ (P x) (P x))
$hyp "h" (Double a)
$goal (\/ (P a) (Q a))"#,
            "proof 10 4 4 0 17 6 definition and not_or close",
        ),
        (
            r#"$hyp "e" (= (f a) b)
$hyp "e2" (= b c)
$hyp "p" (P (f a))
$goal (P c)"#,
            "proof 11 4 4 0 27 6 p_not_p trans close_refl close",
        ),
        (
            r#"$hyp "h" (E. ((x) (/\ (P x) (A. ((y) (=> (P y) (= y x)))))))
$goal (E. ((x) (A. ((y) (=> (P y) (= x y))))))"#,
            "proof 60 34 9 0 137 33 ex and not_ex not_all_ex not_impl all impl close close_sym",
        ),
        (
            r#"$hyp "h" (\/ (P a) (Q a) (R a))
$hyp "h2" (=> (P a) (S a))
$hyp "h3" (=> (Q a) (S a))
$hyp "h4" (<=> (R a) (S a))
$goal (S a)"#,
            "proof 36 16 13 0 23 9 disj_tree impl close close impl close close equiv close close",
        ),
        (
            r#"$hyp "h" (A. ((x) (P x)))
$goal (Q a)"#,
            "exhausted 5 2 0 0 11 3",
        ),
        (
            r#"$hyp "le" (A. ((x y z) (=> (/\ (le x y) (le y z)) (le x z))))
$hyp "refl" (A. ((x) (le x x)))
$hyp "l1" (le a b)
$hyp "l2" (le b c)
$hyp "eq" (= c d)
$goal (/\ (le a d) (le e e))"#,
            "proof 18 7 6 0 60 8 definition not_and trans close close_refl close_refl",
        ),
        (
            r#"$hyp "x" (= (g a b) (g c d))
$hyp "y" (-. (= (h (g a b)) (h (g c d))))
$goal F."#,
            "proof 6 2 2 0 17 3 not_equal close",
        ),
        (
            r#"$hyp "h" (A. ((x) (E. ((y) (R x y)))))
$hyp "h2" (A. ((x y) (=> (R x y) (S y))))
$goal (E. ((z) (S z)))"#,
            "proof 66 32 13 1 121 22 all ex all all impl close not_ex close",
        ),
        (
            r#"$hyp "dm" (-. (/\ (\/ (P a) (Q a)) (-. (P a)) (-. (Q a)) (R b) (=> T. (R b))))
$goal (\/ (P a) (Q a) (-. (R b)))"#,
            "exhausted 19 9 5 0 28 7",
        ),
        (
            r#"$def "s" (Sub A B) (A. ((x) (=> (in x A) (in x B))))
$hyp "h1" (Sub a b)
$hyp "h2" (Sub b c)
$goal (Sub a c)"#,
            "proof 44 21 14 0 90 20 definition definition definition not_all_ex not_impl all impl all impl close close close",
        ),
        (
            r#"$hyp "x" (= u v)
$hyp "y" (= v w)
$hyp "z" (A. ((m) (=> (= m w) (P m))))
$goal (P u)"#,
            "proof 25 13 7 0 51 12 all impl close_refl p_not_p definition definition close_refl",
        ),
        (
            r#"$hyp "h" (A. ((x) (=> (P x) (P (f x)))))
$hyp "h2" (P a)
$hyp "h3" (A. ((x y) (=> (/\ (P x) (P y)) (P (g x y)))))
$goal (P b)"#,
            "exhausted 21 9 0 0 66 12",
        ),
    ];

    #[test]
    fn searches_as_the_typescript_does() {
        for (text, expected) in CASES {
            assert_eq!(run(text, 20_000), expected, "{text}");
        }
    }

    // The corpus's .znn files, under packages/prove-it/tests/fixtures, as the TypeScript searches
    // them without the TLA+ extension.
    const FIXTURES: [(&str, u64, &str); 79] = [
        (
            "zenon-encoder/Encoder-1.znn",
            5000,
            "exhausted 12 1 0 0 31 11",
        ),
        (
            "zenon-encoder/Encoder-11.znn",
            5000,
            "exhausted 2 1 0 0 9 1",
        ),
        (
            "zenon-encoder/Encoder-13.znn",
            5000,
            "exhausted 5 2 0 0 22 3",
        ),
        (
            "zenon-encoder/Encoder-15.znn",
            5000,
            "exhausted 2 1 0 0 19 1",
        ),
        (
            "zenon-encoder/Encoder-17.znn",
            5000,
            "exhausted 15 7 3 0 41 5",
        ),
        (
            "zenon-encoder/Encoder-19.znn",
            5000,
            "proof 22 11 6 0 60 9 not_ex not_ex not_and close_refl close_refl",
        ),
        (
            "zenon-encoder/Encoder-22.znn",
            5000,
            "exhausted 2 1 0 0 20 1",
        ),
        (
            "zenon-encoder/Encoder-3.znn",
            5000,
            "proof 6 2 2 0 14 4 definition close_refl",
        ),
        (
            "zenon-encoder/Encoder-5.znn",
            5000,
            "exhausted 3 1 0 0 10 2",
        ),
        (
            "zenon-encoder/Encoder-7.znn",
            5000,
            "exhausted 10 5 2 0 38 3",
        ),
        (
            "zenon-encoder/Encoder-9.znn",
            5000,
            "exhausted 4 2 0 0 27 2",
        ),
        (
            "zenon/memory/PaxosCommit_proof-253.znn",
            5000,
            "exhausted 49 16 1 0 250 33",
        ),
        (
            "zenon/proved/AtomicBakeryWithoutSMT-116.znn",
            5000,
            "exhausted 40 15 1 0 212 25",
        ),
        (
            "zenon/proved/AtomicBakeryWithoutSMT-414.znn",
            5000,
            "exhausted 66 26 2 0 284 44",
        ),
        (
            "zenon/proved/BubbleSort-14.znn",
            5000,
            "exhausted 5 1 0 0 34 4",
        ),
        (
            "zenon/proved/ByzPaxos-VoteProof-770.znn",
            5000,
            "exhausted 24 6 0 0 124 18",
        ),
        (
            "zenon/proved/EWD687a_proof-55.znn",
            5000,
            "exhausted 6 3 0 0 80 3",
        ),
        (
            "zenon/proved/EWD998PCal_proof-186.znn",
            5000,
            "proof 39 16 16 1 118 12 not_equal close_refl close close_refl not_equal definition not_equal not_equal not_equal close_refl close close_refl close_refl close_refl not_equal definition not_equal not_equal not_equal close_refl close close_refl close_refl",
        ),
        (
            "zenon/proved/EmptySetEqCases_proofs-630.znn",
            5000,
            "exhausted 16 11 2 0 52 7",
        ),
        (
            "zenon/proved/EmptySetEqCases_proofs-643.znn",
            5000,
            "exhausted 5 2 0 0 21 3",
        ),
        (
            "zenon/proved/FiniteSetTheorems_proofs-138.znn",
            5000,
            "exhausted 15 14 0 0 70 10",
        ),
        (
            "zenon/proved/FiniteSetTheorems_proofs-467.znn",
            5000,
            "exhausted 6 2 0 0 49 4",
        ),
        (
            "zenon/proved/FiniteSetTheorems_proofs-536.znn",
            5000,
            "exhausted 21 7 0 0 101 14",
        ),
        (
            "zenon/proved/FiniteSetTheorems_proofs-557.znn",
            5000,
            "exhausted 11 3 0 0 33 8",
        ),
        (
            "zenon/proved/FiniteSetTheorems_proofs-657.znn",
            5000,
            "exhausted 9 3 0 0 40 6",
        ),
        (
            "zenon/proved/NestedCdot_test-1.znn",
            5000,
            "exhausted 2 1 0 0 27 1",
        ),
        (
            "zenon/proved/SnapShot_test-142.znn",
            5000,
            "exhausted 8 3 0 0 71 5",
        ),
        (
            "zenon/proved/VoteProof-3.znn",
            5000,
            "exhausted 7 3 0 0 120 5",
        ),
        (
            "zenon/proved/VoteProof-429.znn",
            5000,
            "exhausted 22 6 0 0 78 16",
        ),
        (
            "zenon/proved/WellFoundedInduction_proofs-261.znn",
            5000,
            "exhausted 5 2 0 0 37 3",
        ),
        (
            "zenon/proved/bcastByz-720.znn",
            5000,
            "exhausted 16 4 0 0 104 13",
        ),
        (
            "zenon/proved/setEuclid_test-105.znn",
            5000,
            "exhausted 10 3 0 0 33 7",
        ),
        (
            "zenon/rules/boolcase_all.znn",
            5000,
            "exhausted 6 2 0 0 17 4",
        ),
        (
            "zenon/rules/boolcase_equal.znn",
            5000,
            "exhausted 5 2 0 0 13 3",
        ),
        (
            "zenon/rules/boolcase_equiv.znn",
            5000,
            "exhausted 7 2 0 0 15 5",
        ),
        (
            "zenon/rules/boolcase_imply.znn",
            5000,
            "exhausted 6 2 0 0 14 4",
        ),
        (
            "zenon/rules/boolcase_not.znn",
            5000,
            "exhausted 6 2 0 0 12 4",
        ),
        (
            "zenon/rules/boolcase_or.znn",
            5000,
            "exhausted 6 2 0 0 14 4",
        ),
        ("zenon/rules/box_p.znn", 5000, "exhausted 3 1 0 0 5 2"),
        ("zenon/rules/case.znn", 5000, "exhausted 11 4 0 0 25 7"),
        ("zenon/rules/case_other.znn", 5000, "exhausted 8 3 0 0 21 5"),
        (
            "zenon/rules/cup_subseteq.znn",
            5000,
            "exhausted 7 3 1 0 17 3",
        ),
        ("zenon/rules/iffalse.znn", 5000, "exhausted 2 1 0 0 7 1"),
        ("zenon/rules/iftrue.znn", 5000, "exhausted 2 1 0 0 7 1"),
        ("zenon/rules/in_addElt.znn", 5000, "exhausted 9 3 0 0 33 6"),
        ("zenon/rules/in_nat_succ.znn", 5000, "exhausted 2 1 0 0 8 1"),
        ("zenon/rules/in_upair.znn", 5000, "exhausted 6 2 0 0 19 4"),
        ("zenon/rules/neq_record.znn", 5000, "exhausted 4 1 0 0 19 3"),
        (
            "zenon/rules/noteq_x_true.znn",
            5000,
            "exhausted 3 1 0 0 6 2",
        ),
        (
            "zenon/rules/notin_UNION.znn",
            5000,
            "exhausted 6 2 0 0 18 4",
        ),
        (
            "zenon/rules/notin_addElt.znn",
            5000,
            "exhausted 2 1 0 0 8 1",
        ),
        ("zenon/rules/notin_upair.znn", 5000, "exhausted 2 1 0 0 6 1"),
        (
            "zenon/rules/notisafcn_extend.znn",
            5000,
            "exhausted 2 1 0 0 6 1",
        ),
        (
            "zenon/rules/notisafcn_onearg.znn",
            5000,
            "exhausted 2 1 0 0 6 1",
        ),
        ("zenon/rules/np_eq_r.znn", 5000, "exhausted 6 2 0 0 13 4"),
        ("zenon/rules/p_eq_l.znn", 5000, "exhausted 9 3 1 0 16 5"),
        ("zenon/rules/p_eq_r.znn", 5000, "exhausted 9 3 1 0 16 5"),
        (
            "zenon/rules/record_domain.znn",
            5000,
            "exhausted 2 1 0 0 13 1",
        ),
        (
            "zenon/rules/record_eq_match.znn",
            5000,
            "exhausted 3 1 0 0 18 2",
        ),
        (
            "zenon/rules/record_eq_mismatch.znn",
            5000,
            "exhausted 3 1 0 0 15 2",
        ),
        ("zenon/rules/record_neq.znn", 5000, "exhausted 4 1 0 0 19 3"),
        (
            "zenon/rules/record_notisafcn.znn",
            5000,
            "exhausted 2 1 0 0 7 1",
        ),
        (
            "zenon/rules/relation-close_sym.znn",
            5000,
            "proof 3 1 1 0 16 2 close_sym",
        ),
        (
            "zenon/rules/relation-p_not_p_sym.znn",
            5000,
            "proof 8 3 3 0 33 4 p_not_p_sym close close_refl",
        ),
        (
            "zenon/rules/relation-refl.znn",
            5000,
            "proof 5 2 2 0 14 3 refl close",
        ),
        (
            "zenon/rules/relation-trans.znn",
            5000,
            "proof 17 5 5 0 78 8 trans close_refl trans close close_refl",
        ),
        (
            "zenon/rules/relation-trans_eq.znn",
            5000,
            "proof 18 6 5 0 76 8 trans_eq close refl close close",
        ),
        (
            "zenon/rules/relation-trans_eq2.znn",
            5000,
            "proof 121 144 14 2 205 42 trans_eq2 all close all close all close",
        ),
        (
            "zenon/rules/relation-trans_eq_sym.znn",
            5000,
            "proof 158 176 27 2 234 30 all all trans_sym trans_sym trans_eq_sym close close close_refl all close_sym trans_sym all close_sym close_refl",
        ),
        (
            "zenon/rules/relation-trans_sym.znn",
            5000,
            "proof 10 3 3 0 56 5 trans_sym close close_refl",
        ),
        (
            "zenon/rules/relation-transsym.znn",
            5000,
            "proof 241 152 19 0 575 112 all all all all disj_tree close close_refl all all disj_tree close close close",
        ),
        (
            "zenon/rules/setemptyequal.znn",
            5000,
            "exhausted 2 1 0 0 5 0",
        ),
        (
            "zenon/rules/subseteq_cap.znn",
            5000,
            "exhausted 5 2 0 0 16 3",
        ),
        (
            "zenon/rules/tuple_eq_mismatch.znn",
            5000,
            "exhausted 3 1 0 0 12 2",
        ),
        (
            "zenon/unknown/DiningPhilosophers_proof-304.znn",
            5000,
            "exhausted 69 32 21 0 152 24",
        ),
        (
            "zenon/unknown/DiningPhilosophers_proof-464.znn",
            5000,
            "exhausted 13 5 0 0 50 8",
        ),
        (
            "zenon/rules/relation-transsym.znn",
            100,
            "step limit 101 54 4 0 313 48",
        ),
        (
            "zenon/rules/relation-trans_eq_sym.znn",
            100,
            "step limit 101 141 14 0 224 30",
        ),
        (
            "zenon/rules/relation-trans_eq2.znn",
            0,
            "step limit 1 0 0 0 31 0",
        ),
    ];

    #[test]
    fn searches_the_corpus_as_the_typescript_does() {
        let directory = concat!(env!("CARGO_MANIFEST_DIR"), "/../../../../tests/fixtures/");
        for (path, step_limit, expected) in FIXTURES {
            let text = std::fs::read_to_string(format!("{directory}{path}")).expect("a fixture");
            assert_eq!(run(&text, step_limit), expected, "{path}");
        }
    }

    const GROUP: &str = r#"$hyp "assoc" (A. ((x y z) (= (m (m x y) z) (m x (m y z)))))
$hyp "left" (A. ((x) (= (m e x) x)))
$hyp "inv" (A. ((x) (= (m (i x) x) e)))
$goal (A. ((x) (= (m x e) x)))"#;

    #[test]
    fn searches_longer_runs_as_the_typescript_does() {
        let pigeons = r#"$hyp "p1" (\/ (p a) (p b) (p c))
$hyp "p2" (\/ (q a) (q b) (q c))
$hyp "p3" (\/ (r a) (r b) (r c))
$hyp "p4" (\/ (s a) (s b) (s c))
$hyp "c1" (A. ((x) (-. (/\ (p x) (q x)))))
$hyp "c2" (A. ((x) (-. (/\ (p x) (r x)))))
$hyp "c3" (A. ((x) (-. (/\ (p x) (s x)))))
$hyp "c4" (A. ((x) (-. (/\ (q x) (r x)))))
$hyp "c5" (A. ((x) (-. (/\ (q x) (s x)))))
$hyp "c6" (A. ((x) (-. (/\ (r x) (s x)))))
$goal F."#;
        assert_eq!(
            run(pigeons, 200_000),
            "proof 1106 544 118 15 288 42 951:3673689603"
        );
        let order = r#"$hyp "le" (A. ((x y z) (=> (/\ (lt x y) (lt y z)) (lt x z))))
$hyp "s" (A. ((x) (lt x (s x))))
$hyp "n" (A. ((x) (-. (lt x x))))
$hyp "f" (A. ((x) (E. ((y) (/\ (lt x y) (P y))))))
$goal (E. ((x y) (/\ (P x) (/\ (P y) (lt x y)))))"#;
        assert_eq!(
            run(order, 200_000),
            "proof 243 193 25 0 674 111 all ex and not_ex all ex and not_ex disj_tree close close close"
        );
        assert_eq!(run(GROUP, 2000), "step limit 2001 4737 258 2 27037 698");
    }

    #[test]
    fn stops_at_the_memory_limit_as_the_typescript_does() {
        assert_eq!(
            run(GROUP, 200_000),
            "memory limit 6236 29018 778 4 143199 2234"
        );
    }

    #[test]
    fn closes_a_branch_on_true_negated() {
        assert_eq!(run("$goal T.", 100), "proof 2 1 1 0 2 1 not_true");
    }
}
