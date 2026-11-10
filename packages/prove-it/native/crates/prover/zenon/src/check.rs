//! An independent check of the proofs that the Zenon port finds. It shares no code with the search:
//! formulas compare by their own alpha-equivalence, substitution and unfolding are rebuilt here, and
//! each rule's branches come from the lemma that justifies the rule in tlapm's Zenon.thy rather than
//! from the prover. The check walks the proof bottom up and computes the formulas each subproof
//! needs. A proof is valid when every rule is one of the lemmas and the root needs only hypotheses.

mod definitions;
mod equality;
mod functions;
mod keys;
mod propositional;
mod records;
mod relations;
mod rewrites;
mod sets;
mod terms;
mod tla;

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use prove_decide::Limits;

use self::definitions::get_definition_spec;
use self::equality::{equality_rules, get_relation_rule_spec};
use self::functions::function_rules;
use self::keys::Keys;
use self::propositional::propositional_rules;
use self::records::record_rules;
use self::relations::RelationProperties;
use self::rewrites::rewrite_rules;
use self::sets::set_rules;
pub use self::terms::CheckContext;
use self::terms::{Checked, Checker, RuleSpec, SpecTable, Term, UncheckedError, ensure};
use self::tla::tla_rules;
use crate::limits::get_limit_failure;
use crate::proof::{Proof, ProofKey, RuleName};

const PLAIN_RULES: [SpecTable; 7] = [
    propositional_rules,
    equality_rules,
    set_rules,
    function_rules,
    record_rules,
    rewrite_rules,
    tla_rules,
];

fn get_rule_spec(proof: &Proof, checker: &mut Checker<'_>) -> Checked<RuleSpec> {
    let rule = &proof.rule;
    // The TypeScript's types give each rule its arguments; a proof built here could break that.
    let arity = rule.name.arity();
    ensure(if rule.name.is_variadic() {
        rule.args.len() >= arity
    } else {
        rule.args.len() == arity
    })?;
    let args: Vec<Term> = rule.args.iter().map(Term::from).collect();
    match rule.name {
        RuleName::Definition => {
            let definition = rule.definition.as_ref().ok_or(UncheckedError)?;
            get_definition_spec(definition, &args, checker)
        }
        RuleName::CloseRefl | RuleName::CloseSym | RuleName::Refl | RuleName::PNotPSym => {
            let relation = rule.relation.as_deref().ok_or(UncheckedError)?;
            get_relation_rule_spec(rule.name, relation, &args, checker)
        }
        name => {
            let uses: Vec<Term> = proof.uses.iter().map(Term::from).collect();
            PLAIN_RULES
                .iter()
                .find_map(|table| table(name, &args, checker, &uses))
                .unwrap_or(Err(UncheckedError))
        }
    }
}

/// A set of keys that keeps the order they were added in, as a JavaScript `Set` does.
#[derive(Default)]
struct KeySet {
    order: Vec<Rc<str>>,
    members: HashSet<Rc<str>>,
}

impl KeySet {
    fn add(&mut self, key: Rc<str>) {
        if self.members.insert(key.clone()) {
            self.order.push(key);
        }
    }
}

fn get_needed(
    proof: &Proof,
    checker: &mut Checker<'_>,
    needed: &HashMap<ProofKey, KeySet>,
) -> Checked<KeySet> {
    let spec = get_rule_spec(proof, checker)?;
    ensure(spec.branches.len() == proof.subproofs.len())?;
    let mut result = KeySet::default();
    for key in spec
        .premises
        .iter()
        .map(|premise| checker.get_top_key(premise))
        .collect::<Checked<Vec<_>>>()?
    {
        result.add(key);
    }
    for (subproof, branch) in proof.subproofs.iter().zip(&spec.branches) {
        let branch = branch
            .iter()
            .map(|formula| checker.get_top_key(formula))
            .collect::<Checked<HashSet<_>>>()?;
        if let Some(keys) = needed.get(&ProofKey(subproof.clone())) {
            for key in &keys.order {
                if !branch.contains(key) {
                    result.add(key.clone());
                }
            }
        }
    }
    Ok(result)
}

fn check(root: &Rc<Proof>, checker: &mut Checker<'_>, limits: &Limits) -> Checked<bool> {
    let mut needed: HashMap<ProofKey, KeySet> = HashMap::new();
    // Subproofs before their parents, without recursion: proofs can be deep.
    let mut stack = vec![(root.clone(), false)];
    while !stack.is_empty() {
        if get_limit_failure(limits).is_some() {
            return Ok(false);
        }
        let Some((proof, is_ready)) = stack.pop() else {
            break;
        };
        let key = ProofKey(proof.clone());
        if needed.contains_key(&key) {
            continue;
        }
        if is_ready {
            let keys = get_needed(&proof, checker, &needed)?;
            needed.insert(key, keys);
            continue;
        }
        stack.push((proof.clone(), true));
        for subproof in &proof.subproofs {
            if !needed.contains_key(&ProofKey(subproof.clone())) {
                stack.push((subproof.clone(), false));
            }
        }
    }
    let hypotheses = checker
        .context
        .hypotheses
        .iter()
        .map(|hypothesis| checker.get_top_key(&Term::from(hypothesis)))
        .collect::<Checked<HashSet<_>>>()?;
    Ok(needed
        .get(&ProofKey(root.clone()))
        .is_none_or(|keys| keys.order.iter().all(|key| hypotheses.contains(key))))
}

/// True when the proof refutes the hypotheses: whether the proof is valid, or false once the limits
/// pass.
pub fn check_proof(root: &Rc<Proof>, context: &CheckContext, limits: &Limits) -> bool {
    let mut checker = Checker {
        context,
        keys: Keys::default(),
        relations: RelationProperties::new(context),
    };
    check(root, &mut checker, limits).unwrap_or(false)
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;
    use crate::expr::{Expr, Expressions, UNIVERSE};
    use crate::proof::Rule;

    fn unlimited() -> Limits {
        Limits::new(f64::INFINITY, None, None)
    }

    fn get_context(hypotheses: Vec<Expr>) -> CheckContext {
        CheckContext {
            hypotheses,
            definitions: Vec::new(),
        }
    }

    fn get_closure(formula: &Expr) -> Rc<Proof> {
        Rc::new(Proof {
            conclusions: Vec::new(),
            rule: Rule::new(RuleName::Close, vec![formula.clone()]),
            uses: Vec::new(),
            subproofs: Vec::new(),
        })
    }

    struct Fixture {
        exprs: Expressions,
        first: Expr,
        second: Expr,
        conjunction: Expr,
    }

    impl Fixture {
        fn new() -> Fixture {
            let exprs = Expressions::new();
            let first = exprs.evar("p");
            let second = exprs.evar("q");
            let conjunction = exprs.eand(&first, &second);
            Fixture {
                exprs,
                first,
                second,
                conjunction,
            }
        }

        fn get_split(&self, name: RuleName) -> Rc<Proof> {
            Rc::new(Proof {
                conclusions: Vec::new(),
                rule: Rule::new(name, vec![self.first.clone(), self.second.clone()]),
                uses: Vec::new(),
                subproofs: vec![get_closure(&self.first)],
            })
        }
    }

    #[test]
    fn accepts_a_closure_on_a_formula_and_its_negation() {
        let fixture = Fixture::new();
        let context = get_context(vec![
            fixture.first.clone(),
            fixture.exprs.enot(&fixture.first),
        ]);
        assert!(check_proof(
            &get_closure(&fixture.first),
            &context,
            &unlimited()
        ));
    }

    // tlapm kills Zenon at its deadline, so a proof that the checker hasn't accepted by then
    // doesn't count.
    #[test]
    fn stops_at_the_deadline_past_the_step_limit_or_once_aborted() {
        let fixture = Fixture::new();
        let context = get_context(vec![
            fixture.first.clone(),
            fixture.exprs.enot(&fixture.first),
        ]);
        let proof = get_closure(&fixture.first);
        assert!(!check_proof(
            &proof,
            &context,
            &Limits::new(-1.0, None, None)
        ));
        assert!(!check_proof(
            &proof,
            &context,
            &Limits::new(f64::INFINITY, None, Some(Arc::new(|| true)))
        ));
        assert!(!check_proof(
            &proof,
            &context,
            &Limits::new(f64::INFINITY, Some(0), None)
        ));
    }

    #[test]
    fn rejects_a_closure_without_the_negation() {
        let fixture = Fixture::new();
        assert!(!check_proof(
            &get_closure(&fixture.first),
            &get_context(vec![fixture.first.clone()]),
            &unlimited()
        ));
    }

    #[test]
    fn accepts_a_conjunction_split_into_its_conjuncts() {
        let fixture = Fixture::new();
        let context = get_context(vec![
            fixture.conjunction.clone(),
            fixture.exprs.enot(&fixture.first),
        ]);
        assert!(check_proof(
            &fixture.get_split(RuleName::And),
            &context,
            &unlimited()
        ));
    }

    #[test]
    fn rejects_a_rule_whose_premise_isnt_a_hypothesis() {
        let fixture = Fixture::new();
        let context = get_context(vec![
            fixture.exprs.eand(&fixture.second, &fixture.first),
            fixture.exprs.enot(&fixture.first),
        ]);
        assert!(!check_proof(
            &fixture.get_split(RuleName::And),
            &context,
            &unlimited()
        ));
    }

    #[test]
    fn rejects_a_disjunction_rule_on_a_conjunction() {
        let fixture = Fixture::new();
        let context = get_context(vec![
            fixture.conjunction.clone(),
            fixture.exprs.enot(&fixture.first),
        ]);
        assert!(!check_proof(
            &fixture.get_split(RuleName::Or),
            &context,
            &unlimited()
        ));
    }

    fn get_relation_context(symbol: &str) -> (Rc<Proof>, CheckContext) {
        let exprs = Expressions::new();
        let left = exprs.evar("a");
        let right = exprs.evar("b");
        let swapped = Rc::new(Proof {
            conclusions: Vec::new(),
            rule: Rule::relation(RuleName::CloseSym, "R", vec![left.clone(), right.clone()]),
            uses: Vec::new(),
            subproofs: Vec::new(),
        });
        let from = exprs.evar("x");
        let to = exprs.evar("y");
        let symmetry = exprs.eall(
            &from,
            UNIVERSE,
            &exprs.eall(
                &to,
                UNIVERSE,
                &exprs.eimply(
                    &exprs.eapp(symbol, &[from.clone(), to.clone()]),
                    &exprs.eapp(symbol, &[to.clone(), from.clone()]),
                ),
            ),
        );
        let context = get_context(vec![
            symmetry,
            exprs.eapp("R", &[left.clone(), right.clone()]),
            exprs.enot(&exprs.eapp("R", &[right, left])),
        ]);
        (swapped, context)
    }

    #[test]
    fn accepts_a_symmetric_closure_when_a_hypothesis_makes_the_relation_symmetric() {
        let (swapped, context) = get_relation_context("R");
        assert!(check_proof(&swapped, &context, &unlimited()));
    }

    #[test]
    fn rejects_a_symmetric_closure_without_that_hypothesis() {
        let (swapped, context) = get_relation_context("S");
        assert!(!check_proof(&swapped, &context, &unlimited()));
    }
}
