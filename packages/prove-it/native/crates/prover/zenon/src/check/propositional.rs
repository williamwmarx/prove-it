//! The checks of Zenon's rules for connectives, quantifiers and the cut.

use super::terms::{
    Checked, Checker, RuleSpec, Term, TermKind, and, equiv, expect_kind, expect_not, false_term,
    imply, instantiate, not, or, spec, term, true_term,
};
use crate::proof::RuleName;

fn get_conjuncts(formula: &Term) -> Vec<Term> {
    match formula.kind() {
        TermKind::And => formula.args().iter().flat_map(get_conjuncts).collect(),
        TermKind::Not => {
            let operand = formula.arg(0);
            match operand.kind() {
                TermKind::Or => operand
                    .args()
                    .iter()
                    .flat_map(|inner| get_conjuncts(&not(inner)))
                    .collect(),
                TermKind::Imply => [
                    get_conjuncts(&operand.arg(0)),
                    get_conjuncts(&not(&operand.arg(1))),
                ]
                .concat(),
                TermKind::Not => get_conjuncts(&operand.arg(0)),
                _ => vec![formula.clone()],
            }
        }
        _ => vec![formula.clone()],
    }
}

fn get_disjuncts(formula: &Term) -> Vec<Term> {
    match formula.kind() {
        TermKind::Or => formula.args().iter().flat_map(get_disjuncts).collect(),
        TermKind::Imply => [
            get_disjuncts(&not(&formula.arg(0))),
            get_disjuncts(&formula.arg(1)),
        ]
        .concat(),
        TermKind::Not => {
            let operand = formula.arg(0);
            match operand.kind() {
                TermKind::And => operand
                    .args()
                    .iter()
                    .flat_map(|inner| get_disjuncts(&not(inner)))
                    .collect(),
                TermKind::Not => get_disjuncts(&operand.arg(0)),
                _ => vec![formula.clone()],
            }
        }
        _ => vec![formula.clone()],
    }
}

// The witness of an existential: Hilbert's epsilon of its body.
fn get_witness(exists: &Term) -> Term {
    instantiate(exists, &term(TermKind::Tau, exists.symbol(), exists.args()))
}

fn ex(args: &[Term]) -> Checked<RuleSpec> {
    expect_kind(&args[0], TermKind::Ex)?;
    spec(vec![args[0].clone()], vec![vec![get_witness(&args[0])]])
}

fn not_all_ex(args: &[Term]) -> Checked<RuleSpec> {
    let for_all = expect_not(&args[0])?;
    expect_kind(&for_all, TermKind::All)?;
    let negated = term(
        TermKind::Ex,
        for_all.symbol(),
        vec![for_all.arg(0), not(&for_all.arg(1))],
    );
    spec(
        vec![args[0].clone()],
        vec![vec![get_witness(&negated), negated]],
    )
}

fn all(args: &[Term]) -> Checked<RuleSpec> {
    expect_kind(&args[0], TermKind::All)?;
    spec(
        vec![args[0].clone()],
        vec![vec![instantiate(&args[0], &args[1])]],
    )
}

fn not_ex(args: &[Term]) -> Checked<RuleSpec> {
    let exists = expect_not(&args[0])?;
    expect_kind(&exists, TermKind::Ex)?;
    spec(
        vec![args[0].clone()],
        vec![vec![not(&instantiate(&exists, &args[1]))]],
    )
}

/// `PROPOSITIONAL_RULES`.
pub fn propositional_rules(
    name: RuleName,
    args: &[Term],
    _checker: &mut Checker<'_>,
    _uses: &[Term],
) -> Option<Checked<RuleSpec>> {
    Some(match name {
        RuleName::Close => spec(vec![args[0].clone(), not(&args[0])], vec![]),
        RuleName::False => spec(vec![false_term()], vec![]),
        RuleName::NotTrue => spec(vec![not(&true_term())], vec![]),
        RuleName::ConjTree => spec(vec![args[0].clone()], vec![get_conjuncts(&args[0])]),
        RuleName::DisjTree => spec(
            vec![args[0].clone()],
            get_disjuncts(&args[0])
                .into_iter()
                .map(|inner| vec![inner])
                .collect(),
        ),
        RuleName::And => spec(
            vec![and(&args[0], &args[1])],
            vec![vec![args[0].clone(), args[1].clone()]],
        ),
        RuleName::NotNot => spec(vec![not(&not(&args[0]))], vec![vec![args[0].clone()]]),
        RuleName::NotOr => spec(
            vec![not(&or(&args[0], &args[1]))],
            vec![vec![not(&args[0]), not(&args[1])]],
        ),
        RuleName::NotImpl => spec(
            vec![not(&imply(&args[0], &args[1]))],
            vec![vec![args[0].clone(), not(&args[1])]],
        ),
        RuleName::Or => spec(
            vec![or(&args[0], &args[1])],
            vec![vec![args[0].clone()], vec![args[1].clone()]],
        ),
        RuleName::Impl => spec(
            vec![imply(&args[0], &args[1])],
            vec![vec![not(&args[0])], vec![args[1].clone()]],
        ),
        RuleName::Equiv => spec(
            vec![equiv(&args[0], &args[1])],
            vec![
                vec![not(&args[0]), not(&args[1])],
                vec![args[0].clone(), args[1].clone()],
            ],
        ),
        RuleName::NotAnd => spec(
            vec![not(&and(&args[0], &args[1]))],
            vec![vec![not(&args[0])], vec![not(&args[1])]],
        ),
        RuleName::NotEquiv => spec(
            vec![not(&equiv(&args[0], &args[1]))],
            vec![
                vec![not(&args[0]), args[1].clone()],
                vec![args[0].clone(), not(&args[1])],
            ],
        ),
        RuleName::Ex => ex(args),
        RuleName::NotAllEx => not_all_ex(args),
        RuleName::All => all(args),
        RuleName::NotEx => not_ex(args),
        RuleName::Cut => spec(vec![], vec![vec![args[0].clone()], vec![not(&args[0])]]),
        _ => return None,
    })
}
