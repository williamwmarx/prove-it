//! The checks of the TLA+ extension's rules for set membership, set equality and subsets, after the
//! lemmas in Zenon.thy that justify them.

use super::terms::{
    Checked, Checker, RuleSpec, Term, TermKind, and, app, domain, ensure, equal, equiv, expect_app,
    expect_not, fapply, imply, instantiate, is_app, is_variable, member, not, spec,
};
use crate::proof::RuleName;

struct Membership {
    element: Term,
    operands: Vec<Term>,
    set: Term,
}

fn get_membership_spec(
    formula: &Term,
    is_negated: bool,
    constructor: &str,
    arity: usize,
) -> Checked<Membership> {
    let atom = if is_negated {
        expect_not(formula)?
    } else {
        formula.clone()
    };
    let sides = expect_app(&atom, "TLA.in", Some(2))?;
    Ok(Membership {
        element: sides[0].clone(),
        operands: expect_app(&sides[1], constructor, Some(arity))?,
        set: sides[1].clone(),
    })
}

fn get_set_equal_spec(
    formula: &Term,
    is_negated: bool,
    checker: &mut Checker<'_>,
) -> Checked<RuleSpec> {
    let sides = expect_app(
        &if is_negated {
            expect_not(formula)?
        } else {
            formula.clone()
        },
        "=",
        Some(2),
    )?;
    let extensional = checker.bind(TermKind::All, "", |bound| {
        equiv(&member(bound, &sides[0]), &member(bound, &sides[1]))
    });
    spec(
        vec![formula.clone()],
        vec![vec![if is_negated {
            not(&extensional)
        } else {
            extensional
        }]],
    )
}

fn in_emptyset(args: &[Term]) -> Checked<RuleSpec> {
    ensure(is_variable(
        &expect_app(&args[0], "TLA.in", Some(2))?[1],
        "TLA.emptyset",
    ))?;
    spec(vec![args[0].clone()], vec![])
}

fn in_upair(args: &[Term]) -> Checked<RuleSpec> {
    let membership = get_membership_spec(&args[0], false, "TLA.upair", 2)?;
    spec(
        vec![args[0].clone()],
        membership
            .operands
            .iter()
            .map(|inner| vec![equal(&membership.element, inner)])
            .collect(),
    )
}

fn notin_upair(args: &[Term]) -> Checked<RuleSpec> {
    let membership = get_membership_spec(&args[0], true, "TLA.upair", 2)?;
    spec(
        vec![args[0].clone()],
        vec![
            membership
                .operands
                .iter()
                .map(|inner| not(&equal(&membership.element, inner)))
                .collect(),
        ],
    )
}

fn in_add_elt(args: &[Term]) -> Checked<RuleSpec> {
    let membership = get_membership_spec(&args[0], false, "TLA.addElt", 2)?;
    let mut branches = Vec::new();
    let mut rest = membership.set.clone();
    while is_app(&rest, "TLA.addElt", Some(2)) {
        branches.push(vec![equal(&membership.element, &rest.arg(0))]);
        rest = rest.arg(1);
    }
    if !is_variable(&rest, "TLA.emptyset") {
        branches.push(vec![member(&membership.element, &rest)]);
    }
    spec(vec![args[0].clone()], branches)
}

fn notin_add_elt(args: &[Term]) -> Checked<RuleSpec> {
    let membership = get_membership_spec(&args[0], true, "TLA.addElt", 2)?;
    let mut formulas = Vec::new();
    let mut rest = membership.set.clone();
    while is_app(&rest, "TLA.addElt", Some(2)) {
        formulas.push(not(&equal(&membership.element, &rest.arg(0))));
        rest = rest.arg(1);
    }
    if !is_variable(&rest, "TLA.emptyset") {
        formulas.push(not(&member(&membership.element, &rest)));
    }
    spec(vec![args[0].clone()], vec![formulas])
}

fn in_set(args: &[Term]) -> Checked<RuleSpec> {
    let sides = expect_app(&args[0], "TLA.in", Some(2))?;
    let elements = expect_app(&sides[1], "TLA.set", None)?;
    spec(
        vec![args[0].clone()],
        elements
            .iter()
            .map(|inner| vec![equal(&sides[0], inner)])
            .collect(),
    )
}

fn notin_set(args: &[Term]) -> Checked<RuleSpec> {
    let sides = expect_app(&expect_not(&args[0])?, "TLA.in", Some(2))?;
    let elements = expect_app(&sides[1], "TLA.set", None)?;
    spec(
        vec![args[0].clone()],
        vec![
            elements
                .iter()
                .map(|inner| not(&equal(&sides[0], inner)))
                .collect(),
        ],
    )
}

fn in_subset(args: &[Term], is_negated: bool) -> Checked<RuleSpec> {
    let membership = get_membership_spec(&args[0], is_negated, "TLA.SUBSET", 1)?;
    let subset = app(
        "TLA.subseteq",
        vec![membership.element, membership.operands[0].clone()],
    );
    spec(
        vec![args[0].clone()],
        vec![vec![if is_negated { not(&subset) } else { subset }]],
    )
}

fn in_union(args: &[Term], is_negated: bool, checker: &mut Checker<'_>) -> Checked<RuleSpec> {
    let membership = get_membership_spec(&args[0], is_negated, "TLA.UNION", 1)?;
    let exists = checker.bind(TermKind::Ex, "", |bound| {
        and(
            &member(bound, &membership.operands[0]),
            &member(&membership.element, bound),
        )
    });
    spec(
        vec![args[0].clone()],
        vec![vec![if is_negated { not(&exists) } else { exists }]],
    )
}

fn in_cup(args: &[Term]) -> Checked<RuleSpec> {
    let membership = get_membership_spec(&args[0], false, "TLA.cup", 2)?;
    spec(
        vec![args[0].clone()],
        membership
            .operands
            .iter()
            .map(|inner| vec![member(&membership.element, inner)])
            .collect(),
    )
}

fn notin_cup(args: &[Term]) -> Checked<RuleSpec> {
    let membership = get_membership_spec(&args[0], true, "TLA.cup", 2)?;
    spec(
        vec![args[0].clone()],
        vec![
            membership
                .operands
                .iter()
                .map(|inner| not(&member(&membership.element, inner)))
                .collect(),
        ],
    )
}

fn in_cap(args: &[Term]) -> Checked<RuleSpec> {
    let membership = get_membership_spec(&args[0], false, "TLA.cap", 2)?;
    spec(
        vec![args[0].clone()],
        vec![
            membership
                .operands
                .iter()
                .map(|inner| member(&membership.element, inner))
                .collect(),
        ],
    )
}

fn notin_cap(args: &[Term]) -> Checked<RuleSpec> {
    let membership = get_membership_spec(&args[0], true, "TLA.cap", 2)?;
    spec(
        vec![args[0].clone()],
        membership
            .operands
            .iter()
            .map(|inner| vec![not(&member(&membership.element, inner))])
            .collect(),
    )
}

fn in_setminus(args: &[Term]) -> Checked<RuleSpec> {
    let membership = get_membership_spec(&args[0], false, "TLA.setminus", 2)?;
    spec(
        vec![args[0].clone()],
        vec![vec![
            member(&membership.element, &membership.operands[0]),
            not(&member(&membership.element, &membership.operands[1])),
        ]],
    )
}

fn notin_setminus(args: &[Term]) -> Checked<RuleSpec> {
    let membership = get_membership_spec(&args[0], true, "TLA.setminus", 2)?;
    spec(
        vec![args[0].clone()],
        vec![
            vec![not(&member(&membership.element, &membership.operands[0]))],
            vec![member(&membership.element, &membership.operands[1])],
        ],
    )
}

fn in_subsetof(args: &[Term]) -> Checked<RuleSpec> {
    let membership = get_membership_spec(&args[0], false, "TLA.subsetOf", 2)?;
    let predicate = &membership.operands[1];
    ensure(predicate.kind() == TermKind::Lam)?;
    spec(
        vec![args[0].clone()],
        vec![vec![
            member(&membership.element, &membership.operands[0]),
            instantiate(predicate, &membership.element),
        ]],
    )
}

fn notin_subsetof(args: &[Term]) -> Checked<RuleSpec> {
    let membership = get_membership_spec(&args[0], true, "TLA.subsetOf", 2)?;
    let predicate = &membership.operands[1];
    ensure(predicate.kind() == TermKind::Lam)?;
    spec(
        vec![args[0].clone()],
        vec![
            vec![not(&member(&membership.element, &membership.operands[0]))],
            vec![not(&instantiate(predicate, &membership.element))],
        ],
    )
}

fn in_setofall(args: &[Term], is_negated: bool, checker: &mut Checker<'_>) -> Checked<RuleSpec> {
    let membership = get_membership_spec(&args[0], is_negated, "TLA.setOfAll", 2)?;
    let mapping = &membership.operands[1];
    ensure(mapping.kind() == TermKind::Lam)?;
    let exists = checker.bind(TermKind::Ex, "", |bound| {
        and(
            &member(bound, &membership.operands[0]),
            &equal(&membership.element, &instantiate(mapping, bound)),
        )
    });
    spec(
        vec![args[0].clone()],
        vec![vec![if is_negated { not(&exists) } else { exists }]],
    )
}

fn get_maps(checker: &mut Checker<'_>, membership: &Membership) -> Term {
    let fcn = &membership.element;
    checker.bind(TermKind::All, "", |bound| {
        imply(
            &member(bound, &membership.operands[0]),
            &member(&fapply(fcn, bound), &membership.operands[1]),
        )
    })
}

fn in_funcset(args: &[Term], checker: &mut Checker<'_>) -> Checked<RuleSpec> {
    let membership = get_membership_spec(&args[0], false, "TLA.FuncSet", 2)?;
    let fcn = &membership.element;
    let maps = get_maps(checker, &membership);
    spec(
        vec![args[0].clone()],
        vec![vec![
            app("TLA.isAFcn", vec![fcn.clone()]),
            equal(&domain(fcn), &membership.operands[0]),
            maps,
        ]],
    )
}

fn notin_funcset(args: &[Term], checker: &mut Checker<'_>) -> Checked<RuleSpec> {
    let membership = get_membership_spec(&args[0], true, "TLA.FuncSet", 2)?;
    let fcn = &membership.element;
    let maps = get_maps(checker, &membership);
    spec(
        vec![args[0].clone()],
        vec![
            vec![not(&app("TLA.isAFcn", vec![fcn.clone()]))],
            vec![not(&equal(&domain(fcn), &membership.operands[0]))],
            vec![not(&maps)],
        ],
    )
}

fn except_notin_funcset(args: &[Term]) -> Checked<RuleSpec> {
    let membership = get_membership_spec(&args[0], true, "TLA.FuncSet", 2)?;
    let except = expect_app(&membership.element, "TLA.except", Some(3))?;
    spec(
        vec![args[0].clone()],
        vec![
            vec![not(&member(&except[0], &membership.set))],
            vec![not(&member(&except[2], &membership.operands[1]))],
        ],
    )
}

// x = {} or {} = x, where `empty` is the side of the empty set.
fn set_equal_empty(args: &[Term], empty: usize, checker: &mut Checker<'_>) -> Checked<RuleSpec> {
    let sides = expect_app(&args[0], "=", Some(2))?;
    ensure(is_variable(&sides[empty], "TLA.emptyset"))?;
    let set = &sides[1 - empty];
    spec(
        vec![args[0].clone()],
        vec![vec![
            checker.bind(TermKind::All, "", |bound| not(&member(bound, set))),
        ]],
    )
}

fn cup_subseteq(args: &[Term], is_negated: bool) -> Checked<RuleSpec> {
    let atom = if is_negated {
        expect_not(&args[0])?
    } else {
        args[0].clone()
    };
    let sides = expect_app(&atom, "TLA.subseteq", Some(2))?;
    let union = expect_app(&sides[0], "TLA.cup", Some(2))?;
    let subsets = union
        .iter()
        .map(|inner| app("TLA.subseteq", vec![inner.clone(), sides[1].clone()]));
    spec(
        vec![args[0].clone()],
        if is_negated {
            subsets.map(|subset| vec![not(&subset)]).collect()
        } else {
            vec![subsets.collect()]
        },
    )
}

fn subseteq_cap(args: &[Term], is_negated: bool) -> Checked<RuleSpec> {
    let atom = if is_negated {
        expect_not(&args[0])?
    } else {
        args[0].clone()
    };
    let sides = expect_app(&atom, "TLA.subseteq", Some(2))?;
    let intersection = expect_app(&sides[1], "TLA.cap", Some(2))?;
    let subsets = intersection
        .iter()
        .map(|inner| app("TLA.subseteq", vec![sides[0].clone(), inner.clone()]));
    spec(
        vec![args[0].clone()],
        if is_negated {
            subsets.map(|subset| vec![not(&subset)]).collect()
        } else {
            vec![subsets.collect()]
        },
    )
}

/// `SET_RULES`.
pub fn set_rules(
    name: RuleName,
    args: &[Term],
    checker: &mut Checker<'_>,
    _uses: &[Term],
) -> Option<Checked<RuleSpec>> {
    Some(match name {
        RuleName::InEmptyset => in_emptyset(args),
        RuleName::InUpair => in_upair(args),
        RuleName::NotinUpair => notin_upair(args),
        RuleName::InAddElt => in_add_elt(args),
        RuleName::NotinAddElt => notin_add_elt(args),
        RuleName::InSet => in_set(args),
        RuleName::NotinSet => notin_set(args),
        RuleName::InSUBSET => in_subset(args, false),
        RuleName::NotinSUBSET => in_subset(args, true),
        RuleName::InUNION => in_union(args, false, checker),
        RuleName::NotinUNION => in_union(args, true, checker),
        RuleName::InCup => in_cup(args),
        RuleName::NotinCup => notin_cup(args),
        RuleName::InCap => in_cap(args),
        RuleName::NotinCap => notin_cap(args),
        RuleName::InSetminus => in_setminus(args),
        RuleName::NotinSetminus => notin_setminus(args),
        RuleName::InSubsetof => in_subsetof(args),
        RuleName::NotinSubsetof => notin_subsetof(args),
        RuleName::InSetofall => in_setofall(args, false, checker),
        RuleName::NotinSetofall => in_setofall(args, true, checker),
        RuleName::InFuncset => in_funcset(args, checker),
        RuleName::NotinFuncset => notin_funcset(args, checker),
        RuleName::ExceptNotinFuncset => except_notin_funcset(args),
        RuleName::Setequalempty => set_equal_empty(args, 1, checker),
        RuleName::Setemptyequal => set_equal_empty(args, 0, checker),
        RuleName::Setequal => get_set_equal_spec(&args[0], false, checker),
        RuleName::Notsetequal => get_set_equal_spec(&args[0], true, checker),
        RuleName::CupSubseteq => cup_subseteq(args, false),
        RuleName::NotCupSubseteq => cup_subseteq(args, true),
        RuleName::SubseteqCap => subseteq_cap(args, false),
        RuleName::NotSubseteqCap => subseteq_cap(args, true),
        _ => return None,
    })
}
