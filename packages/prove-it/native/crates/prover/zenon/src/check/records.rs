//! The checks of the TLA+ extension's rules for tuples and records, after the lemmas in Zenon.thy
//! that justify them.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use super::terms::{
    Checked, Checker, RuleSpec, Term, UncheckedError, app, domain, ensure, equal, expect_app,
    expect_not, fapply, get_pairs, get_string_text, make_natural, member, not, spec,
};
use crate::proof::RuleName;

/// The fields of a record or a set of records, whose labels must be distinct string literals.
pub fn get_fields(record: &Term, constructor: &str) -> Checked<Vec<(Term, Term)>> {
    let fields = get_pairs(&expect_app(record, constructor, None)?)?;
    let labels = fields
        .iter()
        .map(|field| get_string_text(&field.0))
        .collect::<Checked<Vec<_>>>()?;
    ensure(labels.iter().collect::<HashSet<_>>().len() == labels.len())?;
    Ok(fields)
}

fn get_labels(fields: &[(Term, Term)]) -> Term {
    app(
        "TLA.set",
        fields.iter().map(|field| field.0.clone()).collect(),
    )
}

fn get_record_inequality_spec(formula: &Term, is_record_right: bool) -> Checked<RuleSpec> {
    let sides = expect_app(&expect_not(formula)?, "=", Some(2))?;
    let other = if is_record_right {
        &sides[0]
    } else {
        &sides[1]
    };
    let fields = get_fields(
        if is_record_right {
            &sides[1]
        } else {
            &sides[0]
        },
        "TLA.record",
    )?;
    let mut branches = vec![
        vec![not(&app("TLA.isAFcn", vec![other.clone()]))],
        vec![not(&equal(&domain(other), &get_labels(&fields)))],
    ];
    branches.extend(
        fields
            .iter()
            .map(|field| vec![not(&equal(&fapply(other, &field.0), &field.1))]),
    );
    spec(vec![formula.clone()], branches)
}

// Checks that the formulas list exactly the expected ones, and returns them as branches.
fn expect_same_set(
    checker: &mut Checker<'_>,
    given: &[Term],
    expected: &[Term],
) -> Checked<Vec<Vec<Term>>> {
    let keys = expected
        .iter()
        .map(|formula| checker.get_top_key(formula))
        .collect::<Checked<HashSet<_>>>()?;
    ensure(given.len() == keys.len())?;
    for formula in given {
        ensure(keys.contains(&checker.get_top_key(formula)?))?;
    }
    Ok(given.iter().map(|formula| vec![formula.clone()]).collect())
}

fn get_values_by_label(fields: &[(Term, Term)]) -> Checked<HashMap<Rc<str>, Term>> {
    fields
        .iter()
        .map(|field| Ok((get_string_text(&field.0)?, field.1.clone())))
        .collect()
}

fn tuple_eq_match(args: &[Term]) -> Checked<RuleSpec> {
    let sides = expect_app(&args[0], "=", Some(2))?;
    let left = expect_app(&sides[0], "TLA.tuple", None)?;
    let right = expect_app(&sides[1], "TLA.tuple", None)?;
    ensure(left.len() == right.len())?;
    spec(
        vec![args[0].clone()],
        vec![
            left.iter()
                .zip(&right)
                .map(|(inner, other)| equal(inner, other))
                .collect(),
        ],
    )
}

fn tuple_eq_mismatch(args: &[Term]) -> Checked<RuleSpec> {
    let sides = expect_app(&args[0], "=", Some(2))?;
    ensure(
        expect_app(&sides[0], "TLA.tuple", None)?.len()
            != expect_app(&sides[1], "TLA.tuple", None)?.len(),
    )?;
    spec(vec![args[0].clone()], vec![])
}

fn in_product(args: &[Term]) -> Checked<RuleSpec> {
    let sides = expect_app(&args[0], "TLA.in", Some(2))?;
    let element = &sides[0];
    let components = expect_app(
        &expect_app(&sides[1], "TLA.Product", Some(1))?[0],
        "TLA.tuple",
        None,
    )?;
    let mut branch = vec![
        app("TLA.isASeq", vec![element.clone()]),
        equal(
            &app("TLA.Len", vec![element.clone()]),
            &make_natural(components.len()),
        ),
    ];
    branch.extend(
        components
            .iter()
            .enumerate()
            .map(|(index, inner)| member(&fapply(element, &make_natural(index + 1)), inner)),
    );
    spec(vec![args[0].clone()], vec![branch])
}

fn notin_product(args: &[Term]) -> Checked<RuleSpec> {
    let sides = expect_app(&expect_not(&args[0])?, "TLA.in", Some(2))?;
    let element = &sides[0];
    let components = expect_app(
        &expect_app(&sides[1], "TLA.Product", Some(1))?[0],
        "TLA.tuple",
        None,
    )?;
    let mut branches = vec![
        vec![not(&app("TLA.isASeq", vec![element.clone()]))],
        vec![not(&equal(
            &app("TLA.Len", vec![element.clone()]),
            &make_natural(components.len()),
        ))],
    ];
    branches.extend(components.iter().enumerate().map(|(index, inner)| {
        vec![not(&member(
            &fapply(element, &make_natural(index + 1)),
            inner,
        ))]
    }));
    spec(vec![args[0].clone()], branches)
}

fn tuple_notisaseq(args: &[Term]) -> Checked<RuleSpec> {
    expect_app(
        &expect_app(&expect_not(&args[0])?, "TLA.isASeq", Some(1))?[0],
        "TLA.tuple",
        None,
    )?;
    spec(vec![args[0].clone()], vec![])
}

fn record_eq_match(args: &[Term], checker: &mut Checker<'_>) -> Checked<RuleSpec> {
    let sides = expect_app(&args[0], "=", Some(2))?;
    let left = get_fields(&sides[0], "TLA.record")?;
    let right = get_fields(&sides[1], "TLA.record")?;
    let values_by_label = get_values_by_label(&right)?;
    let mut equalities = Vec::new();
    for field in &left {
        if let Some(other) = values_by_label.get(&get_string_text(&field.0)?) {
            equalities.push(equal(&field.1, other));
        }
    }
    let keys = equalities
        .iter()
        .map(|formula| checker.get_top_key(formula))
        .collect::<Checked<HashSet<_>>>()?;
    let given = &args[1..];
    for formula in given {
        ensure(keys.contains(&checker.get_top_key(formula)?))?;
    }
    spec(vec![args[0].clone()], vec![given.to_vec()])
}

fn record_eq_mismatch(args: &[Term]) -> Checked<RuleSpec> {
    let sides = expect_app(&args[0], "=", Some(2))?;
    let left_labels = get_fields(&sides[0], "TLA.record")?
        .iter()
        .map(|field| get_string_text(&field.0))
        .collect::<Checked<Vec<_>>>()?;
    let right_labels = get_fields(&sides[1], "TLA.record")?
        .iter()
        .map(|field| get_string_text(&field.0))
        .collect::<Checked<HashSet<_>>>()?;
    ensure(
        left_labels.len() != right_labels.len()
            || left_labels
                .iter()
                .any(|label| !right_labels.contains(label)),
    )?;
    spec(vec![args[0].clone()], vec![])
}

fn record_neq_match(args: &[Term], checker: &mut Checker<'_>) -> Checked<RuleSpec> {
    let sides = expect_app(&expect_not(&args[0])?, "=", Some(2))?;
    let left = get_fields(&sides[0], "TLA.record")?;
    let right = get_fields(&sides[1], "TLA.record")?;
    let values_by_label = get_values_by_label(&right)?;
    ensure(left.len() == right.len())?;
    let inequalities = left
        .iter()
        .map(|field| {
            let other = values_by_label
                .get(&get_string_text(&field.0)?)
                .ok_or(UncheckedError)?;
            Ok(not(&equal(&field.1, other)))
        })
        .collect::<Checked<Vec<_>>>()?;
    spec(
        vec![args[0].clone()],
        expect_same_set(checker, &args[1..], &inequalities)?,
    )
}

fn in_recordset(args: &[Term]) -> Checked<RuleSpec> {
    let sides = expect_app(&args[0], "TLA.in", Some(2))?;
    let element = &sides[0];
    let fields = get_fields(&sides[1], "TLA.recordset")?;
    let mut branch = vec![
        app("TLA.isAFcn", vec![element.clone()]),
        equal(&domain(element), &get_labels(&fields)),
    ];
    branch.extend(
        fields
            .iter()
            .map(|field| member(&fapply(element, &field.0), &field.1)),
    );
    spec(vec![args[0].clone()], vec![branch])
}

fn notin_recordset(args: &[Term]) -> Checked<RuleSpec> {
    let sides = expect_app(&expect_not(&args[0])?, "TLA.in", Some(2))?;
    let element = &sides[0];
    let fields = get_fields(&sides[1], "TLA.recordset")?;
    let mut branches = vec![
        vec![not(&app("TLA.isAFcn", vec![element.clone()]))],
        vec![not(&equal(&domain(element), &get_labels(&fields)))],
    ];
    branches.extend(
        fields
            .iter()
            .map(|field| vec![not(&member(&fapply(element, &field.0), &field.1))]),
    );
    spec(vec![args[0].clone()], branches)
}

fn record_notisafcn(args: &[Term]) -> Checked<RuleSpec> {
    expect_app(
        &expect_app(&expect_not(&args[0])?, "TLA.isAFcn", Some(1))?[0],
        "TLA.record",
        None,
    )?;
    spec(vec![args[0].clone()], vec![])
}

/// `RECORD_RULES`.
pub fn record_rules(
    name: RuleName,
    args: &[Term],
    checker: &mut Checker<'_>,
    _uses: &[Term],
) -> Option<Checked<RuleSpec>> {
    Some(match name {
        RuleName::TupleEqMatch => tuple_eq_match(args),
        RuleName::TupleEqMismatch => tuple_eq_mismatch(args),
        RuleName::InProduct => in_product(args),
        RuleName::NotinProduct => notin_product(args),
        RuleName::TupleNotisaseq => tuple_notisaseq(args),
        RuleName::RecordEqMatch => record_eq_match(args, checker),
        RuleName::RecordEqMismatch => record_eq_mismatch(args),
        RuleName::RecordNeqMatch => record_neq_match(args, checker),
        RuleName::NeqRecord => get_record_inequality_spec(&args[0], true),
        RuleName::RecordNeq => get_record_inequality_spec(&args[0], false),
        RuleName::InRecordset => in_recordset(args),
        RuleName::NotinRecordset => notin_recordset(args),
        RuleName::RecordNotisafcn => record_notisafcn(args),
        _ => return None,
    })
}
