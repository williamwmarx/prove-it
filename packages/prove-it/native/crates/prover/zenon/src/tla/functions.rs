// Ported from Zenon's ext_tla.ml, as shipped in tlapm. Copyright 2008 INRIA, see LICENSE.
//! The rules for functions: membership in a function set, isAFcn and function equality.

use crate::expr::Kind;
use crate::node::Priority;
use crate::proof::{Rule, RuleName};
use crate::tla::terms::{
    FUNCTION_CONSTRUCTORS, Item, Literal, domain, equal, fapply, is_constructor,
    make_extension_node, member,
};

pub fn get_function_set_nodes(literal: &Literal) -> Option<Vec<Item>> {
    let exprs = literal.context.exprs;
    let formula = &literal.formula;
    let is_negated = literal.is_negated;
    let node = |priority, rule, branches| make_extension_node(literal, priority, rule, branches);
    let relation = literal
        .relation
        .as_ref()
        .filter(|inner| inner.is_app("TLA.in"))?;
    let element = &relation.args[0];
    let set = &relation.args[1];
    if !set.is_app_with_arity("TLA.FuncSet", 2) {
        return None;
    }
    let fcn = element;
    let source = &set.args[0];
    let target = &set.args[1];
    let is_fcn = exprs.eapp("TLA.isAFcn", std::slice::from_ref(fcn));
    let has_domain = equal(exprs, &domain(exprs, fcn), source);
    let bound = exprs.new_var();
    let maps = exprs.eall(
        &bound,
        "",
        &exprs.eimply(
            &member(exprs, &bound, source),
            &member(exprs, &fapply(exprs, fcn, &bound), target),
        ),
    );
    if !is_negated {
        let rule = Rule::new(
            RuleName::InFuncset,
            vec![
                formula.clone(),
                is_fcn.clone(),
                has_domain.clone(),
                maps.clone(),
                fcn.clone(),
                source.clone(),
                target.clone(),
            ],
        );
        return Some(
            [
                node(
                    Priority::Arity,
                    rule.clone(),
                    vec![vec![is_fcn.clone(), has_domain.clone()]],
                ),
                node(
                    Priority::Instance(maps.clone()),
                    rule,
                    vec![vec![is_fcn, has_domain, maps]],
                ),
            ]
            .concat(),
        );
    }
    let not_fcn = exprs.enot(&is_fcn);
    let not_domain = exprs.enot(&has_domain);
    let not_maps = exprs.enot(&maps);
    let priority = if fcn.kind == Kind::App && FUNCTION_CONSTRUCTORS.contains(&&*fcn.symbol) {
        Priority::Arity
    } else {
        Priority::Instance(not_maps.clone())
    };
    let shortcut = if fcn.is_app_with_arity("TLA.except", 3) {
        node(
            Priority::Arity,
            Rule::new(
                RuleName::ExceptNotinFuncset,
                vec![
                    formula.clone(),
                    exprs.enot(&member(
                        exprs,
                        &fcn.args[0],
                        &exprs.eapp("TLA.FuncSet", &[source.clone(), target.clone()]),
                    )),
                    exprs.enot(&member(exprs, &fcn.args[2], target)),
                    fcn.args[0].clone(),
                    fcn.args[1].clone(),
                    fcn.args[2].clone(),
                    source.clone(),
                    target.clone(),
                ],
            ),
            vec![
                vec![exprs.enot(&member(
                    exprs,
                    &fcn.args[0],
                    &exprs.eapp("TLA.FuncSet", &[source.clone(), target.clone()]),
                ))],
                vec![exprs.enot(&member(exprs, &fcn.args[2], target))],
            ],
        )
    } else {
        vec![]
    };
    Some(
        [
            shortcut,
            node(
                priority,
                Rule::new(
                    RuleName::NotinFuncset,
                    vec![
                        formula.clone(),
                        not_fcn.clone(),
                        not_domain.clone(),
                        not_maps.clone(),
                        fcn.clone(),
                        source.clone(),
                        target.clone(),
                    ],
                ),
                vec![vec![not_fcn], vec![not_domain], vec![not_maps]],
            ),
        ]
        .concat(),
    )
}

pub fn get_function_nodes(literal: &Literal) -> Option<Vec<Item>> {
    let exprs = literal.context.exprs;
    let formula = &literal.formula;
    let is_negated = literal.is_negated;
    let atom = &literal.atom;
    let node = |priority, rule, branches| make_extension_node(literal, priority, rule, branches);
    if is_negated && atom.is_app_with_arity("TLA.isAFcn", 1) {
        let fcn = &atom.args[0];
        if fcn.is_app_with_arity("TLA.Fcn", 2) {
            return Some(node(
                Priority::Prop,
                Rule::new(
                    RuleName::NotisafcnFcn,
                    vec![formula.clone(), fcn.args[0].clone(), fcn.args[1].clone()],
                ),
                vec![],
            ));
        }
        if fcn.is_app_with_arity("TLA.except", 3) {
            return Some(node(
                Priority::Prop,
                Rule::new(
                    RuleName::NotisafcnExcept,
                    vec![
                        formula.clone(),
                        fcn.args[0].clone(),
                        fcn.args[1].clone(),
                        fcn.args[2].clone(),
                    ],
                ),
                vec![],
            ));
        }
        if fcn.is_app_with_arity("TLA.oneArg", 2) {
            return Some(node(
                Priority::Prop,
                Rule::new(
                    RuleName::NotisafcnOnearg,
                    vec![formula.clone(), fcn.args[0].clone(), fcn.args[1].clone()],
                ),
                vec![],
            ));
        }
        if fcn.is_app_with_arity("TLA.extend", 2) {
            return Some(node(
                Priority::Prop,
                Rule::new(
                    RuleName::NotisafcnExtend,
                    vec![formula.clone(), fcn.args[0].clone(), fcn.args[1].clone()],
                ),
                vec![],
            ));
        }
    }
    let relation = literal
        .relation
        .as_ref()
        .filter(|inner| inner.is_app("="))?;
    let left = &relation.args[0];
    let right = &relation.args[1];
    if !is_constructor(FUNCTION_CONSTRUCTORS, left) && !is_constructor(FUNCTION_CONSTRUCTORS, right)
    {
        return None;
    }
    let bound = exprs.new_var();
    let same_domain = equal(exprs, &domain(exprs, left), &domain(exprs, right));
    let same_value = equal(
        exprs,
        &fapply(exprs, left, &bound),
        &fapply(exprs, right, &bound),
    );
    if !is_negated {
        let is_fcn = exprs.eequiv(
            &exprs.eapp("TLA.isAFcn", std::slice::from_ref(left)),
            &exprs.eapp("TLA.isAFcn", std::slice::from_ref(right)),
        );
        let values = exprs.eall(&bound, "", &same_value);
        let result = exprs.eand(&exprs.eand(&is_fcn, &same_domain), &values);
        return Some(node(
            Priority::Instance(values),
            Rule::new(
                RuleName::Funequal,
                vec![formula.clone(), result.clone(), left.clone(), right.clone()],
            ),
            vec![vec![result]],
        ));
    }
    let values = exprs.eall(
        &bound,
        "",
        &exprs.eimply(&member(exprs, &bound, &domain(exprs, right)), &same_value),
    );
    let result = exprs.enot(&exprs.eand(
        &exprs.eand(
            &exprs.eand(
                &exprs.eapp("TLA.isAFcn", std::slice::from_ref(left)),
                &exprs.eapp("TLA.isAFcn", std::slice::from_ref(right)),
            ),
            &same_domain,
        ),
        &values,
    ));
    Some(node(
        Priority::Instance(values),
        Rule::new(
            RuleName::Notfunequal,
            vec![formula.clone(), result.clone(), left.clone(), right.clone()],
        ),
        vec![vec![result]],
    ))
}
