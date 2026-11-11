//! What Backend.Prep does to an obligation before a backend's frontend: normalize_expand, which
//! expands definitions, runs Expr.Elab.normalize and the frontend methods the obligation cites, then
//! trivial and flatten. A port of `src/prover/prep/normalize.ts`.
//!
//! The TypeScript's module-level `createContextMap`s live in thread-locals here, so they share each
//! mapped prefix of a context across obligations as the TypeScript's do.

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use crate::action::{ActionOptions, expand_action_operators, lambdify};
use crate::anonymize::{Anonymizer, AnonymizerHost, create_anonymizer};
use crate::equality::is_equal_expr;
use crate::errors::{ObligationError, Result};
use crate::expression::{
    Bound, BoundDomain, Builtin, Bullet, ContextMap, Defn, DefnCore, ExceptPoint, ExceptSpec, Expr,
    ExprCore, ExprProps, Field, Hyp, HypCore, Hyps, ObligationWarning, Quantifier, ScopeRef,
    Sequent, Visibility, apply_builtin, at, expr, get_children, map_children, map_except_specs,
    map_hyp, to_index,
};
use crate::pragma::OldMethod;
use crate::prep::enabled_axioms::implication_to_enabled;
use crate::prep::level_comparison::check_level_change;
use crate::prep::methods::{FoundMethods, find_methods};
use crate::proof::Counter;
use crate::substitution::{
    Substitution, SubstitutionNode, bump_by, cons_substitution, shift, shift_expr, substitute_expr,
    substitute_hyp,
};

type Step<State> = fn(&State, &Hyp, &Hyp) -> Result<(State, Option<Hyp>)>;

type SharedContextMap<State> = RefCell<ContextMap<State, Step<State>>>;

fn expand_definition(
    is_pragma_expanded: bool,
    current: &Substitution,
    hyp: &Hyp,
) -> Result<(Substitution, Option<Hyp>)> {
    let expanded = match &hyp.core {
        HypCore::Defn {
            definition,
            visibility,
            ..
        } => match &definition.core {
            DefnCore::Bpragma { body, .. } if is_pragma_expanded => Some(body),
            DefnCore::Operator { body, .. } if *visibility == Visibility::Visible => Some(body),
            _ => None,
        },
        _ => None,
    };
    match expanded {
        Some(body) => Ok((
            cons_substitution(substitute_expr(current, body)?, current.clone()),
            None,
        )),
        None => Ok((bump_by(1, current), Some(substitute_hyp(current, hyp)?))),
    }
}

thread_local! {
    static EXPAND_DEFINITIONS_AND_PRAGMAS: SharedContextMap<Substitution> =
        RefCell::new(ContextMap::new(shift(0), |current, hyp, _| {
            expand_definition(true, current, hyp)
        }));

    static EXPAND_DEFINITIONS: SharedContextMap<Substitution> =
        RefCell::new(ContextMap::new(shift(0), |current, hyp, _| {
            expand_definition(false, current, hyp)
        }));

    // let_normalize on each hypothesis, and whether the context so far is non_temporal.
    static NORMALIZE_LET_CONTEXT: SharedContextMap<bool> =
        RefCell::new(ContextMap::new(true, |is_context_non_temporal, hyp, _| {
            Ok((
                *is_context_non_temporal && get_visited_exprs(hyp).iter().all(is_non_temporal),
                Some(map_hyp(hyp, &mut normalize_let, Hyps::All)?),
            ))
        }));

    static NORMALIZE_EXCEPT_CONTEXT: SharedContextMap<()> =
        RefCell::new(ContextMap::new((), |_, hyp, _| {
            Ok(((), Some(map_hyp(hyp, &mut normalize_except, Hyps::All)?)))
        }));
}

/// Forgets the mapped contexts.
pub(crate) fn reset_caches() {
    for context_map in [&EXPAND_DEFINITIONS_AND_PRAGMAS, &EXPAND_DEFINITIONS] {
        context_map.with(|shared| shared.borrow_mut().clear());
    }
    NORMALIZE_LET_CONTEXT.with(|shared| shared.borrow_mut().clear());
    NORMALIZE_EXCEPT_CONTEXT.with(|shared| shared.borrow_mut().clear());
}

/// expand_defs: each visible operator definition and each pragma, whatever its visibility,
/// substitutes into the rest of the obligation and leaves the context. Toolbox.expand_defs leaves
/// the pragmas.
pub fn expand_defs(sequent: &Sequent, is_pragma_expanded: bool) -> Result<Sequent> {
    let expander = if is_pragma_expanded {
        &EXPAND_DEFINITIONS_AND_PRAGMAS
    } else {
        &EXPAND_DEFINITIONS
    };
    let expanded =
        expander.with(|context_map| context_map.borrow_mut().map(&sequent.context, None))?;
    Ok(Sequent {
        context: expanded.context,
        active: substitute_expr(&expanded.state, &sequent.active)?,
    })
}

const TEMPORAL_BUILTINS: [Builtin; 6] = [
    Builtin::BoxTrue,
    Builtin::BoxFalse,
    Builtin::Diamond,
    Builtin::Actplus,
    Builtin::Leadsto,
    Builtin::Cdot,
];

// The expressions of a hypothesis that Visit.iter visits, none for a hidden one.
fn get_visited_exprs(hyp: &Hyp) -> Vec<Expr> {
    match &hyp.core {
        HypCore::Fresh { domain, .. } => domain.iter().cloned().collect(),
        HypCore::Flex { .. } => Vec::new(),
        HypCore::Defn {
            definition,
            visibility,
            ..
        } => match &definition.core {
            DefnCore::Operator { body, .. } | DefnCore::Bpragma { body, .. }
                if *visibility != Visibility::Hidden =>
            {
                vec![body.clone()]
            }
            _ => Vec::new(),
        },
        HypCore::Fact {
            expression,
            visibility,
            ..
        } => {
            if *visibility == Visibility::Hidden {
                Vec::new()
            } else {
                vec![expression.clone()]
            }
        }
    }
}

// Elab.non_temporal: no temporal operator, but in hidden hypotheses.
fn is_non_temporal(expression: &Expr) -> bool {
    match &expression.core {
        ExprCore::Tsub { .. } | ExprCore::Fair { .. } => false,
        ExprCore::Apply { operator, .. } if matches!(&operator.core, ExprCore::Internal { builtin } if TEMPORAL_BUILTINS.contains(builtin)) => {
            false
        }
        ExprCore::Sequent { sequent } => {
            sequent
                .context
                .iter()
                .flat_map(get_visited_exprs)
                .all(|inner| is_non_temporal(&inner))
                && is_non_temporal(&sequent.active)
        }
        _ => get_children(expression).iter().all(is_non_temporal),
    }
}

// Elab.let_normalize: each LET definition is substituted into the rest of the LET.
fn normalize_let(expression: &Expr) -> Result<Expr> {
    let ExprCore::Let { definitions, body } = &expression.core else {
        return map_children(expression, &mut normalize_let);
    };
    let Some((definition, rest_definitions)) = definitions.split_first() else {
        return normalize_let(body);
    };
    let (DefnCore::Operator { body: operator, .. } | DefnCore::Bpragma { body: operator, .. }) =
        &definition.core
    else {
        return Err(ObligationError::proof(
            if matches!(definition.core, DefnCore::Instance { .. }) {
                "Found INSTANCE in Expr.Elab.let_normalize, all INSTANCE statements have been replaced with definitions in Module.Elab "
            } else {
                "Expr.Elab.let_normalize"
            },
        ));
    };
    let operator = normalize_let(operator)?;
    let rest = expression.with_core(ExprCore::Let {
        definitions: rest_definitions.to_vec(),
        body: body.clone(),
    });
    normalize_let(&substitute_expr(
        &cons_substitution(operator, shift(0)),
        &rest,
    )?)
}

fn get_access(base: &Expr, point: &ExceptPoint) -> Expr {
    match point {
        ExceptPoint::Dot(field) => at(
            ExprCore::Dot {
                expression: base.clone(),
                field: field.clone(),
            },
            base,
        ),
        ExceptPoint::Apply(expression) => at(
            ExprCore::FcnApp {
                function: base.clone(),
                args: vec![expression.clone()],
            },
            base,
        ),
    }
}

fn is_same_head(left: &ExceptPoint, right: &ExceptPoint) -> bool {
    match (left, right) {
        (ExceptPoint::Dot(left_field), ExceptPoint::Dot(right_field)) => left_field == right_field,
        (ExceptPoint::Apply(left_expression), ExceptPoint::Apply(right_expression)) => {
            is_equal_expr(left_expression, right_expression)
        }
        _ => false,
    }
}

// The field of a record constructor that a point names, as a field or as a string argument.
fn get_record_field<'record>(record: &'record Expr, point: &ExceptPoint) -> Option<&'record Field> {
    let name = match point {
        ExceptPoint::Dot(field) => Some(field),
        ExceptPoint::Apply(expression) => match &expression.core {
            ExprCore::String { value } => Some(value),
            _ => None,
        },
    };
    match (&record.core, name) {
        (ExprCore::Record { fields }, Some(name)) => {
            fields.iter().find(|field| field.name == *name)
        }
        _ => None,
    }
}

// Elab.except_normalize: [f EXCEPT p1 = b1, ...] folds left to right into f, sharing each prefix of
// adjacent updates and updating a record constructor in place on a field it has.
fn normalize_except(expression: &Expr) -> Result<Expr> {
    let ExprCore::Except { function, specs } = &expression.core else {
        return map_children(expression, &mut normalize_except);
    };
    let function = normalize_except(function)?;
    let specs = map_except_specs(specs, &mut normalize_except)?;
    Ok(apply_except_specs(expression, &function, &specs))
}

fn select_point(base: &Expr, point: &ExceptPoint) -> Expr {
    get_record_field(base, point)
        .map_or_else(|| get_access(base, point), |field| field.value.clone())
}

fn update_point(except: &Expr, base: &Expr, point: &ExceptPoint, value: Expr) -> Expr {
    let field = match (&base.core, get_record_field(base, point)) {
        (ExprCore::Record { fields }, Some(field)) => Some((fields, field)),
        _ => None,
    };
    let Some((fields, field)) = field else {
        return at(
            ExprCore::Except {
                function: base.clone(),
                specs: vec![ExceptSpec {
                    trail: vec![point.clone()],
                    value,
                }],
            },
            except,
        );
    };
    let fields = fields
        .iter()
        .map(|entry| {
            if entry.name == field.name {
                Field {
                    name: entry.name.clone(),
                    value: value.clone(),
                }
            } else {
                entry.clone()
            }
        })
        .collect();
    at(ExprCore::Record { fields }, base)
}

fn apply_except_specs(except: &Expr, base: &Expr, specs: &[ExceptSpec]) -> Expr {
    let Some((first, others)) = specs.split_first() else {
        return base.clone();
    };
    let Some(head) = first.trail.first() else {
        return apply_except_specs(except, &first.value, others);
    };
    let count = specs
        .iter()
        .position(|spec| {
            spec.trail
                .first()
                .is_none_or(|point| !is_same_head(point, head))
        })
        .unwrap_or(specs.len());
    let tails = specs[..count]
        .iter()
        .map(|spec| ExceptSpec {
            trail: spec.trail[1..].to_vec(),
            value: spec.value.clone(),
        })
        .collect::<Vec<_>>();
    let selected = apply_except_specs(except, &select_point(base, head), &tails);
    apply_except_specs(
        except,
        &update_point(except, base, head, selected),
        &specs[count..],
    )
}

/// Elab.normalize, on an obligation as a sequent expression, as Prep.normalize_expr calls it: LET
/// definitions inline, and the updates of an EXCEPT fold into the function they update.
pub fn normalize_sequent(sequent: &Sequent) -> Result<Sequent> {
    let inlined = NORMALIZE_LET_CONTEXT
        .with(|context_map| context_map.borrow_mut().map(&sequent.context, None))?;
    let active = normalize_let(&sequent.active)?;
    if inlined.state && is_non_temporal(&sequent.active) {
        let context = NORMALIZE_EXCEPT_CONTEXT.with(|context_map| {
            context_map
                .borrow_mut()
                .map(&sequent.context, Some(&inlined.context))
        })?;
        return Ok(Sequent {
            context: context.context,
            active: normalize_except(&active)?,
        });
    }
    Ok(Sequent {
        context: inlined.context,
        active,
    })
}

/// The anonymizer's instance expander and warning sink: Expr.Anon's anon, which only meets the names
/// that lambdification binds, so it never expands an instance.
struct LambdifyHost;

impl AnonymizerHost for LambdifyHost {
    fn expand_instance(
        &mut self,
        _anonymizer: &mut Anonymizer,
        _scope: &ScopeRef,
        _definition: &Defn,
    ) -> Result<Vec<Defn>> {
        Err(ObligationError::assert_failure())
    }

    fn on_warning(&mut self, _warning: ObligationWarning) {}
}

// expand_enabled_cdot: the first frontend the methods cite, in tlapm's order, transforms the
// obligation. Its soundness checks throw a TlaProverError, as tlapm then runs no backend.
fn expand_enabled_cdot(sequent: Sequent, frontends: &[String]) -> Result<Sequent> {
    let has = |name: &str| frontends.iter().any(|frontend| frontend == name);
    let is_enabled = has("expandenabled");
    let is_cdot = has("expandcdot");
    let is_auto_use = has("autouse");
    let is_lambdify = has("lambdify");
    if !is_enabled && !is_cdot && !is_lambdify {
        if has("levelcomparison") {
            return check_level_change(&sequent);
        }
        if has("enabledaxioms") {
            return implication_to_enabled(&sequent);
        }
        return Ok(sequent);
    }
    // Expr.Anon's anon, which only meets the names that lambdification binds.
    let mut anonymizer = create_anonymizer(Rc::new(Counter {
        value: Cell::new(0),
    }));
    let expression = expr(ExprCore::Sequent { sequent });
    let result = if is_enabled || is_cdot {
        expand_action_operators(
            &mut anonymizer,
            &mut LambdifyHost,
            &mut |_| {},
            &None,
            &expression,
            ActionOptions {
                is_enabled,
                is_cdot,
                is_auto_use,
            },
        )?
    } else {
        lambdify(
            &mut anonymizer,
            &mut LambdifyHost,
            &mut |_| {},
            &None,
            &expression,
            Some(ActionOptions {
                is_enabled: true,
                is_cdot: true,
                is_auto_use,
            }),
        )?
    };
    match &result.core {
        ExprCore::Sequent { sequent } => Ok(sequent.clone()),
        _ => Err(ObligationError::assert_failure()),
    }
}

/// normalize_expand: expand_defs, Elab.normalize, then the frontends the obligation cites.
/// `methods` defaults to `find_methods` of the obligation.
pub fn normalize_expand(
    sequent: &Sequent,
    method: Option<&OldMethod>,
    methods: Option<&FoundMethods>,
) -> Result<Sequent> {
    let found;
    let methods = match methods {
        Some(methods) => methods,
        None => {
            found = find_methods(sequent, method)?;
            &found
        }
    };
    expand_enabled_cdot(
        normalize_sequent(&expand_defs(sequent, true)?)?,
        &methods.frontends,
    )
}

/// trivial: the goal is TRUE, or find_fact finds it as a hypothesis, visible or not: a fact
/// alpha-equivalent to it, or the x \in S of a declaration NEW x \in S.
pub fn is_trivial(sequent: &Sequent) -> Result<bool> {
    if matches!(
        sequent.active.core,
        ExprCore::Internal {
            builtin: Builtin::TRUE
        }
    ) {
        return Ok(true);
    }
    let length = to_index(sequent.context.len());
    for (index, hyp) in sequent.context.iter().enumerate() {
        let index = to_index(index);
        let is_found = match &hyp.core {
            HypCore::Fact { expression, .. } => {
                is_equal_expr(expression, &*shift_expr(index - length, &sequent.active)?)
            }
            HypCore::Fresh {
                domain: Some(domain),
                ..
            } => {
                let membership = apply_builtin(
                    Builtin::Mem,
                    vec![expr(ExprCore::Ix { index: 1 }), shift_expr(1, domain)?],
                    &ExprProps::default(),
                );
                is_equal_expr(
                    &membership,
                    &*shift_expr(index + 1 - length, &sequent.active)?,
                )
            }
            _ => false,
        };
        if is_found {
            return Ok(true);
        }
    }
    Ok(false)
}

fn is_unbounded(bound: &Bound) -> bool {
    matches!(bound.domain, BoundDomain::NoDomain)
}

// extract_equalities: the equalities in a conjunction, apart from the rest of it.
fn extract_equalities(expression: &Expr) -> (Vec<Expr>, Option<Expr>) {
    match &expression.core {
        ExprCore::List {
            bullet: Bullet::And | Bullet::Refs,
            items,
        } => {
            let parts = items.iter().map(extract_equalities).collect::<Vec<_>>();
            let equalities = parts
                .iter()
                .flat_map(|part| part.0.iter().cloned())
                .collect();
            let mut rest = parts
                .iter()
                .filter_map(|part| part.1.clone())
                .collect::<Vec<_>>();
            if rest.len() <= 1 {
                return (equalities, rest.pop());
            }
            return (
                equalities,
                Some(expression.with_core(ExprCore::List {
                    bullet: Bullet::And,
                    items: rest,
                })),
            );
        }
        ExprCore::Apply { operator, args } => {
            if let ExprCore::Internal { builtin } = operator.core {
                if builtin == Builtin::Conj && args.len() == 2 {
                    let left = extract_equalities(&args[0]);
                    let right = extract_equalities(&args[1]);
                    let equalities = [left.0, right.0].concat();
                    return match (left.1, right.1) {
                        (Some(left_rest), Some(right_rest)) => (
                            equalities,
                            Some(expression.with_core(ExprCore::Apply {
                                operator: operator.clone(),
                                args: vec![left_rest, right_rest],
                            })),
                        ),
                        (left_rest, right_rest) => (equalities, left_rest.or(right_rest)),
                    };
                }
                if builtin == Builtin::Eq {
                    return (vec![expression.clone()], None);
                }
            }
        }
        ExprCore::Internal {
            builtin: Builtin::TRUE,
        } => return (Vec::new(), None),
        ExprCore::Quant {
            quantifier: Quantifier::Forall,
            bounds,
            body,
        } if bounds.iter().all(is_unbounded) => {
            let extracted = extract_equalities(body);
            let quantify = |inner: &Expr, from: &Expr| {
                at(
                    ExprCore::Quant {
                        quantifier: Quantifier::Forall,
                        bounds: bounds.clone(),
                        body: inner.clone(),
                    },
                    from,
                )
            };
            return (
                extracted
                    .0
                    .iter()
                    .map(|equality| quantify(equality, equality))
                    .collect(),
                extracted.1.map(|rest| quantify(&rest, expression)),
            );
        }
        _ => {}
    }
    (Vec::new(), Some(expression.clone()))
}

/// flatten: each visible fact becomes the rest of it, then its equalities.
pub fn flatten(sequent: &Sequent) -> Result<Sequent> {
    let mut context = Vec::new();
    let mut substitution = shift(0);
    for hyp in &sequent.context {
        let HypCore::Fact {
            expression,
            visibility: visibility @ Visibility::Visible,
            time,
            use_location,
        } = &hyp.core
        else {
            context.push(substitute_hyp(&substitution, hyp)?);
            substitution = bump_by(1, &substitution);
            continue;
        };
        let extracted = extract_equalities(expression);
        let facts = extracted
            .1
            .into_iter()
            .chain(extracted.0)
            .collect::<Vec<_>>();
        for (index, fact) in facts.iter().enumerate() {
            context.push(hyp.with_core(HypCore::Fact {
                expression: shift_expr(to_index(index), &substitute_expr(&substitution, fact)?)?,
                visibility: *visibility,
                time: *time,
                use_location: use_location.clone(),
            }));
        }
        substitution = Rc::new(SubstitutionNode::Compose {
            outer: shift(to_index(facts.len()) - 1),
            inner: bump_by(1, &substitution),
        });
    }
    Ok(Sequent {
        context,
        active: substitute_expr(&substitution, &sequent.active)?,
    })
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::*;
    use crate::prep::fingerprint::tests::{describe, parse_sequent};

    /// An outcome as the TypeScript script prints it: the result, or `!` and the error, on one line.
    fn print_outcome<Value>(result: Result<Value>, print: impl Fn(Value) -> String) -> String {
        match result {
            Ok(value) => print(value),
            Err(error) => format!("!{}", describe::<()>(Err(error)).replace('\n', "\\n")),
        }
    }

    fn print_sequent(sequent: Sequent) -> String {
        format!("{sequent:?}")
    }

    fn read_method(header: &str) -> Option<OldMethod> {
        if header == "-" {
            return None;
        }
        let parts = header.split('|').collect::<Vec<_>>();
        Some(OldMethod {
            name: parts[0].to_owned(),
            tactic: Some(parts[1].to_owned()).filter(|tactic| !tactic.is_empty()),
            timeout: parts[2].parse().ok(),
        })
    }

    fn get_found(frontends: &[&str]) -> FoundMethods {
        FoundMethods {
            frontends: frontends.iter().map(|name| (*name).to_owned()).collect(),
            provers: Vec::new(),
        }
    }

    /// Checks one case: the obligation's method (`-` for none), the sequent, then a line per
    /// outcome, `key value`, where a value `=other` repeats the input's (`in`) or an earlier
    /// outcome's. `fm` is the frontends `findMethods` finds; `ed` is `expandDefs` without pragmas;
    /// `ns` `normalizeSequent` after `expandDefs`; `ne` `normalizeExpand`, and `tr` and `fl`
    /// `isTrivial` and `flatten` of it; `xe`, `xc` and `xl` `normalizeExpand` with the frontends
    /// ExpandENABLED and AutoUSE, ExpandCdot, and Lambdify. A sequent compares as the sequent its
    /// JSON reads back to.
    ///
    /// The JSON reader leaves out a pragma's methods, so for an obligation without a method of its
    /// own, `fm` stands for what `find_methods` would find; one with a method takes the default path.
    fn check_case(case: &str, failures: &mut Vec<String>) {
        let mut lines = case.lines();
        let header = lines.next().unwrap_or_default();
        let input = lines.next().unwrap_or_default();
        let method = read_method(header);
        let sequent = parse_sequent(input);
        let mut values = HashMap::from([("in", input)]);
        let outcomes = lines
            .map(|line| {
                let (key, value) = line.split_once(' ').unwrap_or((line, ""));
                let value = value
                    .strip_prefix('=')
                    .map_or(value, |reference| values[reference]);
                values.insert(key, value);
                (key, value)
            })
            .collect::<Vec<_>>();
        let cited = values.get("fm").copied().unwrap_or_default();
        let found = get_found(
            &cited
                .split(',')
                .filter(|name| !name.is_empty())
                .collect::<Vec<_>>(),
        );
        let expanded = normalize_expand(
            &sequent,
            method.as_ref(),
            method.is_none().then_some(&found),
        );
        for (key, wanted) in outcomes {
            let actual = match key {
                "fm" if method.is_none() => continue,
                "fm" => print_outcome(find_methods(&sequent, method.as_ref()), |found| {
                    found.frontends.join(",")
                }),
                "ed" => print_outcome(expand_defs(&sequent, false), print_sequent),
                "ns" => print_outcome(
                    expand_defs(&sequent, true).and_then(|inner| normalize_sequent(&inner)),
                    print_sequent,
                ),
                "ne" => print_outcome(expanded.clone(), print_sequent),
                "tr" => print_outcome(
                    expanded.clone().and_then(|inner| is_trivial(&inner)),
                    |value| value.to_string(),
                ),
                "fl" => print_outcome(
                    expanded.clone().and_then(|inner| flatten(&inner)),
                    print_sequent,
                ),
                _ => {
                    let frontends = match key {
                        "xe" => get_found(&["expandenabled", "autouse"]),
                        "xc" => get_found(&["expandcdot"]),
                        "xl" => get_found(&["lambdify"]),
                        _ => panic!("unknown outcome {key}"),
                    };
                    print_outcome(
                        normalize_expand(&sequent, method.as_ref(), Some(&frontends)),
                        print_sequent,
                    )
                }
            };
            let is_sequent = !matches!(key, "fm" | "tr") && !wanted.starts_with('!');
            let wanted = if is_sequent {
                print_sequent(parse_sequent(wanted))
            } else {
                wanted.to_owned()
            };
            if wanted != actual {
                failures.push(format!(
                    "{key}:\n  wanted {wanted}\n  actual {actual}\n  {header} {input}"
                ));
            }
        }
    }

    fn check_cases(text: &str) -> usize {
        let mut failures = Vec::new();
        let cases = text
            .split("\n= ")
            .filter(|case| !case.trim().is_empty())
            .collect::<Vec<_>>();
        for case in &cases {
            check_case(case.trim_start().trim_start_matches("= "), &mut failures);
        }
        assert!(
            failures.is_empty(),
            "{} failures:\n{}",
            failures.len(),
            failures.join("\n")
        );
        cases.len()
    }

    /// Obligations of the tlapm corpus, one for each kind of outcome, without the hypotheses
    /// nothing refers to, then synthetic ones for the EXCEPT, LET, trivial and flatten edge cases.
    /// The outcomes come from running `normalize.ts` under Bun on these sequents.
    const CASES: &str = r##"
= isabelle|(auto intro: inIrrefl)|
{"context":[],"active":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"S","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Quant","quantifier":"Exists","bounds":[{"name":"x","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Notmem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}}}}
fm 
ed =in
ns =in
ne =in
tr false
fl =in
xe =in
xc =in
xl =in
= -
{"context":[],"active":{"kind":"Internal","builtin":"TRUE"}}
fm 
ed =in
ns =in
ne =in
tr true
fl =in
xe =in
xc =in
xl =in
= -
{"context":[{"kind":"Flex","name":"Y"},{"kind":"Defn","definition":{"kind":"Operator","name":"P","body":{"kind":"Lambda","params":[{"name":"a","shape":0},{"name":"x","shape":0}],"body":{"kind":"If","condition":{"kind":"Ix","index":3},"consequent":{"kind":"Ix","index":1},"alternative":{"kind":"Ix","index":1}}}},"whereDefined":"User","visibility":"Visible","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"<1>1","body":{"kind":"List","bullet":"Refs","items":[]}},"whereDefined":{"kind":"Proof","time":"Always"},"visibility":"Visible","isLocal":true}],"active":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"z","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":3},"args":[{"kind":"Ix","index":4},{"kind":"Ix","index":1}]}]},{"kind":"Ix","index":1}]}}}
fm 
ed {"context":[{"kind":"Flex","name":"Y"}],"active":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"z","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"If","condition":{"kind":"Ix","index":2},"consequent":{"kind":"Ix","index":1},"alternative":{"kind":"Ix","index":1}}]},{"kind":"Ix","index":1}]}}}
ns =ed
ne =ed
tr false
fl =ed
xe =ed
xc =ed
xl =ed
= -
{"context":[{"kind":"Defn","definition":{"kind":"Bpragma","name":"ENABLEDaxioms","body":{"kind":"Internal","builtin":"TRUE"},"methods":[[{"hint":"prover","value":{"kind":"String","value":"enabledaxioms"}}]]},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Flex","name":"x"},{"kind":"Flex","name":"y"},{"kind":"Defn","definition":{"kind":"Operator","name":"P","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Num","integer":"1","fraction":""}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"A","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]},{"kind":"Num","integer":"1","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]},{"kind":"Num","integer":"1","fraction":""}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"<1>1","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":2},{"kind":"Internal","builtin":"BOOLEAN"}]}},"whereDefined":{"kind":"Proof","time":"Now"},"visibility":"Visible","isLocal":true},{"kind":"Defn","definition":{"kind":"Operator","name":"<1>2","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":2},{"kind":"Internal","builtin":"BOOLEAN"}]}},"whereDefined":{"kind":"Proof","time":"Now"},"visibility":"Visible","isLocal":true},{"kind":"Defn","definition":{"kind":"Operator","name":"<1>3","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":4},{"kind":"Ix","index":3}]}]}},"whereDefined":{"kind":"Proof","time":"Now"},"visibility":"Visible","isLocal":true},{"kind":"Fact","expression":{"kind":"Ix","index":3},"visibility":"Visible","time":"Now"},{"kind":"Fact","expression":{"kind":"Ix","index":3},"visibility":"Visible","time":"Now"},{"kind":"Fact","expression":{"kind":"Ix","index":3},"visibility":"Visible","time":"Now"},{"kind":"Fact","expression":{"kind":"Ix","index":11},"visibility":"Visible","time":"Always"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":9},{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Ix","index":8}]}]}}
fm enabledaxioms
ed {"context":[{"kind":"Defn","definition":{"kind":"Bpragma","name":"ENABLEDaxioms","body":{"kind":"Internal","builtin":"TRUE"},"methods":[[{"hint":"prover","value":{"kind":"String","value":"enabledaxioms"}}]]},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Flex","name":"x"},{"kind":"Flex","name":"y"},{"kind":"Defn","definition":{"kind":"Operator","name":"P","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Num","integer":"1","fraction":""}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"A","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]},{"kind":"Num","integer":"1","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]},{"kind":"Num","integer":"1","fraction":""}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":2},{"kind":"Internal","builtin":"BOOLEAN"}]},"visibility":"Visible","time":"Now"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":2},{"kind":"Internal","builtin":"BOOLEAN"}]},"visibility":"Visible","time":"Now"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":4},{"kind":"Ix","index":3}]}]},"visibility":"Visible","time":"Now"},{"kind":"Fact","expression":{"kind":"Ix","index":8},"visibility":"Visible","time":"Always"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":6},{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Ix","index":5}]}]}}
ns {"context":[{"kind":"Flex","name":"x"},{"kind":"Flex","name":"y"},{"kind":"Defn","definition":{"kind":"Operator","name":"P","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Num","integer":"1","fraction":""}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"A","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]},{"kind":"Num","integer":"1","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]},{"kind":"Num","integer":"1","fraction":""}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":2},{"kind":"Internal","builtin":"BOOLEAN"}]},"visibility":"Visible","time":"Now"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":2},{"kind":"Internal","builtin":"BOOLEAN"}]},"visibility":"Visible","time":"Now"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":4},{"kind":"Ix","index":3}]}]},"visibility":"Visible","time":"Now"},{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":6},{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Ix","index":5}]}]}}
ne {"context":[{"kind":"Flex","name":"x"},{"kind":"Flex","name":"y"},{"kind":"Defn","definition":{"kind":"Operator","name":"P","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Num","integer":"1","fraction":""}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"A","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]},{"kind":"Num","integer":"1","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]},{"kind":"Num","integer":"1","fraction":""}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":2},{"kind":"Internal","builtin":"BOOLEAN"}]},"visibility":"Visible","time":"Now"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":2},{"kind":"Internal","builtin":"BOOLEAN"}]},"visibility":"Visible","time":"Now"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":4},{"kind":"Ix","index":3}]}]},"visibility":"Visible","time":"Now"},{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"}],"active":{"kind":"Internal","builtin":"TRUE"}}
tr true
fl {"context":[{"kind":"Flex","name":"x"},{"kind":"Flex","name":"y"},{"kind":"Defn","definition":{"kind":"Operator","name":"P","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Num","integer":"1","fraction":""}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"A","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]},{"kind":"Num","integer":"1","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]},{"kind":"Num","integer":"1","fraction":""}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":2},{"kind":"Internal","builtin":"BOOLEAN"}]},"visibility":"Visible","time":"Now"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":2},{"kind":"Internal","builtin":"BOOLEAN"}]},"visibility":"Visible","time":"Now"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":4},{"kind":"Ix","index":3}]}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Internal","builtin":"TRUE"}}
xe {"context":[{"kind":"Flex","name":"x"},{"kind":"Flex","name":"y"},{"kind":"Defn","definition":{"kind":"Operator","name":"P","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Num","integer":"1","fraction":""}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"A","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]},{"kind":"Num","integer":"1","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]},{"kind":"Num","integer":"1","fraction":""}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":2},{"kind":"Internal","builtin":"BOOLEAN"}]},"visibility":"Visible","time":"Now"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":2},{"kind":"Internal","builtin":"BOOLEAN"}]},"visibility":"Visible","time":"Now"},{"kind":"Fact","expression":{"kind":"Quant","quantifier":"Exists","bounds":[{"name":"y#enabled#prime1","level":"Constant","domain":{"kind":"NoDomain"}},{"name":"x#enabled#prime1","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":6},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"1","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Num","integer":"1","fraction":""}]}]}]}},"visibility":"Visible","time":"Now"},{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":6},{"kind":"Quant","quantifier":"Exists","bounds":[{"name":"y#enabled#prime1","level":"Constant","domain":{"kind":"NoDomain"}},{"name":"x#enabled#prime1","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"1","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Num","integer":"1","fraction":""}]}]}}]}}
xc !TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure
xl !TlaProverError|Hidden definition of operator `A` needs expansion for soundly expanding the operators `ENABLED` and `\cdot` (using rigid quantification).\nThe expansion of the operators `ENABLED` and `\cdot` has been activated with the the proof directives `ExpandENABLED` and `ExpandCdot` from the module `TLAPS`.\nThe operator `A` is defined at: \n	<unknown location>\nand the operator `A` occurs at: \n	<unknown location>\nUsing the proof directive `AutoUSE` from the module `TLAPS`, or `BY DEF A` is expected to avoid this error.\n|
= -
{"context":[{"kind":"Defn","definition":{"kind":"Bpragma","name":"ExpandENABLED","body":{"kind":"Internal","builtin":"TRUE"},"methods":[[{"hint":"prover","value":{"kind":"String","value":"expandenabled"}}]]},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Defn","definition":{"kind":"Bpragma","name":"AutoUSE","body":{"kind":"Internal","builtin":"TRUE"},"methods":[[{"hint":"prover","value":{"kind":"String","value":"autouse"}}]]},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Flex","name":"x"},{"kind":"Defn","definition":{"kind":"Operator","name":"R","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Fact","expression":{"kind":"Ix","index":4},"visibility":"Visible","time":"Always"},{"kind":"Fact","expression":{"kind":"Ix","index":4},"visibility":"Visible","time":"Always"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Ix","index":3}]}}
fm expandenabled,autouse
ed =in
ns {"context":[{"kind":"Flex","name":"x"},{"kind":"Defn","definition":{"kind":"Operator","name":"R","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"},{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Ix","index":3}]}}
ne {"context":[{"kind":"Flex","name":"x"},{"kind":"Defn","definition":{"kind":"Operator","name":"R","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"},{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"}],"active":{"kind":"Quant","quantifier":"Exists","bounds":[{"name":"x#enabled#prime1","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Ix","index":1}}}
tr false
fl {"context":[{"kind":"Flex","name":"x"},{"kind":"Defn","definition":{"kind":"Operator","name":"R","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false}],"active":{"kind":"Quant","quantifier":"Exists","bounds":[{"name":"x#enabled#prime1","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Ix","index":1}}}
xe =ne
xc !TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure
xl !TlaProverError|Hidden definition of operator `R` needs expansion for soundly expanding the operators `ENABLED` and `\cdot` (using rigid quantification).\nThe expansion of the operators `ENABLED` and `\cdot` has been activated with the the proof directives `ExpandENABLED` and `ExpandCdot` from the module `TLAPS`.\nThe operator `R` is defined at: \n	<unknown location>\nand the operator `R` occurs at: \n	<unknown location>\nUsing the proof directive `AutoUSE` from the module `TLAPS`, or `BY DEF R` is expected to avoid this error.\n|
= -
{"context":[{"kind":"Defn","definition":{"kind":"Bpragma","name":"ExpandCdot","body":{"kind":"Internal","builtin":"TRUE"},"methods":[[{"hint":"prover","value":{"kind":"String","value":"expandcdot"}}]]},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Fact","expression":{"kind":"Ix","index":1},"visibility":"Visible","time":"Always"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Cdot"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Internal","builtin":"TRUE"}]},{"kind":"Internal","builtin":"TRUE"}]}}
fm expandcdot
ed =in
ns {"context":[{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Cdot"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Internal","builtin":"TRUE"}]},{"kind":"Internal","builtin":"TRUE"}]}}
ne !TlaProverError|Expr.Action|
xe !TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure
xc !TlaProverError|Expr.Action|
xl {"context":[{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"}],"active":{"kind":"Apply","operator":{"kind":"Opaque","name":"CdotWrapper"},"args":[{"kind":"Lambda","params":[{"name":"r#0","shape":0}],"body":{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Opaque","name":"EnabledWrapper"},"args":[{"kind":"Lambda","params":[{"name":"r#0","shape":0}],"body":{"kind":"Internal","builtin":"TRUE"}}]},{"kind":"Internal","builtin":"TRUE"}]}}]}}
= -
{"context":[{"kind":"Defn","definition":{"kind":"Bpragma","name":"ExpandENABLED","body":{"kind":"Internal","builtin":"TRUE"},"methods":[[{"hint":"prover","value":{"kind":"String","value":"expandenabled"}}]]},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Fact","expression":{"kind":"Ix","index":1},"visibility":"Visible","time":"Always"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Cdot"},"args":[{"kind":"Internal","builtin":"TRUE"},{"kind":"Internal","builtin":"TRUE"}]}]}}
fm expandenabled
ed =in
ns {"context":[{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Cdot"},"args":[{"kind":"Internal","builtin":"TRUE"},{"kind":"Internal","builtin":"TRUE"}]}]}}
ne !TlaProverError|Expr.Action|
xe !TlaProverError|Expr.Action|
xc !TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure
xl {"context":[{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"}],"active":{"kind":"Apply","operator":{"kind":"Opaque","name":"EnabledWrapper"},"args":[{"kind":"Lambda","params":[{"name":"r#0","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Opaque","name":"CdotWrapper"},"args":[{"kind":"Lambda","params":[{"name":"r#0","shape":0}],"body":{"kind":"List","bullet":"And","items":[{"kind":"Internal","builtin":"TRUE"},{"kind":"Internal","builtin":"TRUE"}]}}]}}]}}
= -
{"context":[{"kind":"Flex","name":"x"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Cdot"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"0","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Num","integer":"1","fraction":""}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Cdot"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"1","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Num","integer":"2","fraction":""}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"2","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Num","integer":"3","fraction":""}]}]}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Cdot"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"0","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Num","integer":"1","fraction":""}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"1","fraction":""}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Num","integer":"3","fraction":""}]}]}]}}
fm 
ed =in
ns =in
ne =in
tr false
fl =in
xe !TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure
xc {"context":[{"kind":"Flex","name":"x"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Quant","quantifier":"Exists","bounds":[{"name":"x#enabled#prime1","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Num","integer":"0","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"1","fraction":""}]}]},{"kind":"Quant","quantifier":"Exists","bounds":[{"name":"x#enabled#prime2","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Num","integer":"1","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"2","fraction":""}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"2","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]},{"kind":"Num","integer":"3","fraction":""}]}]}]}}]}},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Quant","quantifier":"Exists","bounds":[{"name":"x#enabled#prime1","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Num","integer":"0","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"1","fraction":""}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"1","fraction":""}]}]}},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Num","integer":"3","fraction":""}]}]}]}}
xl {"context":[{"kind":"Flex","name":"x"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Opaque","name":"CdotWrapper"},"args":[{"kind":"Lambda","params":[{"name":"r#0","shape":0}],"body":{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Num","integer":"0","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"1","fraction":""}]}]},{"kind":"Apply","operator":{"kind":"Opaque","name":"CdotWrapper"},"args":[{"kind":"Lambda","params":[{"name":"r#0","shape":0}],"body":{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Num","integer":"1","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"2","fraction":""}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"2","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]},{"kind":"Num","integer":"3","fraction":""}]}]}]}}]}]}}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Opaque","name":"CdotWrapper"},"args":[{"kind":"Lambda","params":[{"name":"r#0","shape":0}],"body":{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Num","integer":"0","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"1","fraction":""}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"1","fraction":""}]}]}}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Num","integer":"3","fraction":""}]}]}]}}
= -
{"context":[{"kind":"Flex","name":"x"},{"kind":"Defn","definition":{"kind":"Operator","name":"R","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Internal","builtin":"TRUE"}]}},"whereDefined":"User","visibility":"Visible","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"A","body":{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Internal","builtin":"FALSE"}]},{"kind":"Ix","index":1}]}},"whereDefined":"User","visibility":"Visible","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"B","body":{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":3},{"kind":"Internal","builtin":"TRUE"}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]},{"kind":"Internal","builtin":"FALSE"}]}]}},"whereDefined":"User","visibility":"Visible","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"C","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Cdot"},"args":[{"kind":"Ix","index":2},{"kind":"Ix","index":1}]}},"whereDefined":"User","visibility":"Visible","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"D","body":{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":5},{"kind":"Internal","builtin":"FALSE"}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":5}]},{"kind":"Internal","builtin":"FALSE"}]}]}},"whereDefined":"User","visibility":"Visible","isLocal":false}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Equiv"},"args":[{"kind":"Ix","index":2},{"kind":"Ix","index":1}]}}
fm 
ed {"context":[{"kind":"Flex","name":"x"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Equiv"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Cdot"},"args":[{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Internal","builtin":"FALSE"}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Internal","builtin":"TRUE"}]}]},{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Internal","builtin":"TRUE"}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Internal","builtin":"FALSE"}]}]}]},{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Internal","builtin":"FALSE"}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Internal","builtin":"FALSE"}]}]}]}}
ns =ed
ne =ed
tr false
fl =ed
xe !TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure
xc {"context":[{"kind":"Flex","name":"x"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Equiv"},"args":[{"kind":"Quant","quantifier":"Exists","bounds":[{"name":"x#enabled#prime1","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"List","bullet":"And","items":[{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Internal","builtin":"FALSE"}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Internal","builtin":"TRUE"}]}]},{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Internal","builtin":"TRUE"}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]},{"kind":"Internal","builtin":"FALSE"}]}]}]}},{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Internal","builtin":"FALSE"}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Internal","builtin":"FALSE"}]}]}]}}
xl {"context":[{"kind":"Flex","name":"x"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Equiv"},"args":[{"kind":"Apply","operator":{"kind":"Opaque","name":"CdotWrapper"},"args":[{"kind":"Lambda","params":[{"name":"r#0","shape":0}],"body":{"kind":"List","bullet":"And","items":[{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Internal","builtin":"FALSE"}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Internal","builtin":"TRUE"}]}]},{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Internal","builtin":"TRUE"}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]},{"kind":"Internal","builtin":"FALSE"}]}]}]}}]},{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Internal","builtin":"FALSE"}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Internal","builtin":"FALSE"}]}]}]}}
= -
{"context":[{"kind":"Defn","definition":{"kind":"Bpragma","name":"ExpandCdot","body":{"kind":"Internal","builtin":"TRUE"},"methods":[[{"hint":"prover","value":{"kind":"String","value":"expandcdot"}}]]},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Flex","name":"x"},{"kind":"Defn","definition":{"kind":"Operator","name":"R","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Internal","builtin":"TRUE"}]}},"whereDefined":"User","visibility":"Visible","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"A","body":{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Internal","builtin":"FALSE"}]},{"kind":"Ix","index":1}]}},"whereDefined":"User","visibility":"Visible","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"B","body":{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":3},{"kind":"Internal","builtin":"TRUE"}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]},{"kind":"Internal","builtin":"FALSE"}]}]}},"whereDefined":"User","visibility":"Visible","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"C","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Cdot"},"args":[{"kind":"Ix","index":2},{"kind":"Ix","index":1}]}},"whereDefined":"User","visibility":"Visible","isLocal":false}],"active":{"kind":"Ix","index":6}}
fm 
ed {"context":[{"kind":"Defn","definition":{"kind":"Bpragma","name":"ExpandCdot","body":{"kind":"Internal","builtin":"TRUE"},"methods":[[{"hint":"prover","value":{"kind":"String","value":"expandcdot"}}]]},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Flex","name":"x"}],"active":{"kind":"Ix","index":2}}
ns {"context":[{"kind":"Flex","name":"x"}],"active":{"kind":"Internal","builtin":"TRUE"}}
ne {"context":[{"kind":"Flex","name":"x"}],"active":{"kind":"Internal","builtin":"TRUE"}}
tr true
fl {"context":[{"kind":"Flex","name":"x"}],"active":{"kind":"Internal","builtin":"TRUE"}}
xe {"context":[{"kind":"Flex","name":"x"}],"active":{"kind":"Internal","builtin":"TRUE"}}
xc {"context":[{"kind":"Flex","name":"x"}],"active":{"kind":"Internal","builtin":"TRUE"}}
xl {"context":[{"kind":"Flex","name":"x"}],"active":{"kind":"Internal","builtin":"TRUE"}}
= -
{"context":[{"kind":"Defn","definition":{"kind":"Bpragma","name":"Zenon","body":{"kind":"Internal","builtin":"TRUE"},"methods":[[{"hint":"prover","value":{"kind":"String","value":"zenon"}}]]},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Defn","definition":{"kind":"Bpragma","name":"ExpandCdot","body":{"kind":"Internal","builtin":"TRUE"},"methods":[[{"hint":"prover","value":{"kind":"String","value":"expandcdot"}}]]},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Fact","expression":{"kind":"Ix","index":1},"visibility":"Visible","time":"Always"}],"active":{"kind":"Ix","index":3}}
fm expandcdot
ed =in
ns {"context":[{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"}],"active":{"kind":"Internal","builtin":"TRUE"}}
ne {"context":[{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"}],"active":{"kind":"Internal","builtin":"TRUE"}}
tr true
fl {"context":[],"active":{"kind":"Internal","builtin":"TRUE"}}
xe {"context":[{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"}],"active":{"kind":"Internal","builtin":"TRUE"}}
xc {"context":[{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"}],"active":{"kind":"Internal","builtin":"TRUE"}}
xl {"context":[{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"}],"active":{"kind":"Internal","builtin":"TRUE"}}
= -
{"context":[{"kind":"Defn","definition":{"kind":"Bpragma","name":"ExpandCdot","body":{"kind":"Internal","builtin":"TRUE"},"methods":[[{"hint":"prover","value":{"kind":"String","value":"expandcdot"}}]]},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Defn","definition":{"kind":"Bpragma","name":"AutoUSE","body":{"kind":"Internal","builtin":"TRUE"},"methods":[[{"hint":"prover","value":{"kind":"String","value":"autouse"}}]]},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Flex","name":"x"},{"kind":"Defn","definition":{"kind":"Operator","name":"R","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Internal","builtin":"TRUE"}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"A","body":{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Internal","builtin":"FALSE"}]},{"kind":"Ix","index":1}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"B","body":{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":3},{"kind":"Internal","builtin":"TRUE"}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]},{"kind":"Internal","builtin":"FALSE"}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"C","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Cdot"},"args":[{"kind":"Ix","index":2},{"kind":"Ix","index":1}]}},"whereDefined":"User","visibility":"Visible","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"D","body":{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":5},{"kind":"Internal","builtin":"FALSE"}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":5}]},{"kind":"Internal","builtin":"FALSE"}]}]}},"whereDefined":"User","visibility":"Visible","isLocal":false},{"kind":"Fact","expression":{"kind":"Ix","index":8},"visibility":"Visible","time":"Always"},{"kind":"Fact","expression":{"kind":"Ix","index":8},"visibility":"Visible","time":"Always"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Equiv"},"args":[{"kind":"Ix","index":4},{"kind":"Ix","index":3}]}}
fm expandcdot,autouse
ed {"context":[{"kind":"Defn","definition":{"kind":"Bpragma","name":"ExpandCdot","body":{"kind":"Internal","builtin":"TRUE"},"methods":[[{"hint":"prover","value":{"kind":"String","value":"expandcdot"}}]]},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Defn","definition":{"kind":"Bpragma","name":"AutoUSE","body":{"kind":"Internal","builtin":"TRUE"},"methods":[[{"hint":"prover","value":{"kind":"String","value":"autouse"}}]]},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Flex","name":"x"},{"kind":"Defn","definition":{"kind":"Operator","name":"R","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Internal","builtin":"TRUE"}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"A","body":{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Internal","builtin":"FALSE"}]},{"kind":"Ix","index":1}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"B","body":{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":3},{"kind":"Internal","builtin":"TRUE"}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]},{"kind":"Internal","builtin":"FALSE"}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Fact","expression":{"kind":"Ix","index":6},"visibility":"Visible","time":"Always"},{"kind":"Fact","expression":{"kind":"Ix","index":6},"visibility":"Visible","time":"Always"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Equiv"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Cdot"},"args":[{"kind":"Ix","index":4},{"kind":"Ix","index":3}]},{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":6},{"kind":"Internal","builtin":"FALSE"}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":6}]},{"kind":"Internal","builtin":"FALSE"}]}]}]}}
ns {"context":[{"kind":"Flex","name":"x"},{"kind":"Defn","definition":{"kind":"Operator","name":"R","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Internal","builtin":"TRUE"}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"A","body":{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Internal","builtin":"FALSE"}]},{"kind":"Ix","index":1}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"B","body":{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":3},{"kind":"Internal","builtin":"TRUE"}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]},{"kind":"Internal","builtin":"FALSE"}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"},{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Equiv"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Cdot"},"args":[{"kind":"Ix","index":4},{"kind":"Ix","index":3}]},{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":6},{"kind":"Internal","builtin":"FALSE"}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":6}]},{"kind":"Internal","builtin":"FALSE"}]}]}]}}
ne {"context":[{"kind":"Flex","name":"x"},{"kind":"Defn","definition":{"kind":"Operator","name":"R","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Internal","builtin":"TRUE"}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"A","body":{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Internal","builtin":"FALSE"}]},{"kind":"Ix","index":1}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"B","body":{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":3},{"kind":"Internal","builtin":"TRUE"}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]},{"kind":"Internal","builtin":"FALSE"}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"},{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Equiv"},"args":[{"kind":"Quant","quantifier":"Exists","bounds":[{"name":"x#enabled#prime1","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"List","bullet":"And","items":[{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":7},{"kind":"Internal","builtin":"FALSE"}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Internal","builtin":"TRUE"}]}]},{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Internal","builtin":"TRUE"}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":7}]},{"kind":"Internal","builtin":"FALSE"}]}]}]}},{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":6},{"kind":"Internal","builtin":"FALSE"}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":6}]},{"kind":"Internal","builtin":"FALSE"}]}]}]}}
tr false
fl {"context":[{"kind":"Flex","name":"x"},{"kind":"Defn","definition":{"kind":"Operator","name":"R","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Internal","builtin":"TRUE"}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"A","body":{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Internal","builtin":"FALSE"}]},{"kind":"Ix","index":1}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"B","body":{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":3},{"kind":"Internal","builtin":"TRUE"}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]},{"kind":"Internal","builtin":"FALSE"}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Equiv"},"args":[{"kind":"Quant","quantifier":"Exists","bounds":[{"name":"x#enabled#prime1","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"List","bullet":"And","items":[{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":5},{"kind":"Internal","builtin":"FALSE"}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Internal","builtin":"TRUE"}]}]},{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Internal","builtin":"TRUE"}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":5}]},{"kind":"Internal","builtin":"FALSE"}]}]}]}},{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":4},{"kind":"Internal","builtin":"FALSE"}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":4}]},{"kind":"Internal","builtin":"FALSE"}]}]}]}}
xe !TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure
xc !TlaProverError|Hidden definition of operator `A` needs expansion for soundly expanding the operator `\cdot` (using rigid quantification).\nThe expansion of the operator `\cdot` has been activated with the `ExpandCdot` proof directive from the module `TLAPS`.\nThe operator `A` is defined at: \n	<unknown location>\nand the operator `A` occurs at: \n	<unknown location>\nUsing the proof directive `AutoUSE` from the module `TLAPS`, or `BY DEF A` is expected to avoid this error.\n|
xl !TlaProverError|Hidden definition of operator `A` needs expansion for soundly expanding the operators `ENABLED` and `\cdot` (using rigid quantification).\nThe expansion of the operators `ENABLED` and `\cdot` has been activated with the the proof directives `ExpandENABLED` and `ExpandCdot` from the module `TLAPS`.\nThe operator `A` is defined at: \n	<unknown location>\nand the operator `A` occurs at: \n	<unknown location>\nUsing the proof directive `AutoUSE` from the module `TLAPS`, or `BY DEF A` is expected to avoid this error.\n|
= -
{"context":[{"kind":"Defn","definition":{"kind":"Bpragma","name":"Zenon","body":{"kind":"Internal","builtin":"TRUE"},"methods":[[{"hint":"prover","value":{"kind":"String","value":"zenon"}}]]},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Defn","definition":{"kind":"Bpragma","name":"ExpandENABLED","body":{"kind":"Internal","builtin":"TRUE"},"methods":[[{"hint":"prover","value":{"kind":"String","value":"expandenabled"}}]]},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Defn","definition":{"kind":"Bpragma","name":"ExpandCdot","body":{"kind":"Internal","builtin":"TRUE"},"methods":[[{"hint":"prover","value":{"kind":"String","value":"expandcdot"}}]]},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Fact","expression":{"kind":"Ix","index":2},"visibility":"Visible","time":"Always"},{"kind":"Fact","expression":{"kind":"Ix","index":2},"visibility":"Visible","time":"Always"}],"active":{"kind":"Ix","index":5}}
fm expandenabled,expandcdot
ed =in
ns {"context":[{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"},{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"}],"active":{"kind":"Internal","builtin":"TRUE"}}
ne =ns
tr true
fl {"context":[],"active":{"kind":"Internal","builtin":"TRUE"}}
xe =ns
xc =ns
xl =ns
= -
{"context":[{"kind":"Defn","definition":{"kind":"Bpragma","name":"Zenon","body":{"kind":"Internal","builtin":"TRUE"},"methods":[[{"hint":"prover","value":{"kind":"String","value":"zenon"}}]]},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Defn","definition":{"kind":"Bpragma","name":"ExpandENABLED","body":{"kind":"Internal","builtin":"TRUE"},"methods":[[{"hint":"prover","value":{"kind":"String","value":"expandenabled"}}]]},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Fact","expression":{"kind":"Ix","index":1},"visibility":"Visible","time":"Always"}],"active":{"kind":"Ix","index":3}}
fm expandenabled
ed =in
ns {"context":[{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"}],"active":{"kind":"Internal","builtin":"TRUE"}}
ne {"context":[{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"}],"active":{"kind":"Internal","builtin":"TRUE"}}
tr true
fl {"context":[],"active":{"kind":"Internal","builtin":"TRUE"}}
xe {"context":[{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"}],"active":{"kind":"Internal","builtin":"TRUE"}}
xc {"context":[{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"}],"active":{"kind":"Internal","builtin":"TRUE"}}
xl {"context":[{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"}],"active":{"kind":"Internal","builtin":"TRUE"}}
= -
{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fresh","name":"x","shape":0,"level":"Constant","domain":{"kind":"Ix","index":1},"domainVisibility":"Visible"},{"kind":"Fresh","name":"y","shape":0,"level":"Constant","domain":{"kind":"Ix","index":2},"domainVisibility":"Visible"},{"kind":"Fresh","name":"z","shape":0,"level":"Constant","domain":{"kind":"Ix","index":3},"domainVisibility":"Visible"},{"kind":"Fresh","name":"j","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fresh","name":"k","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fresh","name":"l","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Defn","definition":{"kind":"Operator","name":"I","body":{"kind":"Record","fields":[{"name":"f1","value":{"kind":"Ix","index":6}},{"name":"f2","value":{"kind":"Ix","index":5}},{"name":"f3","value":{"kind":"Ix","index":4}},{"name":"f4","value":{"kind":"Ix","index":3}},{"name":"f5","value":{"kind":"Ix","index":2}},{"name":"f6","value":{"kind":"Ix","index":1}}]}},"whereDefined":"User","visibility":"Visible","isLocal":true}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":7,"isAtomic":true},{"kind":"Ix","index":7}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":6,"isAtomic":true},{"kind":"Ix","index":6}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":5,"isAtomic":true},{"kind":"Ix","index":5}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":4,"isAtomic":true},{"kind":"Ix","index":4}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":3,"isAtomic":true},{"kind":"Ix","index":3}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2,"isAtomic":true},{"kind":"Ix","index":2}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Num","integer":"0","fraction":""},{"kind":"Num","integer":"0","fraction":""}]}]}}
fm 
ed {"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fresh","name":"x","shape":0,"level":"Constant","domain":{"kind":"Ix","index":1},"domainVisibility":"Visible"},{"kind":"Fresh","name":"y","shape":0,"level":"Constant","domain":{"kind":"Ix","index":2},"domainVisibility":"Visible"},{"kind":"Fresh","name":"z","shape":0,"level":"Constant","domain":{"kind":"Ix","index":3},"domainVisibility":"Visible"},{"kind":"Fresh","name":"j","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fresh","name":"k","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fresh","name":"l","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":6,"isAtomic":true},{"kind":"Ix","index":6}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":5,"isAtomic":true},{"kind":"Ix","index":5}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":4,"isAtomic":true},{"kind":"Ix","index":4}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":3,"isAtomic":true},{"kind":"Ix","index":3}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2,"isAtomic":true},{"kind":"Ix","index":2}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1,"isAtomic":true},{"kind":"Ix","index":1}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Num","integer":"0","fraction":""},{"kind":"Num","integer":"0","fraction":""}]}]}}
ns =ed
ne =ed
tr false
fl =ed
xe =ed
xc =ed
xl =ed
= -
{"context":[{"kind":"Fresh","name":"+","shape":2,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fresh","name":"-","shape":2,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Let","definitions":[{"kind":"Operator","name":"G","body":{"kind":"Apply","operator":{"kind":"Ix","index":2},"args":[{"kind":"Num","integer":"10","fraction":""},{"kind":"Num","integer":"20","fraction":""}]}}],"body":{"kind":"Apply","operator":{"kind":"Ix","index":2},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"10","fraction":""}]},"isAtomic":true},{"kind":"Let","definitions":[{"kind":"Operator","name":"G","body":{"kind":"Apply","operator":{"kind":"Ix","index":2},"args":[{"kind":"Num","integer":"10","fraction":""},{"kind":"Num","integer":"20","fraction":""}]}}],"body":{"kind":"Apply","operator":{"kind":"Ix","index":2},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"10","fraction":""}]}}]}}
fm 
ed =in
ns {"context":[{"kind":"Fresh","name":"+","shape":2,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fresh","name":"-","shape":2,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":2},"args":[{"kind":"Num","integer":"10","fraction":""},{"kind":"Num","integer":"20","fraction":""}]},{"kind":"Num","integer":"10","fraction":""}]},{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":2},"args":[{"kind":"Num","integer":"10","fraction":""},{"kind":"Num","integer":"20","fraction":""}]},{"kind":"Num","integer":"10","fraction":""}]}]}}
ne =ns
tr false
fl =ns
xe =ns
xc =ns
xl =ns
= -
{"context":[{"kind":"Defn","definition":{"kind":"Operator","name":"f","body":{"kind":"Fcn","bounds":[{"name":"x","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"SetEnum","elements":[{"kind":"Num","integer":"1","fraction":""}]}}}],"body":{"kind":"Fcn","bounds":[{"name":"y","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"SetEnum","elements":[{"kind":"Num","integer":"2","fraction":""}]}}}],"body":{"kind":"Num","integer":"3","fraction":""}}}},"whereDefined":"User","visibility":"Visible","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"g","body":{"kind":"Except","function":{"kind":"Ix","index":1},"specs":[{"trail":[{"kind":"Apply","expression":{"kind":"Num","integer":"1","fraction":""}},{"kind":"Apply","expression":{"kind":"Num","integer":"2","fraction":""}}],"value":{"kind":"Num","integer":"1","fraction":""}}]}},"whereDefined":"User","visibility":"Visible","isLocal":false}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"FcnApp","function":{"kind":"FcnApp","function":{"kind":"Ix","index":1},"args":[{"kind":"Num","integer":"1","fraction":""}]},"args":[{"kind":"Num","integer":"2","fraction":""}]},{"kind":"Num","integer":"1","fraction":""}]}}
fm 
ed {"context":[],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"FcnApp","function":{"kind":"FcnApp","function":{"kind":"Except","function":{"kind":"Fcn","bounds":[{"name":"x","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"SetEnum","elements":[{"kind":"Num","integer":"1","fraction":""}]}}}],"body":{"kind":"Fcn","bounds":[{"name":"y","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"SetEnum","elements":[{"kind":"Num","integer":"2","fraction":""}]}}}],"body":{"kind":"Num","integer":"3","fraction":""}}},"specs":[{"trail":[{"kind":"Apply","expression":{"kind":"Num","integer":"1","fraction":""}},{"kind":"Apply","expression":{"kind":"Num","integer":"2","fraction":""}}],"value":{"kind":"Num","integer":"1","fraction":""}}]},"args":[{"kind":"Num","integer":"1","fraction":""}]},"args":[{"kind":"Num","integer":"2","fraction":""}]},{"kind":"Num","integer":"1","fraction":""}]}}
ns {"context":[],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"FcnApp","function":{"kind":"FcnApp","function":{"kind":"Except","function":{"kind":"Fcn","bounds":[{"name":"x","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"SetEnum","elements":[{"kind":"Num","integer":"1","fraction":""}]}}}],"body":{"kind":"Fcn","bounds":[{"name":"y","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"SetEnum","elements":[{"kind":"Num","integer":"2","fraction":""}]}}}],"body":{"kind":"Num","integer":"3","fraction":""}}},"specs":[{"trail":[{"kind":"Apply","expression":{"kind":"Num","integer":"1","fraction":""}}],"value":{"kind":"Except","function":{"kind":"FcnApp","function":{"kind":"Fcn","bounds":[{"name":"x","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"SetEnum","elements":[{"kind":"Num","integer":"1","fraction":""}]}}}],"body":{"kind":"Fcn","bounds":[{"name":"y","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"SetEnum","elements":[{"kind":"Num","integer":"2","fraction":""}]}}}],"body":{"kind":"Num","integer":"3","fraction":""}}},"args":[{"kind":"Num","integer":"1","fraction":""}]},"specs":[{"trail":[{"kind":"Apply","expression":{"kind":"Num","integer":"2","fraction":""}}],"value":{"kind":"Num","integer":"1","fraction":""}}]}}]},"args":[{"kind":"Num","integer":"1","fraction":""}]},"args":[{"kind":"Num","integer":"2","fraction":""}]},{"kind":"Num","integer":"1","fraction":""}]}}
ne =ns
tr false
fl =ns
xe =ns
xc =ns
xl =ns
= -
{"context":[],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Equiv"},"args":[{"kind":"Fair","fairness":"Weak","subscript":{"kind":"Internal","builtin":"TRUE"},"action":{"kind":"Internal","builtin":"TRUE"}},{"kind":"Fair","fairness":"Weak","subscript":{"kind":"Internal","builtin":"TRUE"},"action":{"kind":"Internal","builtin":"TRUE"}}]}}
fm 
ed =in
ns =in
ne =in
tr false
fl =in
xe =in
xc =in
xl =in
= -
{"context":[],"active":{"kind":"Internal","builtin":"FALSE"}}
fm 
ed =in
ns =in
ne =in
tr false
fl =in
xe =in
xc =in
xl =in
= -
{"context":[{"kind":"Defn","definition":{"kind":"Bpragma","name":"M!SMT","body":{"kind":"Internal","builtin":"TRUE"},"methods":[[{"hint":"prover","value":{"kind":"String","value":"smt3"}}]]},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Fact","expression":{"kind":"Ix","index":1},"visibility":"Visible","time":"Always"}],"active":{"kind":"Internal","builtin":"TRUE"}}
fm 
ed =in
ns {"context":[{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"}],"active":{"kind":"Internal","builtin":"TRUE"}}
ne {"context":[{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"}],"active":{"kind":"Internal","builtin":"TRUE"}}
tr true
fl {"context":[],"active":{"kind":"Internal","builtin":"TRUE"}}
xe {"context":[{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"}],"active":{"kind":"Internal","builtin":"TRUE"}}
xc {"context":[{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"}],"active":{"kind":"Internal","builtin":"TRUE"}}
xl {"context":[{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"}],"active":{"kind":"Internal","builtin":"TRUE"}}
= -
{"context":[{"kind":"Defn","definition":{"kind":"Bpragma","name":"M!SMT","body":{"kind":"Internal","builtin":"TRUE"},"methods":[[{"hint":"prover","value":{"kind":"String","value":"smt3"}}]]},"whereDefined":"User","visibility":"Hidden","isLocal":false}],"active":{"kind":"Ix","index":1}}
fm 
ed =in
ns {"context":[],"active":{"kind":"Internal","builtin":"TRUE"}}
ne {"context":[],"active":{"kind":"Internal","builtin":"TRUE"}}
tr true
fl {"context":[],"active":{"kind":"Internal","builtin":"TRUE"}}
xe {"context":[],"active":{"kind":"Internal","builtin":"TRUE"}}
xc {"context":[],"active":{"kind":"Internal","builtin":"TRUE"}}
xl {"context":[],"active":{"kind":"Internal","builtin":"TRUE"}}
= -
{"context":[{"kind":"Flex","name":"x"},{"kind":"Defn","definition":{"kind":"Bpragma","name":"Zenon","body":{"kind":"Internal","builtin":"TRUE"},"methods":[[{"hint":"prover","value":{"kind":"String","value":"zenon"}}]]},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"F","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Num","integer":"1","fraction":""}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"H","body":{"kind":"Tsub","modal":"Box","action":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":3},{"kind":"Num","integer":"1","fraction":""}]}]},"subscript":{"kind":"Ix","index":3}}},"whereDefined":"User","visibility":"Hidden","isLocal":false}],"active":{"kind":"Ix","index":3}}
fm 
ed =in
ns {"context":[{"kind":"Flex","name":"x"},{"kind":"Defn","definition":{"kind":"Operator","name":"F","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"1","fraction":""}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"H","body":{"kind":"Tsub","modal":"Box","action":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":2},{"kind":"Num","integer":"1","fraction":""}]}]},"subscript":{"kind":"Ix","index":2}}},"whereDefined":"User","visibility":"Hidden","isLocal":false}],"active":{"kind":"Internal","builtin":"TRUE"}}
ne =ns
tr true
fl =ns
xe =ns
xc =ns
xl =ns
= -
{"context":[{"kind":"Fresh","name":"c","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Except","function":{"kind":"Record","fields":[{"name":"a","value":{"kind":"Ix","index":1}},{"name":"b","value":{"kind":"Num","integer":"2","fraction":""}},{"name":"a","value":{"kind":"Num","integer":"5","fraction":""}}]},"specs":[{"trail":[{"kind":"Dot","field":"a"}],"value":{"kind":"Num","integer":"3","fraction":""}},{"trail":[{"kind":"Apply","expression":{"kind":"String","value":"b"}}],"value":{"kind":"Num","integer":"4","fraction":""}},{"trail":[{"kind":"Dot","field":"z"}],"value":{"kind":"Num","integer":"6","fraction":""}}]},{"kind":"Ix","index":1}]}}
fm 
ed =in
ns {"context":[{"kind":"Fresh","name":"c","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Except","function":{"kind":"Record","fields":[{"name":"a","value":{"kind":"Num","integer":"3","fraction":""}},{"name":"b","value":{"kind":"Num","integer":"4","fraction":""}},{"name":"a","value":{"kind":"Num","integer":"3","fraction":""}}]},"specs":[{"trail":[{"kind":"Dot","field":"z"}],"value":{"kind":"Num","integer":"6","fraction":""}}]},{"kind":"Ix","index":1}]}}
ne =ns
tr false
fl =ns
xe =ns
xc =ns
xl =ns
= -
{"context":[{"kind":"Fresh","name":"f","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Except","function":{"kind":"Ix","index":1},"specs":[{"trail":[{"kind":"Apply","expression":{"kind":"Num","integer":"1","fraction":""}},{"kind":"Dot","field":"x"}],"value":{"kind":"Num","integer":"1","fraction":""}},{"trail":[{"kind":"Apply","expression":{"kind":"Num","integer":"1","fraction":""}},{"kind":"Dot","field":"y"}],"value":{"kind":"Num","integer":"2","fraction":""}},{"trail":[{"kind":"Apply","expression":{"kind":"Num","integer":"2","fraction":""}}],"value":{"kind":"Num","integer":"3","fraction":""}},{"trail":[],"value":{"kind":"Ix","index":1}},{"trail":[{"kind":"Dot","field":"w"}],"value":{"kind":"Num","integer":"4","fraction":""}}]}}
fm 
ed =in
ns {"context":[{"kind":"Fresh","name":"f","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Except","function":{"kind":"Ix","index":1},"specs":[{"trail":[{"kind":"Dot","field":"w"}],"value":{"kind":"Num","integer":"4","fraction":""}}]}}
ne =ns
tr false
fl =ns
xe =ns
xc =ns
xl =ns
= -
{"context":[{"kind":"Fresh","name":"f","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Ix","index":1}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Except","function":{"kind":"Ix","index":2},"specs":[{"trail":[{"kind":"Dot","field":"x"}],"value":{"kind":"Num","integer":"1","fraction":""}}]}}
fm 
ed =in
ns =in
ne =in
tr false
fl =in
xe {"context":[{"kind":"Fresh","name":"f","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Ix","index":1}]},"visibility":"Visible","time":"Always"}],"active":{"kind":"Except","function":{"kind":"Ix","index":2},"specs":[{"trail":[{"kind":"Dot","field":"x"}],"value":{"kind":"Num","integer":"1","fraction":""}}]}}
xc =xe
xl =xe
= -
{"context":[{"kind":"Fresh","name":"f","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Ix","index":1}]},"visibility":"Hidden","time":"Now"}],"active":{"kind":"Except","function":{"kind":"Ix","index":2},"specs":[{"trail":[{"kind":"Dot","field":"x"}],"value":{"kind":"Num","integer":"1","fraction":""}}]}}
fm 
ed =in
ns =in
ne =in
tr false
fl =in
xe {"context":[{"kind":"Fresh","name":"f","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Ix","index":1}]},"visibility":"Hidden","time":"Always"}],"active":{"kind":"Except","function":{"kind":"Ix","index":2},"specs":[{"trail":[{"kind":"Dot","field":"x"}],"value":{"kind":"Num","integer":"1","fraction":""}}]}}
xc =xe
xl =xe
= -
{"context":[{"kind":"Fresh","name":"f","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Let","definitions":[{"kind":"Operator","name":"A","body":{"kind":"Ix","index":1}},{"kind":"Operator","name":"B","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}}],"body":{"kind":"Let","definitions":[{"kind":"Bpragma","name":"P","body":{"kind":"Ix","index":1},"methods":[]}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":3}]}}}}
fm 
ed =in
ns {"context":[{"kind":"Fresh","name":"f","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":1}]},{"kind":"Ix","index":1}]}}
ne =ns
tr false
fl =ns
xe =ns
xc =ns
xl =ns
= -
{"context":[{"kind":"Fresh","name":"f","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Let","definitions":[{"kind":"Instance","name":"I","instance":{"args":[],"module":"M","substitutions":[]}}],"body":{"kind":"Internal","builtin":"TRUE"}}}
fm 
ed =in
ns !TlaProofError|Found INSTANCE in Expr.Elab.let_normalize, all INSTANCE statements have been replaced with definitions in Module.Elab |Failure("Found INSTANCE in Expr.Elab.let_normalize, all INSTANCE statements have been replaced with definitions in Module.Elab ")
ne !TlaProofError|Found INSTANCE in Expr.Elab.let_normalize, all INSTANCE statements have been replaced with definitions in Module.Elab |Failure("Found INSTANCE in Expr.Elab.let_normalize, all INSTANCE statements have been replaced with definitions in Module.Elab ")
xe !TlaProofError|Found INSTANCE in Expr.Elab.let_normalize, all INSTANCE statements have been replaced with definitions in Module.Elab |Failure("Found INSTANCE in Expr.Elab.let_normalize, all INSTANCE statements have been replaced with definitions in Module.Elab ")
xc !TlaProofError|Found INSTANCE in Expr.Elab.let_normalize, all INSTANCE statements have been replaced with definitions in Module.Elab |Failure("Found INSTANCE in Expr.Elab.let_normalize, all INSTANCE statements have been replaced with definitions in Module.Elab ")
xl !TlaProofError|Found INSTANCE in Expr.Elab.let_normalize, all INSTANCE statements have been replaced with definitions in Module.Elab |Failure("Found INSTANCE in Expr.Elab.let_normalize, all INSTANCE statements have been replaced with definitions in Module.Elab ")
= -
{"context":[{"kind":"Fact","expression":{"kind":"Let","definitions":[{"kind":"Recursive","name":"R","shape":0}],"body":{"kind":"Internal","builtin":"TRUE"}},"visibility":"Hidden","time":"Now"}],"active":{"kind":"Internal","builtin":"TRUE"}}
fm 
ed =in
ns !TlaProofError|Expr.Elab.let_normalize|Failure("Expr.Elab.let_normalize")
ne !TlaProofError|Expr.Elab.let_normalize|Failure("Expr.Elab.let_normalize")
xe !TlaProofError|Expr.Elab.let_normalize|Failure("Expr.Elab.let_normalize")
xc !TlaProofError|Expr.Elab.let_normalize|Failure("Expr.Elab.let_normalize")
xl !TlaProofError|Expr.Elab.let_normalize|Failure("Expr.Elab.let_normalize")
= -
{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fresh","name":"x","shape":0,"level":"Constant","domain":{"kind":"Ix","index":1},"domainVisibility":"Hidden"},{"kind":"Fresh","name":"y","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":2},{"kind":"Ix","index":3}]}}
fm 
ed =in
ns =in
ne =in
tr true
fl =in
xe =in
xc =in
xl =in
= -
{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"Quant","quantifier":"Exists","bounds":[{"name":"a","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}},"visibility":"Hidden","time":"Now"},{"kind":"Fresh","name":"y","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Quant","quantifier":"Exists","bounds":[{"name":"b","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":4}]}}}
fm 
ed =in
ns =in
ne =in
tr true
fl =in
xe {"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"Quant","quantifier":"Exists","bounds":[{"name":"a","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}},"visibility":"Hidden","time":"Always"},{"kind":"Fresh","name":"y","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Quant","quantifier":"Exists","bounds":[{"name":"b","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":4}]}}}
xc =xe
xl =xe
= -
{"context":[{"kind":"Fresh","name":"a","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fresh","name":"b","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":2},{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Internal","builtin":"TRUE"},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":1}]}]},{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"z","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":3}]}]}},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Subseteq"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}]},"visibility":"Visible","time":"Now"},{"kind":"Fact","expression":{"kind":"List","bullet":"Refs","items":[{"kind":"Internal","builtin":"TRUE"},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":3},{"kind":"Ix","index":2}]}]},"visibility":"Visible","time":"Always"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":4},{"kind":"Ix","index":4}]},"visibility":"Hidden","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":5},{"kind":"Ix","index":4}]}}
fm 
ed =in
ns =in
ne =in
tr false
fl {"context":[{"kind":"Fresh","name":"a","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fresh","name":"b","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":2},{"kind":"Ix","index":1}]},{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"z","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":3}]}},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Subseteq"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}]},"visibility":"Visible","time":"Now"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":3},{"kind":"Ix","index":2}]},"visibility":"Visible","time":"Now"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":3},{"kind":"Ix","index":3}]},"visibility":"Visible","time":"Now"},{"kind":"Fact","expression":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"z","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":5}]}},"visibility":"Visible","time":"Now"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":6},{"kind":"Ix","index":5}]},"visibility":"Visible","time":"Always"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":7},{"kind":"Ix","index":7}]},"visibility":"Hidden","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":8},{"kind":"Ix","index":7}]}}
xe {"context":[{"kind":"Fresh","name":"a","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fresh","name":"b","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":2},{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Internal","builtin":"TRUE"},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":1}]}]},{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"z","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":3}]}]}},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Subseteq"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}]},"visibility":"Visible","time":"Always"},{"kind":"Fact","expression":{"kind":"List","bullet":"Refs","items":[{"kind":"Internal","builtin":"TRUE"},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":3},{"kind":"Ix","index":2}]}]},"visibility":"Visible","time":"Always"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":4},{"kind":"Ix","index":4}]},"visibility":"Hidden","time":"Always"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":5},{"kind":"Ix","index":4}]}}
xc =xe
xl =xe
= -
{"context":[{"kind":"Defn","definition":{"kind":"Operator","name":"V","body":{"kind":"Num","integer":"1","fraction":""}},"whereDefined":"User","visibility":"Visible","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"H","body":{"kind":"Ix","index":1}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Defn","definition":{"kind":"Bpragma","name":"P","body":{"kind":"Ix","index":2},"methods":[]},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Defn","definition":{"kind":"Recursive","name":"R","shape":1},"whereDefined":"User","visibility":"Visible","isLocal":false}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":4},{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Ix","index":2},{"kind":"Ix","index":3}]}]}}
fm 
ed {"context":[{"kind":"Defn","definition":{"kind":"Operator","name":"H","body":{"kind":"Num","integer":"1","fraction":""}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Defn","definition":{"kind":"Bpragma","name":"P","body":{"kind":"Num","integer":"1","fraction":""},"methods":[]},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Defn","definition":{"kind":"Recursive","name":"R","shape":1},"whereDefined":"User","visibility":"Visible","isLocal":false}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Num","integer":"1","fraction":""},{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Ix","index":2},{"kind":"Ix","index":3}]}]}}
ns {"context":[{"kind":"Defn","definition":{"kind":"Operator","name":"H","body":{"kind":"Num","integer":"1","fraction":""}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Defn","definition":{"kind":"Recursive","name":"R","shape":1},"whereDefined":"User","visibility":"Visible","isLocal":false}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Num","integer":"1","fraction":""},{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Num","integer":"1","fraction":""},{"kind":"Ix","index":2}]}]}}
ne =ns
tr false
fl =ns
xe =ns
xc =ns
xl =ns
= -
{"context":[{"kind":"Fresh","name":"a","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"1","fraction":""}]}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Num","integer":"1","fraction":""}]}}
fm 
ed =in
ns =in
ne =in
tr false
fl {"context":[{"kind":"Fresh","name":"a","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":1}]},"visibility":"Visible","time":"Now"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Num","integer":"1","fraction":""}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":3},{"kind":"Num","integer":"1","fraction":""}]}}
xe {"context":[{"kind":"Fresh","name":"a","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"1","fraction":""}]}]},"visibility":"Visible","time":"Always"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Num","integer":"1","fraction":""}]}}
xc =xe
xl =xe
"##;

    #[test]
    fn matches_the_typescript() {
        assert_eq!(check_cases(CASES), 34);
    }
}
