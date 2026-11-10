//! tlapm's E_tuply_declarations: declarations such as <<x, y>> \in S become declarations of names.
//! A port of `src/obligations/tuples.ts`.

use crate::expression::{
    Bound, BoundDomain, Builtin, Bullet, Defn, DefnCore, Expr, ExprCore, Level, Quantifier, expr,
    located,
};

#[derive(Clone, Debug)]
pub enum TuplyBound {
    Name { name: String, domain: BoundDomain },
    Tuple { names: Vec<String>, domain: Expr },
}

/// The binder `expandChoose` expands: a CHOOSE, whose domain is optional, or a set filter.
#[derive(Clone, Debug)]
pub enum TuplyBinder {
    Choose { domain: Option<Expr> },
    SetSt { domain: Expr },
}

fn get_opaque(name: &str) -> Expr {
    expr(ExprCore::Opaque {
        name: name.to_owned(),
    })
}

fn get_names_tuple(names: &[String]) -> Expr {
    expr(ExprCore::Tuple {
        elements: names.iter().map(|name| get_opaque(name)).collect(),
    })
}

fn get_equality(left: Expr, right: Expr) -> Expr {
    expr(ExprCore::Apply {
        operator: expr(ExprCore::Internal {
            builtin: Builtin::Eq,
        }),
        args: vec![left, right],
    })
}

/// The first name as a JavaScript template literal shows `names[0]`.
fn get_first_name(names: &[String]) -> &str {
    names.first().map_or("undefined", String::as_str)
}

pub fn get_unbounded(names: &[String]) -> Vec<Bound> {
    names
        .iter()
        .map(|name| Bound {
            name: name.clone(),
            level: Level::Constant,
            domain: BoundDomain::NoDomain,
        })
        .collect()
}

fn get_factors<'a>(domain: Option<&'a Expr>, names: &[String]) -> Option<&'a [Expr]> {
    match &domain?.core {
        ExprCore::Product { factors } if factors.len() == names.len() => Some(factors),
        _ => None,
    }
}

/// Each name is the matching item of the tuple: x == t[1], y == t[2].
fn get_item_definitions(tuple: &str, names: &[String]) -> Vec<Defn> {
    names
        .iter()
        .enumerate()
        .map(|(index, name)| Defn {
            core: DefnCore::Operator {
                name: name.clone(),
                body: expr(ExprCore::FcnApp {
                    function: get_opaque(tuple),
                    args: vec![expr(ExprCore::Num {
                        integer: (index + 1).to_string(),
                        fraction: String::new(),
                    })],
                }),
            },
            location: None,
        })
        .collect()
}

fn get_factor_bounds(names: &[String], factors: &[Expr]) -> Vec<Bound> {
    names
        .iter()
        .zip(factors)
        .map(|(name, factor)| Bound {
            name: name.clone(),
            level: Level::Constant,
            domain: BoundDomain::Domain(factor.clone()),
        })
        .collect()
}

fn get_named_bound(name: &str, domain: &BoundDomain) -> Bound {
    Bound {
        name: name.to_owned(),
        level: Level::Constant,
        domain: domain.clone(),
    }
}

/// \E <<x, y>> \in A \X B: P becomes \E x \in A, y \in B: P, and \E <<x, y>> \in S: P becomes
/// \E x, y: <<x, y>> \in S /\ P. Each domain quantifies separately, the last one innermost.
pub fn expand_quant(quantifier: Quantifier, bounds: &[TuplyBound], body: Expr) -> Expr {
    let mut groups: Vec<Vec<&TuplyBound>> = Vec::new();
    for bound in bounds {
        if matches!(
            bound,
            TuplyBound::Name {
                domain: BoundDomain::Ditto,
                ..
            }
        ) {
            if let Some(group) = groups.last_mut() {
                group.push(bound);
            }
        } else {
            groups.push(vec![bound]);
        }
    }
    groups.iter().rev().fold(body, |inner, group| {
        let quantify = |quantified: Vec<Bound>, quantified_body: Expr| {
            located(
                ExprCore::Quant {
                    quantifier,
                    bounds: quantified,
                    body: quantified_body,
                },
                inner.location.clone(),
            )
        };
        match group[0] {
            TuplyBound::Name { .. } => quantify(
                group
                    .iter()
                    .filter_map(|bound| match bound {
                        TuplyBound::Name { name, domain } => Some(get_named_bound(name, domain)),
                        TuplyBound::Tuple { .. } => None,
                    })
                    .collect(),
                inner.clone(),
            ),
            TuplyBound::Tuple { names, domain } => {
                if let Some(factors) = get_factors(Some(domain), names) {
                    return quantify(get_factor_bounds(names, factors), inner.clone());
                }
                let membership = expr(ExprCore::Apply {
                    operator: expr(ExprCore::Internal {
                        builtin: if quantifier == Quantifier::Exists {
                            Builtin::Mem
                        } else {
                            Builtin::Notmem
                        },
                    }),
                    args: vec![get_names_tuple(names), domain.clone()],
                });
                quantify(
                    get_unbounded(names),
                    expr(ExprCore::List {
                        bullet: if quantifier == Quantifier::Exists {
                            Bullet::And
                        } else {
                            Bullet::Or
                        },
                        items: vec![membership, inner.clone()],
                    }),
                )
            }
        }
    })
}

/// CHOOSE <<x, y>> \in A \X B: P binds t \in A \X B with x == t[1], y == t[2], and any other
/// domain binds t with \E x, y: t = <<x, y>> /\ P. {<<x, y>> \in S: P} binds t the same way.
pub fn expand_choose(binder: TuplyBinder, names: &[String], body: Expr) -> Expr {
    let kind = match binder {
        TuplyBinder::Choose { .. } => "choose",
        TuplyBinder::SetSt { .. } => "setst",
    };
    let name = format!("{kind}#{}", get_first_name(names));
    let domain = match &binder {
        TuplyBinder::Choose { domain } => domain.as_ref(),
        TuplyBinder::SetSt { domain } => Some(domain),
    };
    let body = if get_factors(domain, names).is_some() {
        expr(ExprCore::Let {
            definitions: get_item_definitions(&name, names),
            body,
        })
    } else {
        expr(ExprCore::Quant {
            quantifier: Quantifier::Exists,
            bounds: get_unbounded(names),
            body: expr(ExprCore::List {
                bullet: Bullet::And,
                items: vec![
                    get_equality(get_opaque(&name), get_names_tuple(names)),
                    body,
                ],
            }),
        })
    };
    expr(match binder {
        TuplyBinder::Choose { domain } => ExprCore::Choose { name, domain, body },
        TuplyBinder::SetSt { domain } => ExprCore::SetSt { name, domain, body },
    })
}

/// A set or function constructor binds each tuple as fcn#x, with its names defined in a LET around
/// the value. A set constructor over a matching product binds the names to its factors instead.
fn expand_constructor_bounds(
    bounds: &[TuplyBound],
    value: Expr,
    is_set_of: bool,
) -> (Vec<Bound>, Expr) {
    let expanded: Vec<(Vec<Bound>, Vec<Defn>)> = bounds
        .iter()
        .map(|bound| {
            let (names, domain) = match bound {
                TuplyBound::Name { name, domain } => {
                    return (vec![get_named_bound(name, domain)], Vec::new());
                }
                TuplyBound::Tuple { names, domain } => (names, domain),
            };
            let factors = get_factors(Some(domain), names);
            if let Some(factors) = factors
                && is_set_of
            {
                return (get_factor_bounds(names, factors), Vec::new());
            }
            let name = format!("fcn#{}", get_first_name(names));
            let fcn_bound = Bound {
                name: name.clone(),
                level: Level::Constant,
                domain: BoundDomain::Domain(domain.clone()),
            };
            if factors.is_some() {
                return (vec![fcn_bound], get_item_definitions(&name, names));
            }
            let choice = format!("choose#{name}");
            let mut definitions = vec![Defn {
                core: DefnCore::Operator {
                    name: choice.clone(),
                    body: expand_choose(
                        TuplyBinder::Choose { domain: None },
                        names,
                        get_equality(get_opaque(&name), get_names_tuple(names)),
                    ),
                },
                location: None,
            }];
            definitions.extend(get_item_definitions(&choice, names));
            (vec![fcn_bound], definitions)
        })
        .collect();
    let definitions: Vec<Defn> = expanded
        .iter()
        .flat_map(|item| item.1.iter().cloned())
        .collect();
    let bounds = expanded.into_iter().flat_map(|item| item.0).collect();
    let value = if definitions.is_empty() {
        value
    } else {
        expr(ExprCore::Let {
            definitions,
            body: value,
        })
    };
    (bounds, value)
}

pub fn expand_set_of(element: Expr, bounds: &[TuplyBound]) -> Expr {
    let (bounds, element) = expand_constructor_bounds(bounds, element, true);
    expr(ExprCore::SetOf { element, bounds })
}

pub fn expand_fcn(bounds: &[TuplyBound], body: Expr) -> Expr {
    let (bounds, body) = expand_constructor_bounds(bounds, body, false);
    expr(ExprCore::Fcn { bounds, body })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expression::Locus;

    fn show_bound(bound: &Bound) -> String {
        let domain = match &bound.domain {
            BoundDomain::Domain(expression) => format!(" \\in {}", show(expression)),
            BoundDomain::Ditto => " ditto".to_owned(),
            BoundDomain::NoDomain => String::new(),
        };
        format!("{}{domain}", bound.name)
    }

    fn show_all(items: &[Expr], separator: &str) -> String {
        items.iter().map(show).collect::<Vec<_>>().join(separator)
    }

    fn show_bounds(bounds: &[Bound]) -> String {
        bounds.iter().map(show_bound).collect::<Vec<_>>().join(", ")
    }

    /// The same rendering as the scratch script that printed the TypeScript's results.
    fn show(expression: &Expr) -> String {
        let location = expression
            .location
            .as_ref()
            .map_or_else(String::new, |locus| format!("@{}", locus.start_line));
        match &expression.core {
            ExprCore::Opaque { name } => format!("{name}{location}"),
            ExprCore::Internal { builtin } => builtin.name().to_owned(),
            ExprCore::Num { integer, .. } => integer.clone(),
            ExprCore::Tuple { elements } => format!("<<{}>>", show_all(elements, ", ")),
            ExprCore::Product { factors } => format!("({})", show_all(factors, " X ")),
            ExprCore::Apply { operator, args } => {
                format!("{}({})", show(operator), show_all(args, ", "))
            }
            ExprCore::List { bullet, items } => format!("{bullet:?}[{}]", show_all(items, ", ")),
            ExprCore::Quant {
                quantifier,
                bounds,
                body,
            } => format!(
                "{quantifier:?}{location}{{{}}}: {}",
                show_bounds(bounds),
                show(body)
            ),
            ExprCore::Let { definitions, body } => format!(
                "LET {} IN {}",
                definitions
                    .iter()
                    .map(|definition| match &definition.core {
                        DefnCore::Operator { name, body } => format!("{name} == {}", show(body)),
                        _ => "?".to_owned(),
                    })
                    .collect::<Vec<_>>()
                    .join("; "),
                show(body)
            ),
            ExprCore::FcnApp { function, args } => {
                format!("{}[{}]", show(function), show_all(args, ", "))
            }
            ExprCore::Choose { name, domain, body } => format!(
                "CHOOSE {name}{}: {}",
                domain
                    .as_ref()
                    .map_or_else(String::new, |domain| format!(" \\in {}", show(domain))),
                show(body)
            ),
            ExprCore::SetSt { name, domain, body } => {
                format!("{{{name} \\in {}: {}}}", show(domain), show(body))
            }
            ExprCore::SetOf { element, bounds } => {
                format!("{{{}: {}}}", show(element), show_bounds(bounds))
            }
            ExprCore::Fcn { bounds, body } => {
                format!("[{} |-> {}]", show_bounds(bounds), show(body))
            }
            _ => "?".to_owned(),
        }
    }

    fn get_body() -> Expr {
        located(
            ExprCore::Opaque {
                name: "P".to_owned(),
            },
            Some(Locus {
                file: "f".into(),
                start_line: 7,
                start_column: 1,
                end_line: 7,
                end_column: 2,
            }),
        )
    }

    fn get_product(names: &[&str]) -> Expr {
        expr(ExprCore::Product {
            factors: names.iter().map(|name| get_opaque(name)).collect(),
        })
    }

    fn get_names(names: &[&str]) -> Vec<String> {
        names.iter().map(|name| (*name).to_owned()).collect()
    }

    fn name(name: &str, domain: BoundDomain) -> TuplyBound {
        TuplyBound::Name {
            name: name.to_owned(),
            domain,
        }
    }

    fn tuple(names: &[&str], domain: Expr) -> TuplyBound {
        TuplyBound::Tuple {
            names: get_names(names),
            domain,
        }
    }

    fn domain(name: &str) -> BoundDomain {
        BoundDomain::Domain(get_opaque(name))
    }

    fn get_quant_cases() -> Vec<Vec<TuplyBound>> {
        vec![
            vec![
                name("a", domain("S")),
                name("b", BoundDomain::Ditto),
                name("c", BoundDomain::NoDomain),
            ],
            vec![name("a", BoundDomain::Ditto), name("b", domain("S"))],
            vec![tuple(&["x", "y"], get_product(&["A", "B"]))],
            vec![tuple(&["x", "y"], get_opaque("S"))],
            vec![tuple(&["x", "y", "z"], get_product(&["A", "B"]))],
            vec![
                name("a", domain("S")),
                tuple(&["x", "y"], get_opaque("T")),
                name("b", BoundDomain::Ditto),
                tuple(&["u", "v"], get_product(&["A", "B"])),
            ],
            vec![],
        ]
    }

    #[test]
    fn expands_quantifiers_as_the_typescript_does() {
        let expected = [
            "Exists@7{a \\in S, b ditto}: Exists@7{c}: P@7",
            "Exists@7{b \\in S}: P@7",
            "Exists@7{x \\in A, y \\in B}: P@7",
            "Exists@7{x, y}: And[Mem(<<x, y>>, S), P@7]",
            "Exists@7{x, y, z}: And[Mem(<<x, y, z>>, (A X B)), P@7]",
            "Exists@7{a \\in S}: Exists@7{x, y}: And[Mem(<<x, y>>, T), Exists@7{u \\in A, v \\in B}: P@7]",
            "P@7",
            "Forall@7{a \\in S, b ditto}: Forall@7{c}: P@7",
            "Forall@7{b \\in S}: P@7",
            "Forall@7{x \\in A, y \\in B}: P@7",
            "Forall@7{x, y}: Or[Notmem(<<x, y>>, S), P@7]",
            "Forall@7{x, y, z}: Or[Notmem(<<x, y, z>>, (A X B)), P@7]",
            "Forall@7{a \\in S}: Forall@7{x, y}: Or[Notmem(<<x, y>>, T), Forall@7{u \\in A, v \\in B}: P@7]",
            "P@7",
        ];
        let actual: Vec<String> = [Quantifier::Exists, Quantifier::Forall]
            .into_iter()
            .flat_map(|quantifier| {
                get_quant_cases()
                    .into_iter()
                    .map(move |bounds| show(&expand_quant(quantifier, &bounds, get_body())))
            })
            .collect();
        assert_eq!(actual, expected);
    }

    #[test]
    fn expands_choose_as_the_typescript_does() {
        let cases = [
            (
                TuplyBinder::Choose {
                    domain: Some(get_product(&["A", "B"])),
                },
                get_names(&["x", "y"]),
                "CHOOSE choose#x \\in (A X B): LET x == choose#x[1]; y == choose#x[2] IN P@7",
            ),
            (
                TuplyBinder::Choose { domain: None },
                get_names(&["x", "y"]),
                "CHOOSE choose#x: Exists{x, y}: And[Eq(choose#x, <<x, y>>), P@7]",
            ),
            (
                TuplyBinder::Choose {
                    domain: Some(get_opaque("S")),
                },
                get_names(&["x", "y"]),
                "CHOOSE choose#x \\in S: Exists{x, y}: And[Eq(choose#x, <<x, y>>), P@7]",
            ),
            (
                TuplyBinder::SetSt {
                    domain: get_product(&["A", "B"]),
                },
                get_names(&["x", "y"]),
                "{setst#x \\in (A X B): LET x == setst#x[1]; y == setst#x[2] IN P@7}",
            ),
            (
                TuplyBinder::SetSt {
                    domain: get_opaque("S"),
                },
                get_names(&["x"]),
                "{setst#x \\in S: Exists{x}: And[Eq(setst#x, <<x>>), P@7]}",
            ),
            (
                TuplyBinder::Choose { domain: None },
                Vec::new(),
                "CHOOSE choose#undefined: Exists{}: And[Eq(choose#undefined, <<>>), P@7]",
            ),
        ];
        for (binder, names, expected) in cases {
            assert_eq!(show(&expand_choose(binder, &names, get_body())), expected);
        }
    }

    #[test]
    fn expands_constructors_as_the_typescript_does() {
        let tuple_set = "LET choose#fcn#x == CHOOSE choose#x: Exists{x, y}: And[Eq(choose#x, <<x, y>>), Eq(fcn#x, <<x, y>>)]; x == choose#fcn#x[1]; y == choose#fcn#x[2]";
        let cases = [
            (
                vec![name("a", domain("S")), name("b", BoundDomain::Ditto)],
                "{P@7: a \\in S, b ditto}".to_owned(),
                "[a \\in S, b ditto |-> P@7]".to_owned(),
            ),
            (
                vec![tuple(&["x", "y"], get_product(&["A", "B"]))],
                "{P@7: x \\in A, y \\in B}".to_owned(),
                "[fcn#x \\in (A X B) |-> LET x == fcn#x[1]; y == fcn#x[2] IN P@7]".to_owned(),
            ),
            (
                vec![tuple(&["x", "y"], get_opaque("S"))],
                format!("{{{tuple_set} IN P@7: fcn#x \\in S}}"),
                format!("[fcn#x \\in S |-> {tuple_set} IN P@7]"),
            ),
            (
                vec![
                    name("a", BoundDomain::Domain(get_product(&["A"]))),
                    tuple(&["x", "y"], get_opaque("T")),
                    tuple(&["u", "v"], get_product(&["A", "B"])),
                ],
                format!("{{{tuple_set} IN P@7: a \\in (A), fcn#x \\in T, u \\in A, v \\in B}}"),
                format!(
                    "[a \\in (A), fcn#x \\in T, fcn#u \\in (A X B) |-> {tuple_set}; u == fcn#u[1]; v == fcn#u[2] IN P@7]"
                ),
            ),
        ];
        for (bounds, set_of, fcn) in cases {
            assert_eq!(show(&expand_set_of(get_body(), &bounds)), set_of);
            assert_eq!(show(&expand_fcn(&bounds, get_body())), fcn);
        }
    }

    #[test]
    fn binds_names_without_domains() {
        assert_eq!(show_bounds(&get_unbounded(&get_names(&["p", "q"]))), "p, q");
        assert!(get_unbounded(&[]).is_empty());
        assert!(
            get_unbounded(&get_names(&["p"]))
                .iter()
                .all(|bound| bound.level == Level::Constant)
        );
    }
}
