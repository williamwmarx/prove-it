//! A port of tlapm's Backend.Zenon: an obligation as the input of Zenon's TLA+ front end, a $hyp for
//! each visible fact and a $goal, naming identifiers as Isabelle does. A port of
//! `src/prover/zenon/encode.ts`.

use crate::errors::{ObligationError, Result};
use crate::expression::{
    Bound, BoundDomain, Builtin, Bullet, ExceptPoint, Expr, ExprCore, Field, Hyp, HypCore,
    Quantifier, Sequent, Visibility, located,
};
use crate::first_order::{
    get_unprintable_error, pickle, print_fact, repeat_parsed, split_first_bound,
};
use crate::format::{Doc, FormatArg, format, format_delimited, render_doc, text};
use crate::printer::{Context, create_context, get_bound_name, pop_names, push_name};

fn get_space() -> Doc {
    format("@ ", vec![])
}

fn get_atom(builtin: Builtin) -> Option<&'static str> {
    Some(match builtin {
        Builtin::TRUE => "T.",
        Builtin::FALSE => "F.",
        Builtin::STRING => "TLA.STRING",
        Builtin::BOOLEAN => "(TLA.set T. F.)",
        Builtin::Nat => "arith.N",
        Builtin::Int => "arith.Z",
        Builtin::Real => "arith.R",
        Builtin::Infinity => "arith.Infinity",
        Builtin::Any => "TLA.Any",
        _ => return None,
    })
}

fn get_operator(builtin: Builtin) -> Option<(&'static str, usize)> {
    Some(match builtin {
        Builtin::Implies => ("=>", 2),
        Builtin::Equiv => ("<=>", 2),
        Builtin::Conj => ("/\\", 2),
        Builtin::Disj => ("\\/", 2),
        Builtin::Neg => ("-.", 1),
        Builtin::Eq => ("=", 2),
        Builtin::DOMAIN => ("TLA.DOMAIN", 1),
        Builtin::SUBSET => ("TLA.SUBSET", 1),
        Builtin::UNION => ("TLA.UNION", 1),
        Builtin::Subseteq => ("TLA.subseteq", 2),
        Builtin::Mem => ("TLA.in", 2),
        Builtin::Setminus => ("TLA.setminus", 2),
        Builtin::Cap => ("TLA.cap", 2),
        Builtin::Cup => ("TLA.cup", 2),
        Builtin::Plus => ("arith.add", 2),
        Builtin::Uminus => ("arith.minus", 1),
        Builtin::Times => ("arith.mul", 2),
        Builtin::Ratio => ("arith.div", 2),
        Builtin::Quotient => ("arith.euclidiv", 2),
        Builtin::Remainder => ("arith.mod", 2),
        Builtin::Exp => ("arith.power", 2),
        Builtin::Lteq => ("arith.le", 2),
        Builtin::Lt => ("arith.lt", 2),
        Builtin::Range => ("arith.intrange", 2),
        Builtin::Seq => ("TLA.Seq", 1),
        Builtin::Len => ("TLA.Len", 1),
        Builtin::BSeq => ("TLA.BSeq", 1),
        Builtin::Cat => ("TLA.concat", 2),
        Builtin::Append => ("TLA.Append", 2),
        Builtin::Head => ("TLA.Head", 1),
        Builtin::Tail => ("TLA.Tail", 1),
        Builtin::SubSeq => ("TLA.SubSeq", 3),
        Builtin::SelectSeq => ("TLA.SelectSeq", 2),
        Builtin::OneArg => ("TLA.oneArg", 2),
        Builtin::Extend => ("TLA.extend", 2),
        Builtin::Print => ("TLA.Print", 2),
        Builtin::PrintT => ("TLA.PrintT", 1),
        Builtin::Assert => ("TLA.Assert", 2),
        Builtin::JavaTime => ("TLA.JavaTime", 0),
        Builtin::TLCGet => ("TLA.TLCGet", 1),
        Builtin::TLCSet => ("TLA.TLCSet", 2),
        Builtin::Permutations => ("TLA.Permutations", 1),
        Builtin::SortSeq => ("TLA.SortSeq", 2),
        Builtin::RandomElement => ("TLA.RandomElement", 1),
        Builtin::ToString => ("TLA.ToString", 1),
        _ => return None,
    })
}

fn get_successors(integer: &str) -> Result<String> {
    Ok(format!(
        "{}0{}",
        repeat_parsed("(TLA.fapply TLA.Succ ", integer)?,
        repeat_parsed(")", integer)?
    ))
}

/// The closures of `encodeZenon`, over the names bound where they print.
struct Printer {
    context: Context,
}

impl AsMut<Context> for Printer {
    fn as_mut(&mut self) -> &mut Context {
        &mut self.context
    }
}

impl Printer {
    fn adjoin(&mut self, name: &str) -> Result<String> {
        let pickled = pickle(name)?;
        Ok(push_name(&mut self.context, &pickled))
    }

    fn bump(&mut self) {
        push_name(&mut self.context, "");
    }

    fn delimited(&mut self, args: &[Expr]) -> Result<Doc> {
        format_delimited(args, |arg| self.print_expr(arg), Some(get_space()))
    }

    fn nonatomic(&mut self, name: &str, args: &[Expr]) -> Result<Doc> {
        let delimited = self.delimited(args)?;
        Ok(format("(%s %a)", vec![name.into(), delimited.into()]))
    }

    /// A binder's name binds in the body, and what comes before prints outside it.
    fn print_binder(&mut self, name: &str, before: Doc, body: &Expr) -> Result<Doc> {
        let bound = self.adjoin(name)?;
        let printed = self.print_expr(body)?;
        let doc = format(
            "%a((%s) %a))",
            vec![before.into(), bound.into(), printed.into()],
        );
        pop_names(&mut self.context, 1);
        Ok(doc)
    }

    fn print_internal(&mut self, builtin: Builtin, args: &[Expr]) -> Result<Doc> {
        if let Some(atom) = get_atom(builtin)
            && args.is_empty()
        {
            return Ok(text(atom));
        }
        if let Some((name, arity)) = get_operator(builtin)
            && arity == args.len()
        {
            return self.nonatomic(name, args);
        }
        if let [left, right] = args {
            match builtin {
                Builtin::Neq => {
                    let equality = self.nonatomic("=", args)?;
                    return Ok(format("(-. %a)", vec![equality.into()]));
                }
                Builtin::Notmem => {
                    let membership = self.nonatomic("TLA.in", args)?;
                    return Ok(format("(-. %a)", vec![membership.into()]));
                }
                Builtin::Minus => {
                    let negated = located(
                        ExprCore::Apply {
                            operator: located(
                                ExprCore::Internal {
                                    builtin: Builtin::Uminus,
                                },
                                right.location.clone(),
                            ),
                            args: vec![right.clone()],
                        },
                        right.location.clone(),
                    );
                    return self.nonatomic("arith.add", &[left.clone(), negated]);
                }
                Builtin::Gteq => return self.nonatomic("arith.le", &[right.clone(), left.clone()]),
                Builtin::Gt => return self.nonatomic("arith.lt", &[right.clone(), left.clone()]),
                _ => {}
            }
        }
        if let (Builtin::Unprimable, [arg]) = (builtin, args) {
            return self.print_expr(arg);
        }
        Err(get_unprintable_error(
            builtin,
            args.len(),
            "Backend.Zenon.fmt_apply",
        ))
    }

    fn print_apply(&mut self, operator: &Expr, args: &[Expr]) -> Result<Doc> {
        match &operator.core {
            ExprCore::Ix { index } => {
                let name = get_bound_name(&self.context, *index);
                let Some(name) = name.filter(|_| *index > 0) else {
                    return Err(ObligationError::assert_failure());
                };
                if args.is_empty() {
                    Ok(text(&name))
                } else {
                    self.nonatomic(&name, args)
                }
            }
            ExprCore::Opaque { name } => {
                let name = pickle(name)?;
                if args.is_empty() {
                    Ok(text(&name))
                } else {
                    self.nonatomic(&name, args)
                }
            }
            ExprCore::Internal { builtin } => self.print_internal(*builtin, args),
            ExprCore::Lambda { params, body } => {
                let names = params
                    .iter()
                    .map(|param| Ok(format("%s ", vec![self.adjoin(&param.name)?.into()])))
                    .collect::<Result<Vec<_>>>()?;
                let printed = self.print_expr(body)?;
                let doc = format("((%a) %a)", vec![Doc::from(names).into(), printed.into()]);
                pop_names(&mut self.context, params.len());
                Ok(doc)
            }
            _ => Err(ObligationError::assert_failure()),
        }
    }

    fn print_quant(
        &mut self,
        quantifier: Quantifier,
        bounds: &[Bound],
        body: &Expr,
    ) -> Result<Doc> {
        if bounds.is_empty() {
            return self.print_expr(body);
        }
        let split = split_first_bound(quantifier, bounds, body)?;
        let is_forall = quantifier == Quantifier::Forall;
        match &split.first.domain {
            BoundDomain::NoDomain => self.print_binder(
                &split.first.name,
                text(if is_forall { "(A. " } else { "(E. " }),
                &split.inner,
            ),
            BoundDomain::Domain(expression) => {
                let domain = self.print_expr(expression)?;
                self.print_binder(
                    &split.first.name,
                    format(
                        "(%s %a ",
                        vec![
                            if is_forall { "TLA.bAll" } else { "TLA.bEx" }.into(),
                            domain.into(),
                        ],
                    ),
                    &split.inner,
                )
            }
            BoundDomain::Ditto => Err(ObligationError::assert_failure()),
        }
    }

    /// SetOf and Fcn take one bound, whose domain prints outside it.
    fn print_one_bound(
        &mut self,
        name: &str,
        bounds: &[Bound],
        body: &Expr,
        what: &str,
    ) -> Result<Doc> {
        let [bound] = bounds else {
            return Err(ObligationError::unsupported(format!(
                "{what} (multiple declared constants)"
            )));
        };
        let BoundDomain::Domain(expression) = &bound.domain else {
            return Err(ObligationError::assert_failure());
        };
        let domain = self.print_expr(expression)?;
        self.print_binder(
            &bound.name,
            format("(%s %a ", vec![name.into(), domain.into()]),
            body,
        )
    }

    /// A sequent inside an expression, as an implication under quantifiers.
    fn print_nested_sequent(&mut self, context: &[Hyp], active: &Expr) -> Result<Doc> {
        let Some((hyp, rest)) = context.split_first() else {
            return self.print_expr(active);
        };
        match &hyp.core {
            HypCore::Fact {
                expression,
                visibility,
                ..
            } => {
                let fact = if *visibility == Visibility::Visible {
                    Some(self.print_expr(expression)?)
                } else {
                    None
                };
                self.bump();
                let printed_rest = self.print_nested_sequent(rest, active)?;
                let doc = match fact {
                    Some(fact) => format("(=> %a %a)", vec![fact.into(), printed_rest.into()]),
                    None => printed_rest,
                };
                pop_names(&mut self.context, 1);
                Ok(doc)
            }
            HypCore::Defn { .. } => Err(ObligationError::assert_failure()),
            HypCore::Fresh {
                name,
                domain,
                domain_visibility,
                ..
            } => {
                let domain = match domain {
                    Some(domain) if *domain_visibility == Visibility::Visible => {
                        Some(self.print_expr(domain)?)
                    }
                    _ => None,
                };
                let name = self.adjoin(name)?;
                let printed_rest = self.print_nested_sequent(rest, active)?;
                let doc = match domain {
                    Some(domain) => format(
                        "(TLA.bAll %a ((%s) %a))",
                        vec![domain.into(), name.into(), printed_rest.into()],
                    ),
                    None => format("(A. ((%s) %a))", vec![name.into(), printed_rest.into()]),
                };
                pop_names(&mut self.context, 1);
                Ok(doc)
            }
            HypCore::Flex { name } => {
                let name = self.adjoin(name)?;
                let printed_rest = self.print_nested_sequent(rest, active)?;
                let doc = format(
                    "(A. ((%s) (A. ((%s') %a))))",
                    vec![name.clone().into(), name.into(), printed_rest.into()],
                );
                pop_names(&mut self.context, 1);
                Ok(doc)
            }
        }
    }

    fn print_fields(&mut self, opening: &str, fields: &[Field]) -> Result<Doc> {
        let printed = fields
            .iter()
            .map(|field| {
                let value = self.print_expr(&field.value)?;
                Ok(format(
                    " \"%s\" %a",
                    vec![field.name.as_str().into(), value.into()],
                ))
            })
            .collect::<Result<Vec<_>>>()?;
        Ok(Doc::from(vec![
            text(opening),
            Doc::from(printed),
            text(")"),
        ]))
    }

    #[allow(clippy::too_many_lines)]
    fn print_expr(&mut self, expression: &Expr) -> Result<Doc> {
        match &expression.core {
            ExprCore::Ix { .. }
            | ExprCore::Internal { .. }
            | ExprCore::Opaque { .. }
            | ExprCore::Lambda { .. } => self.print_apply(expression, &[]),
            ExprCore::Apply { operator, args } => self.print_apply(operator, args),
            ExprCore::Sequent { sequent } => {
                self.print_nested_sequent(&sequent.context, &sequent.active)
            }
            ExprCore::With {
                expression: inner, ..
            }
            | ExprCore::Parens {
                expression: inner, ..
            } => self.print_expr(inner),
            ExprCore::If {
                condition,
                consequent,
                alternative,
            } => {
                let condition = self.print_expr(condition)?;
                let consequent = self.print_expr(consequent)?;
                let alternative = self.print_expr(alternative)?;
                Ok(format(
                    "(TLA.cond %a %a %a)",
                    vec![condition.into(), consequent.into(), alternative.into()],
                ))
            }
            ExprCore::List { bullet, items } => {
                if *bullet == Bullet::Refs {
                    match items.as_slice() {
                        [] => return Err(ObligationError::assert_failure()),
                        [item] => return self.print_expr(item),
                        _ => {}
                    }
                }
                let delimited = self.delimited(items)?;
                Ok(format(
                    "(%s %a)",
                    vec![
                        if *bullet == Bullet::Or { "\\/" } else { "/\\" }.into(),
                        delimited.into(),
                    ],
                ))
            }
            ExprCore::Quant {
                quantifier,
                bounds,
                body,
            } => self.print_quant(*quantifier, bounds, body),
            ExprCore::Tquant { .. } => Err(ObligationError::unsupported("\\AA or \\EE")),
            ExprCore::Choose { name, domain, body } => match domain {
                Some(domain) => {
                    let domain = self.print_expr(domain)?;
                    self.print_binder(name, format("(TLA.bChoice %a ", vec![domain.into()]), body)
                }
                None => self.print_binder(name, text("(t. "), body),
            },
            ExprCore::SetSt { name, domain, body } => {
                let domain = self.print_expr(domain)?;
                self.print_binder(name, format("(TLA.subsetOf %a ", vec![domain.into()]), body)
            }
            ExprCore::SetOf { element, bounds } => {
                self.print_one_bound("TLA.setOfAll", bounds, element, "Setof")
            }
            ExprCore::Fcn { bounds, body } => self.print_one_bound("TLA.Fcn", bounds, body, "Fcn"),
            ExprCore::SetEnum { elements } => {
                if elements.is_empty() {
                    return Ok(text("TLA.emptyset"));
                }
                let printed = elements
                    .iter()
                    .map(|element| Ok(format(" %a", vec![self.print_expr(element)?.into()])))
                    .collect::<Result<Vec<_>>>()?;
                Ok(Doc::from(vec![
                    text("(TLA.set"),
                    Doc::from(printed),
                    text(")"),
                ]))
            }
            ExprCore::FcnApp { function, args } => {
                let printed_function = self.print_expr(function)?;
                if let [arg] = args.as_slice() {
                    let printed = self.print_expr(arg)?;
                    return Ok(format(
                        "(TLA.fapply %a %a)",
                        vec![printed_function.into(), printed.into()],
                    ));
                }
                let delimited = self.delimited(args)?;
                Ok(format(
                    "(TLA.fapply %a (TLA.tuple %a))",
                    vec![printed_function.into(), delimited.into()],
                ))
            }
            ExprCore::Arrow { domain, range } => {
                let domain = self.print_expr(domain)?;
                let range = self.print_expr(range)?;
                Ok(format(
                    "(TLA.FuncSet %a %a)",
                    vec![domain.into(), range.into()],
                ))
            }
            ExprCore::Rect { fields } => self.print_fields("(TLA.recordset", fields),
            ExprCore::Record { fields } => self.print_fields("(TLA.record", fields),
            ExprCore::Except { function, specs } => {
                let [spec] = specs.as_slice() else {
                    return Err(ObligationError::unsupported("complex EXCEPT"));
                };
                let [point] = spec.trail.as_slice() else {
                    return Err(ObligationError::unsupported("complex EXCEPT"));
                };
                let argument = match point {
                    ExceptPoint::Dot(field) => text(&format!("\"{field}\"")),
                    ExceptPoint::Apply(expression) => self.print_expr(expression)?,
                };
                let function = self.print_expr(function)?;
                let value = self.print_expr(&spec.value)?;
                Ok(format(
                    "(TLA.except %a %a %a)",
                    vec![function.into(), argument.into(), value.into()],
                ))
            }
            ExprCore::Dot {
                expression: inner,
                field,
            } => {
                let printed = self.print_expr(inner)?;
                Ok(format(
                    "(TLA.fapply %a \"%s\")",
                    vec![printed.into(), field.as_str().into()],
                ))
            }
            ExprCore::Tuple { elements } => {
                let delimited = self.delimited(elements)?;
                Ok(format("(TLA.tuple %a)", vec![delimited.into()]))
            }
            ExprCore::Product { factors } => {
                if let [left, right] = factors.as_slice() {
                    let left = self.print_expr(left)?;
                    let right = self.print_expr(right)?;
                    return Ok(format("(TLA.prod %a %a)", vec![left.into(), right.into()]));
                }
                let delimited = self.delimited(factors)?;
                Ok(format(
                    "(TLA.Product (TLA.tuple %a))",
                    vec![delimited.into()],
                ))
            }
            ExprCore::Sub { .. } => Err(ObligationError::unsupported("Sub")),
            ExprCore::Tsub { .. } => Err(ObligationError::unsupported("Tsub")),
            ExprCore::Fair { .. } => Err(ObligationError::unsupported("Fair")),
            ExprCore::Case { arms, other } => {
                let arms = format_delimited(
                    arms,
                    |arm| {
                        let condition = self.print_expr(&arm.condition)?;
                        let body = self.print_expr(&arm.body)?;
                        Ok(format("%a %a", vec![condition.into(), body.into()]))
                    },
                    Some(get_space()),
                )?;
                match other {
                    Some(other) => {
                        let other = self.print_expr(other)?;
                        Ok(format(
                            "(TLA.CASE %a %a)@]",
                            vec![arms.into(), other.into()],
                        ))
                    }
                    None => Ok(format("(TLA.CASE %a )", vec![arms.into()])),
                }
            }
            ExprCore::String { value } => Ok(format("\"%s\"", vec![value.as_str().into()])),
            ExprCore::Num { integer, fraction } => {
                if !fraction.is_empty() {
                    return Err(ObligationError::unsupported("Real number constants"));
                }
                Ok(text(&get_successors(integer)?))
            }
            ExprCore::Bang { .. } | ExprCore::Let { .. } | ExprCore::At { .. } => {
                Err(ObligationError::assert_failure())
            }
        }
    }

    fn print_hyp(&mut self, hyp: &Hyp) -> Result<Doc> {
        match &hyp.core {
            HypCore::Fresh {
                name,
                domain,
                domain_visibility,
                ..
            } => {
                let domain = match domain {
                    Some(domain) if *domain_visibility == Visibility::Visible => {
                        Some(self.print_expr(domain)?)
                    }
                    _ => None,
                };
                let name = self.adjoin(name)?;
                Ok(match domain {
                    Some(domain) => format(
                        "$hyp \"%s_in\" (TLA.in %s %a)@\n",
                        vec![name.clone().into(), name.into(), domain.into()],
                    ),
                    None => Doc::default(),
                })
            }
            HypCore::Flex { name } => {
                self.adjoin(name)?;
                Ok(Doc::default())
            }
            HypCore::Defn {
                definition,
                visibility,
                ..
            } => {
                let name = self.adjoin(definition.name())?;
                Ok(if *visibility == Visibility::Visible {
                    format("; usable definition %s suppressed@.", vec![name.into()])
                } else {
                    Doc::default()
                })
            }
            HypCore::Fact {
                expression,
                visibility,
                ..
            } => {
                let count = self.context.stack.len().to_string();
                let fact = if *visibility == Visibility::Visible {
                    Some(print_fact(self, |printer| printer.print_expr(expression))?)
                } else {
                    None
                };
                self.bump();
                Ok(match fact {
                    Some(Err(error)) => format(
                        "; omitted temporal assumption : %s @.",
                        vec![error.message().into()],
                    ),
                    Some(Ok(fact)) => {
                        format("$hyp \"v'%s\" %a@\n", vec![count.into(), fact.into()])
                    }
                    None => Doc::default(),
                })
            }
        }
    }

    fn print_sequent(&mut self, sequent: &Sequent) -> Result<Doc> {
        let hyps = sequent
            .context
            .iter()
            .map(|hyp| self.print_hyp(hyp))
            .collect::<Result<Vec<_>>>()?;
        let goal = self.print_expr(&sequent.active)?;
        Ok(Doc::from(vec![
            Doc::from(hyps),
            format("$goal %a", vec![FormatArg::Doc(goal)]),
        ]))
    }
}

/// pp_print_obligation: the text tlapm writes to the .znn file it hands Zenon, for an obligation
/// that Backend.Prep has shipped. Unsupported in the goal fails the obligation and in a fact omits
/// it.
pub fn encode_zenon(id: usize, sequent: &Sequent) -> Result<String> {
    let mut printer = Printer {
        context: create_context(),
    };
    let doc = match printer.print_sequent(sequent) {
        Err(ObligationError::Unsupported(message)) => {
            return Err(ObligationError::prover(format!(
                "Zenon: unsupported operator {message}"
            )));
        }
        doc => doc?,
    };
    render_doc(
        &Doc::from(vec![
            format(";; obligation #%s@\n", vec![id.to_string().into()]),
            doc,
        ]),
        68,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::first_order::test_cases::{describe, get_cases, to_sequent};

    /// Every shared case encodes to the same text, or fails with the same error, as
    /// `src/prover/zenon/encode.ts` under Bun.
    #[test]
    fn encodes_as_the_typescript_does() {
        let cases = get_cases();
        let mut failures = 0;
        for case in cases.items("cases") {
            let actual = encode_zenon(case.count("id"), &to_sequent(case.field("input")))
                .map_err(|error| describe(&error));
            let expected = case.field("zenon").outcome();
            if actual != expected {
                failures += 1;
                eprintln!("expected {expected:?}\nactual   {actual:?}\n");
            }
        }
        assert_eq!(failures, 0);
    }
}
