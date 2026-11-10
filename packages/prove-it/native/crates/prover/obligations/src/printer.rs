//! A port of tlapm's obligation printer: E_fmt with Fmtutil's minimal parenthesization, and the
//! identifier renaming in Ctx. The Rust port of `src/obligations/printer.ts`.

use std::collections::HashMap;

use crate::errors::{ObligationError, Result};
use crate::expression::is_js_space;
use crate::expression::{
    Bound, BoundDomain, Builtin, Bullet, DefnCore, ExceptPoint, Expr, ExprCore, ExprNode, Fairness,
    Hyp, HypCore, HypNode, Level, Modal, Param, ParenForm, Quantifier, Selector, Sequent, Shape,
    Visibility, WhereDefined, get_hyp_name, to_index,
};
use crate::format::{Doc, format, format_delimited, render_doc, text};
use crate::operators::{Fixity, get_standard_form, lookup_operator};

/// A name in scope: its representation and the salt that tells it apart.
#[derive(Clone, Debug)]
pub struct Ident {
    rep: String,
    salt: usize,
}

/// Ctx, which names each binder apart from the names in scope by adding a salt, as a mutable
/// stack: printers bind and unbind names in strict nesting order.
#[derive(Clone, Debug, Default)]
pub struct Context {
    pub stack: Vec<Ident>,
    idents: HashMap<String, Vec<Ident>>,
    defined: HashMap<String, usize>,
}

fn get_ident_name(ident: &Ident) -> String {
    if ident.salt == 0 {
        ident.rep.clone()
    } else {
        format!("{}_{}", ident.rep, ident.salt)
    }
}

pub fn create_context() -> Context {
    Context::default()
}

/// The name of the binder index places in, counting from 1 for the innermost.
pub fn get_bound_name(context: &Context, index: isize) -> Option<String> {
    let index = usize::try_from(index).ok().filter(|&index| index > 0)?;
    let position = context.stack.len().checked_sub(index)?;
    context.stack.get(position).map(get_ident_name)
}

pub fn push_name(context: &mut Context, rep: &str) -> String {
    let previous_salt = context
        .idents
        .get(rep)
        .and_then(|idents| idents.last())
        .map(|previous| previous.salt);
    let mut ident = Ident {
        rep: rep.to_owned(),
        salt: previous_salt.map_or(0, |salt| salt + 1),
    };
    while context.defined.contains_key(&get_ident_name(&ident)) {
        ident.salt += 1;
    }
    context.stack.push(ident.clone());
    let key = get_ident_name(&ident);
    context
        .idents
        .entry(rep.to_owned())
        .or_default()
        .push(ident);
    *context.defined.entry(key.clone()).or_insert(0) += 1;
    key
}

pub fn pop_names(context: &mut Context, count: usize) {
    for _ in 0..count {
        let Some(ident) = context.stack.pop() else {
            return;
        };
        if let Some(idents) = context.idents.get_mut(&ident.rep) {
            idents.pop();
        }
        let key = get_ident_name(&ident);
        let remaining = context.defined.get(&key).copied().unwrap_or(1) - 1;
        if remaining == 0 {
            context.defined.remove(&key);
        } else {
            context.defined.insert(key, remaining);
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Assoc {
    Left,
    Non,
    Right,
}

#[derive(Debug)]
enum Minimal {
    Atm(Doc),
    Big(Doc),
    Op {
        name: String,
        doc: Doc,
        low: i32,
        high: i32,
        skeleton: Box<Skeleton>,
    },
}

#[derive(Debug)]
enum Skeleton {
    Infix {
        assoc: Assoc,
        left: Minimal,
        right: Minimal,
    },
    Prefix(Minimal),
    Postfix(Minimal),
}

fn is_below(high: i32, expression: &Minimal) -> bool {
    match expression {
        Minimal::Atm(_) => true,
        Minimal::Op { low, .. } => high < *low,
        Minimal::Big(_) => false,
    }
}

fn with_parens(doc: Doc) -> Doc {
    Doc::from(vec![format("(", vec![]), doc, format(")", vec![])])
}

fn print_operand(operand: &Minimal, is_bare: bool) -> Doc {
    if is_bare {
        print_minimal(operand)
    } else {
        with_parens(print_minimal(operand))
    }
}

fn print_minimal(expression: &Minimal) -> Doc {
    let (name, doc, high, skeleton) = match expression {
        Minimal::Atm(doc) | Minimal::Big(doc) => return doc.clone(),
        Minimal::Op {
            name,
            doc,
            high,
            skeleton,
            ..
        } => (name, doc, high, skeleton),
    };
    let is_under = |operand: &Minimal| is_below(*high, operand);
    match skeleton.as_ref() {
        Skeleton::Prefix(operand) => {
            let is_same = matches!(operand, Minimal::Op { skeleton, .. } if matches!(skeleton.as_ref(), Skeleton::Prefix(_)));
            let operand_doc = print_operand(operand, is_under(operand) || is_same);
            Doc::from(vec![
                format("@[<h>", vec![]),
                doc.clone(),
                operand_doc,
                format("@]", vec![]),
            ])
        }
        Skeleton::Postfix(operand) => {
            let is_same = matches!(operand, Minimal::Op { skeleton, .. } if matches!(skeleton.as_ref(), Skeleton::Postfix(_)));
            let operand_doc = print_operand(operand, is_under(operand) || is_same);
            Doc::from(vec![
                format("@[<h>", vec![]),
                operand_doc,
                doc.clone(),
                format("@]", vec![]),
            ])
        }
        Skeleton::Infix { assoc, left, right } => {
            let is_left_bare = is_under(left)
                || matches!(left, Minimal::Op { name: left_name, .. } if left_name == name && *assoc == Assoc::Left);
            let is_right_bare = is_under(right)
                || (*assoc == Assoc::Right
                    && matches!(right, Minimal::Op { skeleton, .. } if matches!(skeleton.as_ref(), Skeleton::Infix { assoc: Assoc::Right, .. })));
            Doc::from(vec![
                format("@[<b0>", vec![]),
                print_operand(left, is_left_bare),
                doc.clone(),
                print_operand(right, is_right_bare),
                format("@]", vec![]),
            ])
        }
    }
}

fn is_with(expression: &ExprNode) -> bool {
    match &expression.core {
        ExprCore::Lambda { body, .. } => is_with(body),
        ExprCore::Sequent { sequent } => is_with(&sequent.active),
        ExprCore::With { .. } => true,
        _ => false,
    }
}

fn is_elided(hyp: &HypNode) -> bool {
    match &hyp.core {
        HypCore::Defn {
            definition,
            where_defined,
            visibility,
            ..
        } => {
            let has_with =
                matches!(&definition.core, DefnCore::Operator { body, .. } if is_with(body));
            *visibility == Visibility::Hidden || has_with || *where_defined != WhereDefined::User
        }
        HypCore::Fact {
            expression,
            visibility,
            ..
        } => *visibility == Visibility::Hidden || is_with(expression),
        _ => false,
    }
}

fn print_shape(shape: Shape) -> Result<Doc> {
    if shape == 0 {
        return Ok(Doc::default());
    }
    Ok(format(
        "@[<hov1>(%a)@]",
        vec![format_delimited(&vec!["_"; shape], |item| Ok(text(item)), None)?.into()],
    ))
}

fn print_param(param: &Param) -> Result<Doc> {
    Ok(format(
        "%s%a",
        vec![param.name.as_str().into(), print_shape(param.shape)?.into()],
    ))
}

fn get_level_name(level: Level) -> &'static str {
    match level {
        Level::Constant => "CONSTANT",
        Level::State => "STATE",
        Level::Action => "ACTION",
        Level::Temporal => "TEMPORAL",
        Level::Unknown => "UNKNOWN",
    }
}

fn texts(items: &[String]) -> Result<Doc> {
    format_delimited(items, |item| Ok(text(item)), None)
}

/// A chunk of bounds that share a domain: the first bound's index and every bound's name.
struct Chunk {
    names: Vec<String>,
    index: usize,
}

/// `hyps` names the indices beyond the printer's own context, as the hypothesis deque does in
/// E_fmt.
struct Printer<'hyps> {
    context: Context,
    hyps: &'hyps [Hyp],
}

impl Printer<'_> {
    fn with_names<Output>(
        &mut self,
        names: &[String],
        body: impl FnOnce(&mut Self, Vec<String>) -> Result<Output>,
    ) -> Result<Output> {
        let idents = names
            .iter()
            .map(|name| push_name(&mut self.context, name))
            .collect();
        let result = body(self, idents)?;
        pop_names(&mut self.context, names.len());
        Ok(result)
    }

    fn print_expr(&mut self, expression: &Expr) -> Result<Doc> {
        Ok(print_minimal(&self.format_expr(expression)?))
    }

    fn print_exprs(&mut self, expressions: &[Expr]) -> Result<Doc> {
        format_delimited(expressions, |item| self.print_expr(item), None)
    }

    fn print_lambda(&mut self, params: &[Param], body: &Expr) -> Result<Doc> {
        let names: Vec<String> = params.iter().map(|param| param.name.clone()).collect();
        self.with_names(&names, |printer, _| {
            Ok(format(
                "@[<b2>LAMBDA @[<hv0>%a@] :@ %a@]",
                vec![
                    format_delimited(params, print_param, None)?.into(),
                    printer.print_expr(body)?.into(),
                ],
            ))
        })
    }

    /// fmt_bounds: names bind left to right, domains print in the enclosing context, and dittos
    /// share the previous domain.
    fn format_bounds(
        &mut self,
        bounds: &[Bound],
        body: impl FnOnce(&mut Self, Doc) -> Result<Minimal>,
    ) -> Result<Minimal> {
        let mut domains = Vec::new();
        for bound in bounds {
            domains.push(match &bound.domain {
                BoundDomain::Domain(expression) => Some(self.print_expr(expression)?),
                _ => None,
            });
        }
        let bound_names: Vec<String> = bounds.iter().map(|bound| bound.name.clone()).collect();
        self.with_names(&bound_names, |printer, names| {
            let mut chunks: Vec<Chunk> = Vec::new();
            for (index, bound) in bounds.iter().enumerate() {
                let name = names[index].clone();
                match chunks.last_mut() {
                    Some(chunk) if index > 0 && matches!(bound.domain, BoundDomain::Ditto) => {
                        chunk.names.push(name);
                    }
                    _ => chunks.push(Chunk {
                        names: vec![name],
                        index,
                    }),
                }
            }
            let bounds_doc = format_delimited(
                &chunks,
                |chunk| {
                    let names_doc = texts(&chunk.names)?;
                    Ok(match &bounds[chunk.index].domain {
                        BoundDomain::NoDomain => names_doc,
                        BoundDomain::Ditto => {
                            format("@[<hov0>%a@ \\in ??????@]", vec![names_doc.into()])
                        }
                        BoundDomain::Domain(_) => format(
                            "@[<hov0>%a@ \\in %a@]",
                            vec![
                                names_doc.into(),
                                domains[chunk.index].clone().unwrap_or_default().into(),
                            ],
                        ),
                    })
                },
                None,
            )?;
            body(printer, bounds_doc)
        })
    }

    fn print_selector(&mut self, selector: &Selector) -> Result<Doc> {
        Ok(match selector {
            Selector::Down => format(":", vec![]),
            Selector::Left => format("<<", vec![]),
            Selector::Right => format(">>", vec![]),
            Selector::At => text("@"),
            Selector::Number(value) => text(&value.to_string()),
            Selector::Instance(args) => {
                format("@[<b1>(%a)@]", vec![self.print_exprs(args)?.into()])
            }
            Selector::Label { label, args } => {
                if args.is_empty() {
                    text(label)
                } else {
                    format(
                        "@[<b2>%s@,@[<b1>(%a)@]@]",
                        vec![label.as_str().into(), self.print_exprs(args)?.into()],
                    )
                }
            }
        })
    }

    fn print_selectors(&mut self, selectors: &[Selector]) -> Result<Doc> {
        if selectors.is_empty() {
            return Ok(Doc::default());
        }
        Ok(Doc::from(vec![
            format("!", vec![]),
            format_delimited(
                selectors,
                |selector| self.print_selector(selector),
                Some(format("!", vec![])),
            )?,
        ]))
    }

    fn get_index_name(&self, index: isize) -> String {
        if index < 0 {
            return format!("#$${}", index.unsigned_abs());
        }
        if index == 0 {
            return "#$0".to_owned();
        }
        let depth = to_index(self.context.stack.len());
        if index <= depth {
            return get_bound_name(&self.context, index).unwrap_or_default();
        }
        let hyp = usize::try_from(index - depth)
            .ok()
            .and_then(|beyond| self.hyps.len().checked_sub(beyond))
            .and_then(|position| self.hyps.get(position));
        match hyp {
            Some(hyp) => get_hyp_name(hyp).unwrap_or("??? FACT ???").to_owned(),
            None => format!("#${index}"),
        }
    }

    fn format_apply(&mut self, operator: &Expr, args: &[Expr]) -> Result<Minimal> {
        match &operator.core {
            ExprCore::Lambda { params, body } => {
                let left = Minimal::Big(self.print_lambda(params, body)?);
                let right = Minimal::Atm(format("(%a)", vec![self.print_exprs(args)?.into()]));
                return Ok(Minimal::Op {
                    name: " ".to_owned(),
                    doc: format("@ ", vec![]),
                    low: 20,
                    high: 20,
                    skeleton: Box::new(Skeleton::Infix {
                        assoc: Assoc::Left,
                        left,
                        right,
                    }),
                });
            }
            ExprCore::Bang { .. } => {
                if args.is_empty() {
                    return self.format_expr(operator);
                }
                return Ok(Minimal::Atm(format(
                    "@[<b2>%a@[<b1>(%a)@]@]",
                    vec![
                        self.print_expr(operator)?.into(),
                        self.print_exprs(args)?.into(),
                    ],
                )));
            }
            ExprCore::Internal { builtin } if args.len() == 1 => {
                if *builtin == Builtin::BoxFalse || *builtin == Builtin::Unprimable {
                    return self.format_expr(&args[0]);
                }
                if *builtin == Builtin::Irregular {
                    return Ok(Minimal::Atm(format(
                        "@[<h>@<1>%s%a@<1>%s@]",
                        vec!["<[".into(), self.print_expr(&args[0])?.into(), "]>".into()],
                    )));
                }
            }
            _ => {}
        }
        let form = match &operator.core {
            ExprCore::Ix { index } => lookup_operator(&self.get_index_name(*index)),
            ExprCore::Opaque { name } => {
                let mut found = lookup_operator(name);
                found.name = format!("?{}", found.name);
                found
            }
            ExprCore::Internal { builtin } => get_standard_form(*builtin),
            _ => return Err(ObligationError::proof("Cannot print this operator")),
        };
        let get_operation = |doc: Doc, skeleton: Skeleton| Minimal::Op {
            name: form.name.clone(),
            doc,
            low: form.low,
            high: form.high,
            skeleton: Box::new(skeleton),
        };
        if args.is_empty() {
            return Ok(Minimal::Atm(text(&form.name)));
        }
        if form.fixity == Fixity::Nonfix {
            return Ok(Minimal::Atm(format(
                "@[<b2>%s@[<b1>(%a)@]@]",
                vec![form.name.as_str().into(), self.print_exprs(args)?.into()],
            )));
        }
        if form.fixity == Fixity::Prefix && args.len() == 1 {
            let is_word = form
                .name
                .chars()
                .last()
                .is_some_and(|character| character.is_ascii_alphabetic());
            let doc = if is_word {
                format("%s@ ", vec![form.name.as_str().into()])
            } else {
                text(&form.name)
            };
            return Ok(get_operation(
                doc,
                Skeleton::Prefix(self.format_expr(&args[0])?),
            ));
        }
        if form.fixity == Fixity::Postfix && args.len() == 1 {
            return Ok(get_operation(
                text(&form.name),
                Skeleton::Postfix(self.format_expr(&args[0])?),
            ));
        }
        let assoc = match form.fixity {
            Fixity::InfixLeft => Some(Assoc::Left),
            Fixity::InfixRight => Some(Assoc::Right),
            Fixity::InfixNon => Some(Assoc::Non),
            _ => None,
        };
        if let (Some(assoc), 2) = (assoc, args.len()) {
            let doc = if form.name == ".." {
                text(&form.name)
            } else {
                format("@ %s ", vec![form.name.as_str().into()])
            };
            let left = self.format_expr(&args[0])?;
            let right = self.format_expr(&args[1])?;
            return Ok(get_operation(doc, Skeleton::Infix { assoc, left, right }));
        }
        Err(ObligationError::proof(format!(
            "Arity mismatch for operator {}",
            form.name
        )))
    }

    fn format_product(&mut self, factors: &[Expr]) -> Result<Minimal> {
        match factors {
            [] => Err(ObligationError::proof("Expr.Fmt.fmt_expr: PRODUCT []")),
            [factor] => self.format_expr(factor),
            [first, rest @ ..] => {
                let left = self.format_expr(first)?;
                let right = self.format_product(rest)?;
                Ok(Minimal::Op {
                    name: "\\X".to_owned(),
                    doc: format("@ \\X ", vec![]),
                    low: 10,
                    high: 13,
                    skeleton: Box::new(Skeleton::Infix {
                        assoc: Assoc::Right,
                        left,
                        right,
                    }),
                })
            }
        }
    }

    #[allow(clippy::too_many_lines)]
    fn format_expr(&mut self, expression: &Expr) -> Result<Minimal> {
        Ok(match &expression.core {
            ExprCore::Ix { .. } | ExprCore::Opaque { .. } | ExprCore::Internal { .. } => {
                return self.format_apply(expression, &[]);
            }
            ExprCore::Lambda { params, body } => Minimal::Big(self.print_lambda(params, body)?),
            ExprCore::Bang {
                expression,
                selectors,
            } => Minimal::Atm(Doc::from(vec![
                self.print_expr(expression)?,
                self.print_selectors(selectors)?,
            ])),
            ExprCore::Apply { operator, args } => return self.format_apply(operator, args),
            ExprCore::Sequent { sequent } => Minimal::Big(self.print_sequent(sequent)?),
            ExprCore::With { expression, .. } => return self.format_expr(expression),
            ExprCore::If {
                condition,
                consequent,
                alternative,
            } => Minimal::Big(format(
                "@[<hv2>@[<b2>IF@ %a@]@ @[<b2>THEN %a@]@ @[<b2>ELSE %a@]@]",
                vec![
                    self.print_expr(condition)?.into(),
                    self.print_expr(consequent)?.into(),
                    self.print_expr(alternative)?.into(),
                ],
            )),
            ExprCore::List { bullet, items } => {
                if *bullet == Bullet::Refs && items.is_empty() {
                    return Ok(Minimal::Atm(format("TRUE", vec![])));
                }
                if *bullet == Bullet::Refs && items.len() == 1 {
                    return self.format_expr(&items[0]);
                }
                let bullet = if *bullet == Bullet::Or { "\\/" } else { "/\\" };
                Minimal::Big(format(
                    "@[<v0>%a@]",
                    vec![
                        format_delimited(
                            items,
                            |item| {
                                Ok(format(
                                    "@[<h>%s %a@]",
                                    vec![bullet.into(), self.print_expr(item)?.into()],
                                ))
                            },
                            Some(format("@,", vec![])),
                        )?
                        .into(),
                    ],
                ))
            }
            ExprCore::Let { definitions, body } => {
                let definitions_doc = format_delimited(
                    definitions,
                    |definition| self.print_definition(&definition.core),
                    Some(format("@,", vec![])),
                )?;
                let body_doc = self.print_expr(body)?;
                pop_names(&mut self.context, definitions.len());
                Minimal::Big(Doc::from(vec![
                    format("@[<hv0>LET @[<v0>", vec![]),
                    definitions_doc,
                    format("@]@\nIN  %a@]", vec![body_doc.into()]),
                ]))
            }
            ExprCore::Quant {
                quantifier,
                bounds,
                body,
            } => {
                return self.format_bounds(bounds, |printer, bounds_doc| {
                    Ok(Minimal::Big(format(
                        "@[<b3>%s @[<b0>%a@] :@ %a@]",
                        vec![
                            get_quantifier(*quantifier, "\\A", "\\E").into(),
                            bounds_doc.into(),
                            printer.print_expr(body)?.into(),
                        ],
                    )))
                });
            }
            ExprCore::Tquant {
                quantifier,
                names,
                body,
            } => {
                return self.with_names(names, |printer, names| {
                    Ok(Minimal::Big(format(
                        "@[<b4>%s @[<b0>%a@] : %a@]",
                        vec![
                            get_quantifier(*quantifier, "\\AA", "\\EE").into(),
                            texts(&names)?.into(),
                            printer.print_expr(body)?.into(),
                        ],
                    )))
                });
            }
            ExprCore::Choose { name, domain, body } => {
                let domain_doc = match domain {
                    Some(domain) => Some(self.print_expr(domain)?),
                    None => None,
                };
                return self.with_names(std::slice::from_ref(name), |printer, names| {
                    let name = names.into_iter().next().unwrap_or_default();
                    Ok(Minimal::Big(match domain_doc {
                        Some(domain_doc) => format(
                            "@[<b2>CHOOSE @[<b2>%s \\in@ %a@] :@ %a@]",
                            vec![
                                name.into(),
                                domain_doc.into(),
                                printer.print_expr(body)?.into(),
                            ],
                        ),
                        None => format(
                            "@[<b2>CHOOSE %s :@ %a@]",
                            vec![name.into(), printer.print_expr(body)?.into()],
                        ),
                    }))
                });
            }
            ExprCore::SetSt { name, domain, body } => {
                let domain_doc = self.print_expr(domain)?;
                return self.with_names(std::slice::from_ref(name), |printer, names| {
                    let name = names.into_iter().next().unwrap_or_default();
                    Ok(Minimal::Atm(format(
                        "@[<b3>{@[<b2>%s \\in@ %a@] :@ %a}@]",
                        vec![
                            name.into(),
                            domain_doc.into(),
                            printer.print_expr(body)?.into(),
                        ],
                    )))
                });
            }
            ExprCore::SetOf { element, bounds } => {
                return self.format_bounds(bounds, |printer, bounds_doc| {
                    Ok(Minimal::Atm(format(
                        "@[<b3>{%a :@ %a}@]",
                        vec![printer.print_expr(element)?.into(), bounds_doc.into()],
                    )))
                });
            }
            ExprCore::SetEnum { elements } => Minimal::Atm(format(
                "@[<h>{@[<b0>%a@]}@]",
                vec![self.print_exprs(elements)?.into()],
            )),
            ExprCore::Arrow { domain, range } => Minimal::Atm(format(
                "@[<b3>[%a ->@ %a]@]",
                vec![
                    self.print_expr(domain)?.into(),
                    self.print_expr(range)?.into(),
                ],
            )),
            ExprCore::Fcn { bounds, body } => {
                return self.format_bounds(bounds, |printer, bounds_doc| {
                    Ok(Minimal::Atm(format(
                        "@[<b3>[%a |->@ %a]@]",
                        vec![bounds_doc.into(), printer.print_expr(body)?.into()],
                    )))
                });
            }
            ExprCore::FcnApp { function, args } => {
                let target = self.format_expr(function)?;
                let is_atom = matches!(target, Minimal::Atm(_));
                Minimal::Atm(format(
                    "@[<h>%s%a%s@[<b1>[%a]@]@]",
                    vec![
                        if is_atom { "" } else { "(" }.into(),
                        print_minimal(&target).into(),
                        if is_atom { "" } else { ")" }.into(),
                        self.print_exprs(args)?.into(),
                    ],
                ))
            }
            ExprCore::Product { factors } => return self.format_product(factors),
            ExprCore::Tuple { elements } => Minimal::Atm(format(
                "@[<b2><<%a>>@]",
                vec![self.print_exprs(elements)?.into()],
            )),
            ExprCore::Rect { fields } | ExprCore::Record { fields } => {
                let separator = if matches!(expression.core, ExprCore::Rect { .. }) {
                    ":"
                } else {
                    "|->"
                };
                let pattern = format!("@[<h>%s {separator} %a@]");
                Minimal::Atm(format(
                    "@[<b1>[%a]@]",
                    vec![
                        format_delimited(
                            fields,
                            |field| {
                                Ok(format(
                                    &pattern,
                                    vec![
                                        field.name.as_str().into(),
                                        self.print_expr(&field.value)?.into(),
                                    ],
                                ))
                            },
                            None,
                        )?
                        .into(),
                    ],
                ))
            }
            ExprCore::Except { function, specs } => {
                let function_doc = self.print_expr(function)?;
                let specs_doc = format_delimited(
                    specs,
                    |spec| {
                        let mut trail = Vec::new();
                        for point in &spec.trail {
                            trail.push(match point {
                                ExceptPoint::Dot(field) => {
                                    format(".%s", vec![field.as_str().into()])
                                }
                                ExceptPoint::Apply(expression) => {
                                    format("[%a]", vec![self.print_expr(expression)?.into()])
                                }
                            });
                        }
                        Ok(format(
                            "!@[<h>%a = %a@]",
                            vec![
                                Doc::from(trail).into(),
                                self.print_expr(&spec.value)?.into(),
                            ],
                        ))
                    },
                    None,
                )?;
                Minimal::Atm(format(
                    "@[<b3>[%a EXCEPT@ @[<v0>%a@]]@]",
                    vec![function_doc.into(), specs_doc.into()],
                ))
            }
            ExprCore::Dot { expression, field } => Minimal::Op {
                name: ".".to_owned(),
                doc: format(".", vec![]),
                low: 16,
                high: 16,
                skeleton: Box::new(Skeleton::Infix {
                    assoc: Assoc::Left,
                    left: self.format_expr(expression)?,
                    right: Minimal::Atm(text(field)),
                }),
            },
            ExprCore::Sub {
                modal,
                action,
                subscript,
            }
            | ExprCore::Tsub {
                modal,
                action,
                subscript,
            } => {
                let is_box = *modal == Modal::Box;
                let open = match (matches!(expression.core, ExprCore::Sub { .. }), is_box) {
                    (true, true) => "[",
                    (true, false) => "<<",
                    (false, true) => "[][",
                    (false, false) => "<><<",
                };
                Minimal::Atm(format(
                    "@[<h>%s@[<b2>%a@]%s%a@]",
                    vec![
                        open.into(),
                        self.print_expr(action)?.into(),
                        if is_box { "]_" } else { ">>_" }.into(),
                        self.print_expr(subscript)?.into(),
                    ],
                ))
            }
            ExprCore::Fair {
                fairness,
                subscript,
                action,
            } => Minimal::Big(format(
                "@[<h>%s_%a (%a)@]",
                vec![
                    if *fairness == Fairness::Weak {
                        "WF"
                    } else {
                        "SF"
                    }
                    .into(),
                    with_parens(self.print_expr(subscript)?).into(),
                    self.print_expr(action)?.into(),
                ],
            )),
            ExprCore::Case { arms, other } => {
                let arms_doc = format_delimited(
                    arms,
                    |arm| {
                        Ok(format(
                            "@[<b2>%a ->@ %a@]",
                            vec![
                                self.print_expr(&arm.condition)?.into(),
                                self.print_expr(&arm.body)?.into(),
                            ],
                        ))
                    },
                    Some(format("@,[] ", vec![])),
                )?;
                let other_doc = match other {
                    Some(other) => format(
                        "@,[] @[<b2>OTHER ->@ %a@]",
                        vec![self.print_expr(other)?.into()],
                    ),
                    None => Doc::default(),
                };
                Minimal::Big(format(
                    "@[<v2>CASE %a%a@]",
                    vec![arms_doc.into(), other_doc.into()],
                ))
            }
            ExprCore::String { value } => {
                Minimal::Atm(format("\"%s\"", vec![value.as_str().into()]))
            }
            ExprCore::Num { integer, fraction } => Minimal::Atm(text(&if fraction.is_empty() {
                integer.clone()
            } else {
                format!("{integer}.{fraction}")
            })),
            ExprCore::At { .. } => Minimal::Atm(text("@")),
            ExprCore::Parens { expression, form } => {
                let (label, names) = match form {
                    ParenForm::Syntax => return self.format_expr(expression),
                    ParenForm::Nlabel { label, names } => (label, names.clone()),
                    ParenForm::Xlabel { label, indices } => (
                        label,
                        indices
                            .iter()
                            .map(|entry| {
                                if entry.index >= 1 && entry.index <= self.context.stack.len() {
                                    self.get_index_name(to_index(entry.index))
                                } else {
                                    format!("¶{}", entry.index)
                                }
                            })
                            .collect(),
                    ),
                };
                let inner = self.format_expr(expression)?;
                if names.is_empty() {
                    let pattern = if matches!(inner, Minimal::Op { .. }) {
                        "%s::(%a)"
                    } else {
                        "%s::%a"
                    };
                    return Ok(Minimal::Atm(format(
                        pattern,
                        vec![label.as_str().into(), print_minimal(&inner).into()],
                    )));
                }
                let names_doc = texts(&names)?;
                let pattern = match inner {
                    Minimal::Atm(_) => "%s(%a)::%a",
                    Minimal::Big(_) => "%s(%a)::(%a)",
                    Minimal::Op { .. } => "(%s(%a):: %a)",
                };
                Minimal::Atm(format(
                    pattern,
                    vec![
                        label.as_str().into(),
                        names_doc.into(),
                        print_minimal(&inner).into(),
                    ],
                ))
            }
        })
    }

    /// pp_print_defn: returns the definition's document and binds its name for what follows.
    fn print_definition(&mut self, definition: &DefnCore) -> Result<Doc> {
        match definition {
            DefnCore::Operator { name, body } | DefnCore::Bpragma { name, body, .. } => {
                if let ExprCore::Lambda {
                    params,
                    body: lambda_body,
                } = &body.core
                {
                    let param_names: Vec<String> =
                        params.iter().map(|param| param.name.clone()).collect();
                    let body_doc = self
                        .with_names(&param_names, |printer, _| printer.print_expr(lambda_body))?;
                    let name = push_name(&mut self.context, name);
                    return Ok(format(
                        "@[<b2>%s@[<b1>(%a)@] ==@ %a@]",
                        vec![
                            name.into(),
                            format_delimited(params, print_param, None)?.into(),
                            body_doc.into(),
                        ],
                    ));
                }
                let body_doc = self.print_expr(body)?;
                Ok(format(
                    "@[<b2>%s ==@ %a@]",
                    vec![push_name(&mut self.context, name).into(), body_doc.into()],
                ))
            }
            DefnCore::Instance { name, instance } => {
                let (instance_doc, args) = self.with_names(&instance.args, |printer, args| {
                    let substitutions_doc = if instance.substitutions.is_empty() {
                        Doc::default()
                    } else {
                        format(
                            "@ WITH@ %a",
                            vec![
                                format_delimited(
                                    &instance.substitutions,
                                    |entry| {
                                        Ok(format(
                                            "@[<b2>%s <- %a@]",
                                            vec![
                                                entry.name.as_str().into(),
                                                printer.print_expr(&entry.expression)?.into(),
                                            ],
                                        ))
                                    },
                                    None,
                                )?
                                .into(),
                            ],
                        )
                    };
                    let doc = format(
                        "@[<b2>INSTANCE %s%a@]",
                        vec![instance.module.as_str().into(), substitutions_doc.into()],
                    );
                    Ok((doc, args))
                })?;
                let name = push_name(&mut self.context, name);
                let head = if instance.args.is_empty() {
                    text(&name)
                } else {
                    format("%s (@[<b0>%a@])", vec![name.into(), texts(&args)?.into()])
                };
                Ok(format(
                    "@[<b2>%a == %a@]",
                    vec![head.into(), instance_doc.into()],
                ))
            }
            DefnCore::Recursive { name, shape } => {
                let name = push_name(&mut self.context, name);
                Ok(format(
                    "@[<b2>NEW CONSTANT %s%a@]",
                    vec![name.into(), print_shape(*shape)?.into()],
                ))
            }
        }
    }

    /// pp_print_hyp: prints the hypothesis in the context before it, then binds it.
    fn print_hyp(&mut self, hyp: &HypNode) -> Result<Doc> {
        match &hyp.core {
            HypCore::Fresh {
                name,
                shape,
                level,
                domain,
                domain_visibility,
            } => {
                let domain_doc = match domain {
                    Some(domain) if *domain_visibility == Visibility::Visible => {
                        Some(self.print_expr(domain)?)
                    }
                    _ => None,
                };
                let name = push_name(&mut self.context, name);
                Ok(Doc::from(vec![
                    format(
                        "NEW %s %s%a",
                        vec![
                            get_level_name(*level).into(),
                            name.into(),
                            print_shape(*shape)?.into(),
                        ],
                    ),
                    domain_doc.map_or_else(Doc::default, |domain_doc| {
                        format(" \\in %a", vec![domain_doc.into()])
                    }),
                ]))
            }
            HypCore::Flex { name } => Ok(format(
                "NEW VARIABLE %s",
                vec![push_name(&mut self.context, name).into()],
            )),
            HypCore::Defn { definition, .. } => self.print_definition(&definition.core),
            HypCore::Fact { expression, .. } => {
                let doc = format("@[<h>%a @]", vec![self.print_expr(expression)?.into()]);
                push_name(&mut self.context, "");
                Ok(doc)
            }
        }
    }

    fn print_sequent(&mut self, sequent: &Sequent) -> Result<Doc> {
        if sequent.context.is_empty() {
            return self.print_expr(&sequent.active);
        }
        let mut hyp_docs = Vec::new();
        for hyp in &sequent.context {
            if is_elided(hyp) {
                push_name(&mut self.context, get_hyp_name(hyp).unwrap_or(""));
            } else {
                hyp_docs.push(self.print_hyp(hyp)?);
            }
        }
        let active_doc = self.print_expr(&sequent.active)?;
        pop_names(&mut self.context, sequent.context.len());
        if hyp_docs.is_empty() {
            return Ok(active_doc);
        }
        Ok(Doc::from(vec![
            format("@[<v0>ASSUME @[<v0>", vec![]),
            format_delimited(&hyp_docs, |doc| Ok(doc.clone()), None)?,
            format("@]@\nPROVE  %a@]", vec![active_doc.into()]),
        ]))
    }
}

fn get_quantifier(
    quantifier: Quantifier,
    forall: &'static str,
    exists: &'static str,
) -> &'static str {
    if quantifier == Quantifier::Forall {
        forall
    } else {
        exists
    }
}

pub fn print_expression(hyps: &[Hyp], expression: &Expr) -> Result<Doc> {
    Printer {
        context: create_context(),
        hyps,
    }
    .print_expr(expression)
}

pub fn print_sequent(sequent: &Sequent) -> Result<Doc> {
    Printer {
        context: create_context(),
        hyps: &[],
    }
    .print_sequent(sequent)
}

pub fn format_obligation(sequent: &Sequent) -> Result<String> {
    let rendered = render_doc(
        &format("@[<b0>%a@]", vec![print_sequent(sequent)?.into()]),
        68,
    )?;
    Ok(rendered.trim_end_matches(is_js_space).to_owned())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expression::{
        CaseArm, Defn, ExceptSpec, Field, InstanceDefinition, Substitution, Time, XlabelIndex,
        expr, hyp,
    };
    use crate::pragma::OldMethod;

    /// The JSON the TypeScript serializes its inputs and results to.
    #[derive(Clone, Debug)]
    enum Json {
        Null,
        Bool(bool),
        Number(f64),
        Text(String),
        Array(Vec<Json>),
        Object(Vec<(String, Json)>),
    }

    struct JsonReader<'text> {
        characters: std::iter::Peekable<std::str::Chars<'text>>,
    }

    impl JsonReader<'_> {
        fn skip_space(&mut self) {
            while self
                .characters
                .peek()
                .is_some_and(char::is_ascii_whitespace)
            {
                self.characters.next();
            }
        }

        fn read_string(&mut self) -> String {
            self.skip_space();
            assert_eq!(self.characters.next(), Some('"'));
            let mut value = String::new();
            let mut pending_high = None;
            loop {
                let character = self.characters.next().expect("unterminated string");
                if character == '"' {
                    return value;
                }
                if character != '\\' {
                    value.push(character);
                    continue;
                }
                let escaped = self.characters.next().expect("escape");
                let unescaped = match escaped {
                    'n' => '\n',
                    't' => '\t',
                    'r' => '\r',
                    'b' => '\u{8}',
                    'f' => '\u{c}',
                    'u' => {
                        let digits: String =
                            (0..4).filter_map(|_| self.characters.next()).collect();
                        let code = u32::from_str_radix(&digits, 16).expect("hex");
                        if (0xd800..0xdc00).contains(&code) {
                            pending_high = Some(code);
                            continue;
                        }
                        let code = pending_high.take().map_or(code, |high| {
                            0x10000 + ((high - 0xd800) << 10) + (code - 0xdc00)
                        });
                        char::from_u32(code).expect("scalar")
                    }
                    other => other,
                };
                value.push(unescaped);
            }
        }

        fn read(&mut self) -> Json {
            self.skip_space();
            match self.characters.peek().copied() {
                Some('"') => Json::Text(self.read_string()),
                Some('[') => {
                    self.characters.next();
                    let mut items = Vec::new();
                    self.skip_space();
                    if self.characters.peek() == Some(&']') {
                        self.characters.next();
                        return Json::Array(items);
                    }
                    loop {
                        items.push(self.read());
                        self.skip_space();
                        if self.characters.next() == Some(']') {
                            return Json::Array(items);
                        }
                    }
                }
                Some('{') => {
                    self.characters.next();
                    let mut entries = Vec::new();
                    self.skip_space();
                    if self.characters.peek() == Some(&'}') {
                        self.characters.next();
                        return Json::Object(entries);
                    }
                    loop {
                        let key = self.read_string();
                        self.skip_space();
                        assert_eq!(self.characters.next(), Some(':'));
                        entries.push((key, self.read()));
                        self.skip_space();
                        if self.characters.next() == Some('}') {
                            return Json::Object(entries);
                        }
                    }
                }
                _ => {
                    let mut word = String::new();
                    while let Some(&character) = self.characters.peek() {
                        if !(character.is_ascii_alphanumeric() || "+-.".contains(character)) {
                            break;
                        }
                        word.push(character);
                        self.characters.next();
                    }
                    match word.as_str() {
                        "null" => Json::Null,
                        "true" => Json::Bool(true),
                        "false" => Json::Bool(false),
                        _ => Json::Number(word.parse().expect("number")),
                    }
                }
            }
        }
    }

    fn parse_json(text: &str) -> Json {
        JsonReader {
            characters: text.chars().peekable(),
        }
        .read()
    }

    impl Json {
        fn get(&self, key: &str) -> Option<&Self> {
            match self {
                Self::Object(entries) => entries
                    .iter()
                    .find(|entry| entry.0 == key)
                    .map(|entry| &entry.1),
                _ => None,
            }
        }

        fn field(&self, key: &str) -> &Self {
            self.get(key)
                .unwrap_or_else(|| panic!("missing {key} in {self:?}"))
        }

        fn text(&self, key: &str) -> String {
            match self.field(key) {
                Self::Text(value) => value.clone(),
                other => panic!("not a string: {other:?}"),
            }
        }

        fn number(&self, key: &str) -> usize {
            match self.field(key) {
                #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
                Self::Number(value) => *value as usize,
                other => panic!("not a number: {other:?}"),
            }
        }

        fn signed(&self, key: &str) -> isize {
            match self.field(key) {
                #[allow(clippy::cast_possible_truncation)]
                Self::Number(value) => *value as isize,
                other => panic!("not a number: {other:?}"),
            }
        }

        fn items(&self, key: &str) -> &[Self] {
            match self.field(key) {
                Self::Array(items) => items,
                other => panic!("not an array: {other:?}"),
            }
        }

        fn texts(&self, key: &str) -> Vec<String> {
            self.items(key)
                .iter()
                .map(|item| match item {
                    Self::Text(value) => value.clone(),
                    other => panic!("not a string: {other:?}"),
                })
                .collect()
        }
    }

    fn to_exprs(items: &[Json]) -> Vec<Expr> {
        items.iter().map(to_expr).collect()
    }

    const BUILTINS: &[Builtin] = &[
        Builtin::TRUE,
        Builtin::FALSE,
        Builtin::Implies,
        Builtin::Equiv,
        Builtin::Conj,
        Builtin::Disj,
        Builtin::Neg,
        Builtin::Eq,
        Builtin::Neq,
        Builtin::STRING,
        Builtin::BOOLEAN,
        Builtin::SUBSET,
        Builtin::UNION,
        Builtin::DOMAIN,
        Builtin::Subseteq,
        Builtin::Mem,
        Builtin::Notmem,
        Builtin::Setminus,
        Builtin::Cap,
        Builtin::Cup,
        Builtin::Prime,
        Builtin::StrongPrime,
        Builtin::Leadsto,
        Builtin::ENABLED,
        Builtin::UNCHANGED,
        Builtin::Cdot,
        Builtin::Actplus,
        Builtin::BoxTrue,
        Builtin::BoxFalse,
        Builtin::Diamond,
        Builtin::Nat,
        Builtin::Int,
        Builtin::Real,
        Builtin::Plus,
        Builtin::Minus,
        Builtin::Uminus,
        Builtin::Times,
        Builtin::Ratio,
        Builtin::Quotient,
        Builtin::Remainder,
        Builtin::Exp,
        Builtin::Infinity,
        Builtin::Lteq,
        Builtin::Lt,
        Builtin::Gteq,
        Builtin::Gt,
        Builtin::Divides,
        Builtin::Range,
        Builtin::Seq,
        Builtin::Len,
        Builtin::BSeq,
        Builtin::Cat,
        Builtin::Append,
        Builtin::Head,
        Builtin::Tail,
        Builtin::SubSeq,
        Builtin::SelectSeq,
        Builtin::OneArg,
        Builtin::Extend,
        Builtin::Print,
        Builtin::PrintT,
        Builtin::Assert,
        Builtin::JavaTime,
        Builtin::TLCGet,
        Builtin::TLCSet,
        Builtin::Permutations,
        Builtin::SortSeq,
        Builtin::RandomElement,
        Builtin::Any,
        Builtin::ToString,
        Builtin::Unprimable,
        Builtin::Irregular,
    ];

    fn to_builtin(name: &str) -> Builtin {
        BUILTINS
            .iter()
            .copied()
            .find(|builtin| builtin.name() == name)
            .unwrap_or_else(|| panic!("unknown builtin {name}"))
    }

    fn to_level(name: &str) -> Level {
        match name {
            "Constant" => Level::Constant,
            "State" => Level::State,
            "Action" => Level::Action,
            "Temporal" => Level::Temporal,
            _ => Level::Unknown,
        }
    }

    fn to_visibility(name: &str) -> Visibility {
        if name == "Hidden" {
            Visibility::Hidden
        } else {
            Visibility::Visible
        }
    }

    fn to_params(items: &[Json]) -> Vec<Param> {
        items
            .iter()
            .map(|item| Param {
                name: item.text("name"),
                shape: item.number("shape"),
                location: None,
            })
            .collect()
    }

    fn to_bounds(items: &[Json]) -> Vec<Bound> {
        items
            .iter()
            .map(|item| {
                let domain = item.field("domain");
                Bound {
                    name: item.text("name"),
                    level: to_level(&item.text("level")),
                    domain: match domain.text("kind").as_str() {
                        "NoDomain" => BoundDomain::NoDomain,
                        "Ditto" => BoundDomain::Ditto,
                        _ => BoundDomain::Domain(to_expr(domain.field("expression"))),
                    },
                }
            })
            .collect()
    }

    fn to_selector(item: &Json) -> Selector {
        match item.text("kind").as_str() {
            "Down" => Selector::Down,
            "Number" => Selector::Number(item.number("value")),
            "Left" => Selector::Left,
            "Right" => Selector::Right,
            "At" => Selector::At,
            "Instance" => Selector::Instance(to_exprs(item.items("args"))),
            _ => Selector::Label {
                label: item.text("label"),
                args: to_exprs(item.items("args")),
            },
        }
    }

    fn to_defn(item: &Json) -> Defn {
        let name = item.text("name");
        let core = match item.text("kind").as_str() {
            "Recursive" => DefnCore::Recursive {
                name,
                shape: item.number("shape"),
            },
            "Operator" => DefnCore::Operator {
                name,
                body: to_expr(item.field("body")),
            },
            "Bpragma" => DefnCore::Bpragma {
                name,
                body: to_expr(item.field("body")),
                methods: Vec::new(),
            },
            _ => {
                let instance = item.field("instance");
                DefnCore::Instance {
                    name,
                    instance: InstanceDefinition {
                        args: instance.texts("args"),
                        module: instance.text("module"),
                        substitutions: instance
                            .items("substitutions")
                            .iter()
                            .map(|entry| Substitution {
                                name: entry.text("name"),
                                expression: to_expr(entry.field("expression")),
                            })
                            .collect(),
                        location: None,
                    },
                }
            }
        };
        Defn {
            core,
            location: None,
        }
    }

    fn to_hyp(item: &Json) -> Hyp {
        hyp(match item.text("kind").as_str() {
            "Fresh" => HypCore::Fresh {
                name: item.text("name"),
                shape: item.number("shape"),
                level: to_level(&item.text("level")),
                domain: item.get("domain").map(to_expr),
                domain_visibility: to_visibility(&item.text("domainVisibility")),
            },
            "Flex" => HypCore::Flex {
                name: item.text("name"),
            },
            "Defn" => HypCore::Defn {
                definition: to_defn(item.field("definition")),
                where_defined: match item.field("whereDefined") {
                    Json::Text(name) if name == "User" => WhereDefined::User,
                    Json::Text(_) => WhereDefined::Builtin,
                    _ => WhereDefined::Proof(Time::Now),
                },
                visibility: to_visibility(&item.text("visibility")),
                is_local: false,
                is_constness_unset: false,
            },
            _ => HypCore::Fact {
                expression: to_expr(item.field("expression")),
                visibility: to_visibility(&item.text("visibility")),
                time: Time::Now,
                use_location: None,
            },
        })
    }

    fn to_sequent(item: &Json) -> Sequent {
        Sequent {
            context: item.items("context").iter().map(to_hyp).collect(),
            active: to_expr(item.field("active")),
        }
    }

    fn to_modal(item: &Json) -> Modal {
        if item.text("modal") == "Box" {
            Modal::Box
        } else {
            Modal::Dia
        }
    }

    fn to_quantifier(item: &Json) -> Quantifier {
        if item.text("quantifier") == "Forall" {
            Quantifier::Forall
        } else {
            Quantifier::Exists
        }
    }

    fn to_fields(item: &Json) -> Vec<Field> {
        item.items("fields")
            .iter()
            .map(|field| Field {
                name: field.text("name"),
                value: to_expr(field.field("value")),
            })
            .collect()
    }

    fn to_paren_form(form: &Json) -> ParenForm {
        match form.text("kind").as_str() {
            "Syntax" => ParenForm::Syntax,
            "Nlabel" => ParenForm::Nlabel {
                label: form.text("label"),
                names: form.texts("names"),
            },
            _ => ParenForm::Xlabel {
                label: form.text("label"),
                indices: form
                    .items("indices")
                    .iter()
                    .map(|entry| XlabelIndex {
                        name: entry.text("name"),
                        index: entry.number("index"),
                    })
                    .collect(),
            },
        }
    }

    fn to_except_spec(spec: &Json) -> ExceptSpec {
        ExceptSpec {
            trail: spec
                .items("trail")
                .iter()
                .map(|point| {
                    if point.text("kind") == "Dot" {
                        ExceptPoint::Dot(point.text("field"))
                    } else {
                        ExceptPoint::Apply(to_expr(point.field("expression")))
                    }
                })
                .collect(),
            value: to_expr(spec.field("value")),
        }
    }

    #[allow(clippy::too_many_lines)]
    fn to_expr(item: &Json) -> Expr {
        let child = |key: &str| to_expr(item.field(key));
        expr(match item.text("kind").as_str() {
            "Ix" => ExprCore::Ix {
                index: item.signed("index"),
            },
            "Opaque" => ExprCore::Opaque {
                name: item.text("name"),
            },
            "Internal" => ExprCore::Internal {
                builtin: to_builtin(&item.text("builtin")),
            },
            "Lambda" => ExprCore::Lambda {
                params: to_params(item.items("params")),
                body: child("body"),
            },
            "Sequent" => ExprCore::Sequent {
                sequent: to_sequent(item.field("sequent")),
            },
            "Bang" => ExprCore::Bang {
                expression: child("expression"),
                selectors: item.items("selectors").iter().map(to_selector).collect(),
            },
            "Apply" => ExprCore::Apply {
                operator: child("operator"),
                args: to_exprs(item.items("args")),
            },
            "With" => ExprCore::With {
                expression: child("expression"),
                method: OldMethod {
                    name: item.field("method").text("name"),
                    tactic: None,
                    timeout: None,
                },
            },
            "If" => ExprCore::If {
                condition: child("condition"),
                consequent: child("consequent"),
                alternative: child("alternative"),
            },
            "List" => ExprCore::List {
                bullet: match item.text("bullet").as_str() {
                    "And" => Bullet::And,
                    "Or" => Bullet::Or,
                    _ => Bullet::Refs,
                },
                items: to_exprs(item.items("items")),
            },
            "Let" => ExprCore::Let {
                definitions: item.items("definitions").iter().map(to_defn).collect(),
                body: child("body"),
            },
            "Quant" => ExprCore::Quant {
                quantifier: to_quantifier(item),
                bounds: to_bounds(item.items("bounds")),
                body: child("body"),
            },
            "Tquant" => ExprCore::Tquant {
                quantifier: to_quantifier(item),
                names: item.texts("names"),
                body: child("body"),
            },
            "Choose" => ExprCore::Choose {
                name: item.text("name"),
                domain: item.get("domain").map(to_expr),
                body: child("body"),
            },
            "SetSt" => ExprCore::SetSt {
                name: item.text("name"),
                domain: child("domain"),
                body: child("body"),
            },
            "SetOf" => ExprCore::SetOf {
                element: child("element"),
                bounds: to_bounds(item.items("bounds")),
            },
            "SetEnum" => ExprCore::SetEnum {
                elements: to_exprs(item.items("elements")),
            },
            "Product" => ExprCore::Product {
                factors: to_exprs(item.items("factors")),
            },
            "Tuple" => ExprCore::Tuple {
                elements: to_exprs(item.items("elements")),
            },
            "Fcn" => ExprCore::Fcn {
                bounds: to_bounds(item.items("bounds")),
                body: child("body"),
            },
            "FcnApp" => ExprCore::FcnApp {
                function: child("function"),
                args: to_exprs(item.items("args")),
            },
            "Arrow" => ExprCore::Arrow {
                domain: child("domain"),
                range: child("range"),
            },
            "Rect" => ExprCore::Rect {
                fields: to_fields(item),
            },
            "Record" => ExprCore::Record {
                fields: to_fields(item),
            },
            "Except" => ExprCore::Except {
                function: child("function"),
                specs: item.items("specs").iter().map(to_except_spec).collect(),
            },
            "Dot" => ExprCore::Dot {
                expression: child("expression"),
                field: item.text("field"),
            },
            "Sub" => ExprCore::Sub {
                modal: to_modal(item),
                action: child("action"),
                subscript: child("subscript"),
            },
            "Tsub" => ExprCore::Tsub {
                modal: to_modal(item),
                action: child("action"),
                subscript: child("subscript"),
            },
            "Fair" => ExprCore::Fair {
                fairness: if item.text("fairness") == "Weak" {
                    Fairness::Weak
                } else {
                    Fairness::Strong
                },
                subscript: child("subscript"),
                action: child("action"),
            },
            "Case" => ExprCore::Case {
                arms: item
                    .items("arms")
                    .iter()
                    .map(|arm| CaseArm {
                        condition: to_expr(arm.field("condition")),
                        body: to_expr(arm.field("body")),
                    })
                    .collect(),
                other: item.get("other").map(to_expr),
            },
            "String" => ExprCore::String {
                value: item.text("value"),
            },
            "Num" => ExprCore::Num {
                integer: item.text("integer"),
                fraction: item.text("fraction"),
            },
            "At" => ExprCore::At {
                is_except: matches!(item.field("isExcept"), Json::Bool(true)),
            },
            "Parens" => ExprCore::Parens {
                expression: child("expression"),
                form: to_paren_form(item.field("form")),
            },
            other => panic!("unknown kind {other}"),
        })
    }

    /// Prints each case the TypeScript printed and returns how many differ.
    fn check_cases(cases: &str) -> usize {
        let Json::Array(cases) = parse_json(cases) else {
            panic!("cases are an array");
        };
        assert!(!cases.is_empty());
        let mut failures = 0;
        for case in &cases {
            let input = case.field("input");
            let result = match case.text("mode").as_str() {
                "obligation" => format_obligation(&to_sequent(input)),
                "sequent" => print_sequent(&to_sequent(input)).and_then(|doc| render_doc(&doc, 68)),
                _ => {
                    let hyps: Vec<Hyp> = match case.get("hyps") {
                        Some(Json::Array(items)) => items.iter().map(to_hyp).collect(),
                        _ => Vec::new(),
                    };
                    print_expression(&hyps, &to_expr(input)).and_then(|doc| render_doc(&doc, 68))
                }
            };
            let actual = result.map_err(|error| format!("{}: {}", error.name(), error.message()));
            let expected = if case.get("output").is_some() {
                Ok(case.text("output"))
            } else {
                Err(case.text("error"))
            };
            if actual != expected {
                failures += 1;
                eprintln!("mismatch on {case:?}\nexpected {expected:?}\nactual   {actual:?}");
            }
        }
        failures
    }

    /// Each operator's fixity, precedence and associativity, wrapping at the margin, binders that
    /// clash, hidden and elided hypotheses, selectors, labels, strings with escapes and non-ASCII
    /// text and the printer's errors; then random expressions and sequents. Generated and printed
    /// by `src/obligations/printer.ts` under Bun.
    const CASES: &str = r##"[
{"mode":"expression","input":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Opaque","name":"a"},{"kind":"Opaque","name":"c"}]},{"kind":"Opaque","name":"d"}]},"hyps":[],"output":"?a + ?c + ?d"},
{"mode":"expression","input":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Opaque","name":"a"},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Opaque","name":"c"},{"kind":"Opaque","name":"d"}]}]},"hyps":[],"output":"?a + (?c + ?d)"},
{"mode":"expression","input":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Minus"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Minus"},"args":[{"kind":"Opaque","name":"a"},{"kind":"Opaque","name":"c"}]},{"kind":"Opaque","name":"d"}]},"hyps":[],"output":"?a - ?c - ?d"},
{"mode":"expression","input":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Opaque","name":"a"},{"kind":"Opaque","name":"c"}]},{"kind":"Opaque","name":"d"}]},"hyps":[],"output":"(?a => ?c) => ?d"},
{"mode":"expression","input":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Opaque","name":"a"},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Opaque","name":"c"},{"kind":"Opaque","name":"d"}]}]},"hyps":[],"output":"?a => (?c => ?d)"},
{"mode":"expression","input":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Opaque","name":"a"},{"kind":"Opaque","name":"c"}]},{"kind":"Opaque","name":"d"}]},"hyps":[],"output":"(?a \\/ ?c) /\\ ?d"},
{"mode":"expression","input":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Times"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Opaque","name":"a"},{"kind":"Opaque","name":"c"}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Exp"},"args":[{"kind":"Opaque","name":"c"},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Exp"},"args":[{"kind":"Opaque","name":"a"},{"kind":"Opaque","name":"d"}]}]}]},"hyps":[],"output":"(?a + ?c) * ?c ^ (?a ^ ?d)"},
{"mode":"expression","input":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Exp"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Exp"},"args":[{"kind":"Opaque","name":"a"},{"kind":"Opaque","name":"c"}]},{"kind":"Opaque","name":"d"}]},"hyps":[],"output":"(?a ^ ?c) ^ ?d"},
{"mode":"expression","input":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Neg"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Neg"},"args":[{"kind":"Opaque","name":"a"}]}]},"hyps":[],"output":"~~?a"},
{"mode":"expression","input":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Neg"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Opaque","name":"a"},{"kind":"Opaque","name":"c"}]}]},"hyps":[],"output":"~?a = ?c"},
{"mode":"expression","input":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Opaque","name":"a"}]}]},"hyps":[],"output":"?a''"},
{"mode":"expression","input":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Opaque","name":"a"},{"kind":"Opaque","name":"c"}]}]},"hyps":[],"output":"(?a + ?c)'"},
{"mode":"expression","input":{"kind":"Apply","operator":{"kind":"Internal","builtin":"SUBSET"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"SUBSET"},"args":[{"kind":"Opaque","name":"a"}]}]},"hyps":[],"output":"SUBSET SUBSET ?a"},
{"mode":"expression","input":{"kind":"Apply","operator":{"kind":"Internal","builtin":"DOMAIN"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"UNION"},"args":[{"kind":"Opaque","name":"a"}]}]},"hyps":[],"output":"DOMAIN UNION ?a"},
{"mode":"expression","input":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Uminus"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Uminus"},"args":[{"kind":"Opaque","name":"a"}]}]},"hyps":[],"output":"--?a"},
{"mode":"expression","input":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Range"},"args":[{"kind":"Opaque","name":"a"},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Opaque","name":"c"},{"kind":"Opaque","name":"d"}]}]},"hyps":[],"output":"?a..?c + ?d"},
{"mode":"expression","input":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Divides"},"args":[{"kind":"Opaque","name":"a"},{"kind":"Opaque","name":"c"}]},"hyps":[],"output":"?a ?| ?c"},
{"mode":"expression","input":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Irregular"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Opaque","name":"a"},{"kind":"Opaque","name":"c"}]}]},"hyps":[],"output":"<[?a + ?c]>"},
{"mode":"expression","input":{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxFalse"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Opaque","name":"a"},{"kind":"Opaque","name":"c"}]}]},"hyps":[],"output":"?a + ?c"},
{"mode":"expression","input":{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Opaque","name":"a"},{"kind":"Opaque","name":"c"}]}]},"hyps":[],"output":"[](?a + ?c)"},
{"mode":"expression","input":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Unprimable"},"args":[{"kind":"Opaque","name":"a"}]},"hyps":[],"output":"?a"},
{"mode":"expression","input":{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Opaque","name":"a"},{"kind":"Opaque","name":"c"}]}]},"hyps":[],"output":"ENABLED (?a /\\ ?c)"},
{"mode":"expression","input":{"kind":"Apply","operator":{"kind":"Opaque","name":"+"},"args":[{"kind":"Opaque","name":"a"},{"kind":"Opaque","name":"c"}]},"hyps":[],"output":"?a ?+ ?c"},
{"mode":"expression","input":{"kind":"Apply","operator":{"kind":"Opaque","name":"\\lnot"},"args":[{"kind":"Opaque","name":"a"}]},"hyps":[],"output":"?~?a"},
{"mode":"expression","input":{"kind":"Apply","operator":{"kind":"Opaque","name":"^+"},"args":[{"kind":"Apply","operator":{"kind":"Opaque","name":"^#"},"args":[{"kind":"Opaque","name":"a"}]}]},"hyps":[],"output":"?a?^#?^+"},
{"mode":"expression","input":{"kind":"Apply","operator":{"kind":"Opaque","name":"Foo"},"args":[{"kind":"Opaque","name":"a"},{"kind":"Opaque","name":"c"}]},"hyps":[],"output":"?Foo(?a, ?c)"},
{"mode":"expression","input":{"kind":"Apply","operator":{"kind":"Opaque","name":"Foo"},"args":[]},"hyps":[],"output":"?Foo"},
{"mode":"expression","input":{"kind":"Opaque","name":"\\in"},"hyps":[],"output":"?\\in"},
{"mode":"expression","input":{"kind":"Product","factors":[{"kind":"Opaque","name":"a"},{"kind":"Product","factors":[{"kind":"Opaque","name":"c"},{"kind":"Opaque","name":"d"}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Opaque","name":"a"},{"kind":"Opaque","name":"c"}]}]},"hyps":[],"output":"?a \\X (?c \\X ?d) \\X (?a + ?c)"},
{"mode":"expression","input":{"kind":"Product","factors":[{"kind":"Product","factors":[{"kind":"Opaque","name":"c"},{"kind":"Opaque","name":"d"}]},{"kind":"Opaque","name":"a"}]},"hyps":[],"output":"(?c \\X ?d) \\X ?a"},
{"mode":"expression","input":{"kind":"Product","factors":[]},"hyps":[],"error":"TlaProofError: Expr.Fmt.fmt_expr: PRODUCT []"},
{"mode":"expression","input":{"kind":"Apply","operator":{"kind":"If","condition":{"kind":"Opaque","name":"a"},"consequent":{"kind":"Opaque","name":"c"},"alternative":{"kind":"Opaque","name":"d"}},"args":[{"kind":"Opaque","name":"a"}]},"hyps":[],"error":"TlaProofError: Cannot print this operator"},
{"mode":"expression","input":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Opaque","name":"a"},{"kind":"Opaque","name":"c"},{"kind":"Opaque","name":"d"}]},"hyps":[],"error":"TlaProofError: Arity mismatch for operator +"},
{"mode":"expression","input":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Neg"},"args":[{"kind":"Opaque","name":"a"},{"kind":"Opaque","name":"c"}]},"hyps":[],"error":"TlaProofError: Arity mismatch for operator ~"},
{"mode":"expression","input":{"kind":"Dot","expression":{"kind":"Dot","expression":{"kind":"Opaque","name":"a"},"field":"b"},"field":"c"},"hyps":[],"output":"?a.b.c"},
{"mode":"expression","input":{"kind":"Dot","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Opaque","name":"a"},{"kind":"Opaque","name":"c"}]},"field":"f"},"hyps":[],"output":"(?a + ?c).f"},
{"mode":"expression","input":{"kind":"FcnApp","function":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Opaque","name":"a"},{"kind":"Opaque","name":"c"}]},"args":[{"kind":"Opaque","name":"a"},{"kind":"Opaque","name":"c"}]},"hyps":[],"output":"(?a + ?c)[?a, ?c]"},
{"mode":"expression","input":{"kind":"FcnApp","function":{"kind":"FcnApp","function":{"kind":"Opaque","name":"a"},"args":[{"kind":"Opaque","name":"c"}]},"args":[{"kind":"Opaque","name":"d"}]},"hyps":[],"output":"?a[?c][?d]"},
{"mode":"expression","input":{"kind":"FcnApp","function":{"kind":"If","condition":{"kind":"Opaque","name":"a"},"consequent":{"kind":"Opaque","name":"c"},"alternative":{"kind":"Opaque","name":"d"}},"args":[{"kind":"Opaque","name":"d"}]},"hyps":[],"output":"(IF ?a THEN ?c ELSE ?d)[?d]"},
{"mode":"expression","input":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[]},"hyps":[],"output":"/\\"},
{"mode":"expression","input":{"kind":"List","bullet":"And","items":[{"kind":"Opaque","name":"AVeryLongIdentifierNumber1ThatTakesSpace"},{"kind":"Opaque","name":"AVeryLongIdentifierNumber2ThatTakesSpace"},{"kind":"Opaque","name":"AVeryLongIdentifierNumber3ThatTakesSpace"},{"kind":"Opaque","name":"AVeryLongIdentifierNumber4ThatTakesSpace"}]},"hyps":[],"output":"/\\ ?AVeryLongIdentifierNumber1ThatTakesSpace\n/\\ ?AVeryLongIdentifierNumber2ThatTakesSpace\n/\\ ?AVeryLongIdentifierNumber3ThatTakesSpace\n/\\ ?AVeryLongIdentifierNumber4ThatTakesSpace"},
{"mode":"expression","input":{"kind":"List","bullet":"Refs","items":[]},"hyps":[],"output":"TRUE"},
{"mode":"expression","input":{"kind":"List","bullet":"Refs","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Opaque","name":"a"},{"kind":"Opaque","name":"c"}]}]},"hyps":[],"output":"?a + ?c"},
{"mode":"expression","input":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Opaque","name":"AVeryLongIdentifierNumber1ThatTakesSpace"},{"kind":"Opaque","name":"AVeryLongIdentifierNumber2ThatTakesSpace"}]},{"kind":"Opaque","name":"AVeryLongIdentifierNumber3ThatTakesSpace"}]},{"kind":"Opaque","name":"AVeryLongIdentifierNumber4ThatTakesSpace"}]},{"kind":"Opaque","name":"AVeryLongIdentifierNumber5ThatTakesSpace"}]},{"kind":"Opaque","name":"AVeryLongIdentifierNumber6ThatTakesSpace"}]},"hyps":[],"output":"?AVeryLongIdentifierNumber1ThatTakesSpace\n/\\ ?AVeryLongIdentifierNumber2ThatTakesSpace\n/\\ ?AVeryLongIdentifierNumber3ThatTakesSpace\n/\\ ?AVeryLongIdentifierNumber4ThatTakesSpace\n/\\ ?AVeryLongIdentifierNumber5ThatTakesSpace\n/\\ ?AVeryLongIdentifierNumber6ThatTakesSpace"},
{"mode":"expression","input":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Opaque","name":"AVeryLongIdentifierNumber1ThatTakesSpace"},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Opaque","name":"AVeryLongIdentifierNumber2ThatTakesSpace"},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Opaque","name":"AVeryLongIdentifierNumber3ThatTakesSpace"},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Opaque","name":"AVeryLongIdentifierNumber4ThatTakesSpace"},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Opaque","name":"AVeryLongIdentifierNumber5ThatTakesSpace"},{"kind":"Opaque","name":"AVeryLongIdentifierNumber6ThatTakesSpace"}]}]}]}]}]},"hyps":[],"output":"?AVeryLongIdentifierNumber1ThatTakesSpace\n=> (?AVeryLongIdentifierNumber2ThatTakesSpace\n    => (?AVeryLongIdentifierNumber3ThatTakesSpace\n        => (?AVeryLongIdentifierNumber4ThatTakesSpace\n            => (?AVeryLongIdentifierNumber5ThatTakesSpace\n                => ?AVeryLongIdentifierNumber6ThatTakesSpace))))"},
{"mode":"expression","input":{"kind":"SetEnum","elements":[{"kind":"Opaque","name":"AVeryLongIdentifierNumber1ThatTakesSpace"},{"kind":"Opaque","name":"AVeryLongIdentifierNumber2ThatTakesSpace"},{"kind":"Opaque","name":"AVeryLongIdentifierNumber3ThatTakesSpace"},{"kind":"Opaque","name":"AVeryLongIdentifierNumber4ThatTakesSpace"},{"kind":"Opaque","name":"AVeryLongIdentifierNumber5ThatTakesSpace"}]},"hyps":[],"output":"{?AVeryLongIdentifierNumber1ThatTakesSpace,\n ?AVeryLongIdentifierNumber2ThatTakesSpace,\n ?AVeryLongIdentifierNumber3ThatTakesSpace,\n ?AVeryLongIdentifierNumber4ThatTakesSpace,\n ?AVeryLongIdentifierNumber5ThatTakesSpace}"},
{"mode":"expression","input":{"kind":"Tuple","elements":[{"kind":"Opaque","name":"AVeryLongIdentifierNumber1ThatTakesSpace"},{"kind":"Opaque","name":"AVeryLongIdentifierNumber2ThatTakesSpace"},{"kind":"Opaque","name":"AVeryLongIdentifierNumber3ThatTakesSpace"},{"kind":"Opaque","name":"AVeryLongIdentifierNumber4ThatTakesSpace"},{"kind":"Opaque","name":"AVeryLongIdentifierNumber5ThatTakesSpace"}]},"hyps":[],"output":"<<?AVeryLongIdentifierNumber1ThatTakesSpace,\n  ?AVeryLongIdentifierNumber2ThatTakesSpace,\n  ?AVeryLongIdentifierNumber3ThatTakesSpace,\n  ?AVeryLongIdentifierNumber4ThatTakesSpace,\n  ?AVeryLongIdentifierNumber5ThatTakesSpace>>"},
{"mode":"expression","input":{"kind":"Apply","operator":{"kind":"Opaque","name":"LongOperator"},"args":[{"kind":"Opaque","name":"AVeryLongIdentifierNumber1ThatTakesSpace"},{"kind":"Opaque","name":"AVeryLongIdentifierNumber2ThatTakesSpace"},{"kind":"Opaque","name":"AVeryLongIdentifierNumber3ThatTakesSpace"},{"kind":"Opaque","name":"AVeryLongIdentifierNumber4ThatTakesSpace"}]},"hyps":[],"output":"?LongOperator(?AVeryLongIdentifierNumber1ThatTakesSpace,\n              ?AVeryLongIdentifierNumber2ThatTakesSpace,\n              ?AVeryLongIdentifierNumber3ThatTakesSpace,\n              ?AVeryLongIdentifierNumber4ThatTakesSpace)"},
{"mode":"expression","input":{"kind":"String","value":"he said \"hi\" naïve λ → ∀ 😀"},"hyps":[],"output":"\"he said \"hi\" naïve λ → ∀ 😀\""},
{"mode":"expression","input":{"kind":"Tuple","elements":[{"kind":"String","value":"λλλλλλλλλλλλλλλλλλλλλλλλλλλλλλ"},{"kind":"String","value":"ααααααααααααααααααααααααααααααααααααα"},{"kind":"String","value":"βββββββββββββββββββββββ"}]},"hyps":[],"output":"<<\"λλλλλλλλλλλλλλλλλλλλλλλλλλλλλλ\",\n  \"ααααααααααααααααααααααααααααααααααααα\",\n  \"βββββββββββββββββββββββ\">>"},
{"mode":"expression","input":{"kind":"Num","integer":"12","fraction":"50"},"hyps":[],"output":"12.50"},
{"mode":"expression","input":{"kind":"Bang","expression":{"kind":"Opaque","name":"a"},"selectors":[{"kind":"Down"},{"kind":"Number","value":2},{"kind":"Left"},{"kind":"Right"},{"kind":"At"},{"kind":"Instance","args":[{"kind":"Opaque","name":"a"},{"kind":"Opaque","name":"c"}]},{"kind":"Label","label":"L","args":[]},{"kind":"Label","label":"M","args":[{"kind":"Opaque","name":"d"}]}]},"hyps":[],"output":"?a!:!2!<<!>>!@!(?a, ?c)!L!M(?d)"},
{"mode":"expression","input":{"kind":"Bang","expression":{"kind":"Opaque","name":"a"},"selectors":[]},"hyps":[],"output":"?a"},
{"mode":"expression","input":{"kind":"Apply","operator":{"kind":"Bang","expression":{"kind":"Opaque","name":"a"},"selectors":[{"kind":"Down"}]},"args":[{"kind":"Opaque","name":"c"}]},"hyps":[],"output":"?a!:(?c)"},
{"mode":"expression","input":{"kind":"Apply","operator":{"kind":"Bang","expression":{"kind":"Opaque","name":"a"},"selectors":[{"kind":"Down"}]},"args":[]},"hyps":[],"output":"?a!:"},
{"mode":"expression","input":{"kind":"Apply","operator":{"kind":"Lambda","params":[{"name":"x","shape":0},{"name":"F","shape":2}],"body":{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Ix","index":2}]}},"args":[{"kind":"Opaque","name":"a"},{"kind":"Opaque","name":"c"}]},"hyps":[],"output":"(LAMBDA x, F(_, _) : F(x)) (?a, ?c)"},
{"mode":"expression","input":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Apply","operator":{"kind":"Lambda","params":[{"name":"x","shape":0}],"body":{"kind":"Ix","index":1}},"args":[{"kind":"Opaque","name":"a"}]},{"kind":"Opaque","name":"c"}]},"hyps":[],"output":"(LAMBDA x : x) (?a) + ?c"},
{"mode":"expression","input":{"kind":"Ix","index":0},"hyps":[],"output":"#$0"},
{"mode":"expression","input":{"kind":"Ix","index":-3},"hyps":[],"output":"#$$3"},
{"mode":"expression","input":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":-1},{"kind":"Ix","index":1}]},"hyps":[{"kind":"Fresh","name":"p","shape":0,"level":"Constant","domainVisibility":"Visible"}],"output":"#$$1 + p"},
{"mode":"expression","input":{"kind":"Ix","index":1},"hyps":[],"output":"#$1"},
{"mode":"expression","input":{"kind":"Ix","index":7},"hyps":[{"kind":"Fresh","name":"p","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"Opaque","name":"a"},"visibility":"Visible","time":"Now"},{"kind":"Defn","definition":{"kind":"Operator","name":"Def","body":{"kind":"Opaque","name":"a"}},"whereDefined":"User","visibility":"Visible","isLocal":false}],"output":"#$7"},
{"mode":"expression","input":{"kind":"Ix","index":2},"hyps":[{"kind":"Fresh","name":"p","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"Opaque","name":"a"},"visibility":"Visible","time":"Now"},{"kind":"Defn","definition":{"kind":"Operator","name":"Def","body":{"kind":"Opaque","name":"a"}},"whereDefined":"User","visibility":"Visible","isLocal":false}],"output":"??? FACT ???"},
{"mode":"expression","input":{"kind":"Ix","index":3},"hyps":[{"kind":"Fresh","name":"p","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"Opaque","name":"a"},"visibility":"Visible","time":"Now"},{"kind":"Defn","definition":{"kind":"Operator","name":"Def","body":{"kind":"Opaque","name":"a"}},"whereDefined":"User","visibility":"Visible","isLocal":false}],"output":"p"},
{"mode":"expression","input":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":3}]},"hyps":[{"kind":"Fresh","name":"+","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fresh","name":"x","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fresh","name":"~","shape":0,"level":"Constant","domainVisibility":"Visible"}],"output":"~ + +"},
{"mode":"expression","input":{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Opaque","name":"a"}]},"hyps":[{"kind":"Fresh","name":"~","shape":0,"level":"Constant","domainVisibility":"Visible"}],"output":"~?a"},
{"mode":"expression","input":{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Opaque","name":"a"},{"kind":"Opaque","name":"c"}]},"hyps":[{"kind":"Fresh","name":"\\cup","shape":0,"level":"Constant","domainVisibility":"Visible"}],"output":"?a \\cup ?c"},
{"mode":"expression","input":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"x","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Ix","index":1}}},{"name":"x","level":"Constant","domain":{"kind":"Ditto"}},{"name":"y","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Ix","index":3}]}},"hyps":[{"kind":"Fresh","name":"x","shape":0,"level":"Constant","domainVisibility":"Visible"}],"output":"\\A x, x_1 \\in x, y : x_1 = x"},
{"mode":"expression","input":{"kind":"Quant","quantifier":"Exists","bounds":[{"name":"x","level":"Constant","domain":{"kind":"Ditto"}}],"body":{"kind":"Ix","index":1}},"hyps":[],"output":"\\E x \\in ?????? : x"},
{"mode":"expression","input":{"kind":"Let","definitions":[{"kind":"Operator","name":"F","body":{"kind":"Lambda","params":[{"name":"x","shape":0}],"body":{"kind":"Ix","index":1}}},{"kind":"Operator","name":"F","body":{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Opaque","name":"a"}]}},{"kind":"Recursive","name":"R","shape":2},{"kind":"Instance","name":"I","instance":{"args":["p","q"],"module":"M","substitutions":[{"name":"v","expression":{"kind":"Ix","index":1}}]}},{"kind":"Instance","name":"J","instance":{"args":[],"module":"N","substitutions":[]}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":4}]}},"hyps":[],"output":"LET F(x) == x\n    F_1 == F(?a)\n    NEW CONSTANT R(_, _)\n    I (p, q) == INSTANCE M WITH v <- q\n    J == INSTANCE N\nIN  J + F_1"},
{"mode":"expression","input":{"kind":"Choose","name":"x","domain":{"kind":"Ix","index":1},"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}},"hyps":[{"kind":"Fresh","name":"x","shape":0,"level":"Constant","domainVisibility":"Visible"}],"output":"CHOOSE x \\in x : x \\in x"},
{"mode":"expression","input":{"kind":"Choose","name":"x","body":{"kind":"Ix","index":1}},"hyps":[],"output":"CHOOSE x : x"},
{"mode":"expression","input":{"kind":"SetSt","name":"x_1","domain":{"kind":"Opaque","name":"a"},"body":{"kind":"SetSt","name":"x","domain":{"kind":"Ix","index":1},"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}}},"hyps":[{"kind":"Fresh","name":"x","shape":0,"level":"Constant","domainVisibility":"Visible"}],"output":"{x_1 \\in ?a : {x \\in x_1 : x = x_1}}"},
{"mode":"expression","input":{"kind":"SetOf","element":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]},"bounds":[{"name":"x","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Opaque","name":"a"}}},{"name":"y","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Opaque","name":"c"}}}]},"hyps":[],"output":"{y + x : x \\in ?a, y \\in ?c}"},
{"mode":"expression","input":{"kind":"Fcn","bounds":[{"name":"x","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Opaque","name":"a"}}}],"body":{"kind":"Ix","index":1}},"hyps":[],"output":"[x \\in ?a |-> x]"},
{"mode":"expression","input":{"kind":"Arrow","domain":{"kind":"Opaque","name":"a"},"range":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Opaque","name":"a"},{"kind":"Opaque","name":"c"}]}},"hyps":[],"output":"[?a -> ?a + ?c]"},
{"mode":"expression","input":{"kind":"Rect","fields":[{"name":"a","value":{"kind":"Opaque","name":"a"}},{"name":"b","value":{"kind":"Opaque","name":"c"}}]},"hyps":[],"output":"[a : ?a, b : ?c]"},
{"mode":"expression","input":{"kind":"Record","fields":[{"name":"a","value":{"kind":"Opaque","name":"a"}},{"name":"λ","value":{"kind":"Opaque","name":"c"}}]},"hyps":[],"output":"[a |-> ?a, λ |-> ?c]"},
{"mode":"expression","input":{"kind":"Except","function":{"kind":"Opaque","name":"a"},"specs":[{"trail":[{"kind":"Dot","field":"f"},{"kind":"Apply","expression":{"kind":"Opaque","name":"c"}}],"value":{"kind":"At","isExcept":true}},{"trail":[{"kind":"Apply","expression":{"kind":"Opaque","name":"d"}}],"value":{"kind":"Opaque","name":"a"}}]},"hyps":[],"output":"[?a EXCEPT !.f[?c] = @,\n           ![?d] = ?a]"},
{"mode":"expression","input":{"kind":"Sub","modal":"Box","action":{"kind":"Opaque","name":"a"},"subscript":{"kind":"Opaque","name":"c"}},"hyps":[],"output":"[?a]_?c"},
{"mode":"expression","input":{"kind":"Sub","modal":"Dia","action":{"kind":"Opaque","name":"a"},"subscript":{"kind":"Opaque","name":"c"}},"hyps":[],"output":"<<?a>>_?c"},
{"mode":"expression","input":{"kind":"Tsub","modal":"Box","action":{"kind":"Opaque","name":"a"},"subscript":{"kind":"Opaque","name":"c"}},"hyps":[],"output":"[][?a]_?c"},
{"mode":"expression","input":{"kind":"Tsub","modal":"Dia","action":{"kind":"Opaque","name":"a"},"subscript":{"kind":"Opaque","name":"c"}},"hyps":[],"output":"<><<?a>>_?c"},
{"mode":"expression","input":{"kind":"Fair","fairness":"Weak","subscript":{"kind":"Opaque","name":"a"},"action":{"kind":"Opaque","name":"c"}},"hyps":[],"output":"WF_(?a) (?c)"},
{"mode":"expression","input":{"kind":"Fair","fairness":"Strong","subscript":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Opaque","name":"a"},{"kind":"Opaque","name":"c"}]},"action":{"kind":"Opaque","name":"c"}},"hyps":[],"output":"SF_(?a + ?c) (?c)"},
{"mode":"expression","input":{"kind":"Case","arms":[{"condition":{"kind":"Opaque","name":"a"},"body":{"kind":"Opaque","name":"c"}},{"condition":{"kind":"Opaque","name":"c"},"body":{"kind":"Opaque","name":"d"}}],"other":{"kind":"Opaque","name":"a"}},"hyps":[],"output":"CASE ?a -> ?c\n  [] ?c -> ?d\n  [] OTHER -> ?a"},
{"mode":"expression","input":{"kind":"Case","arms":[{"condition":{"kind":"Opaque","name":"a"},"body":{"kind":"Opaque","name":"c"}}]},"hyps":[],"output":"CASE ?a -> ?c"},
{"mode":"expression","input":{"kind":"If","condition":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Opaque","name":"AVeryLongIdentifierNumber1ThatTakesSpace"},{"kind":"Opaque","name":"AVeryLongIdentifierNumber2ThatTakesSpace"}]},{"kind":"Opaque","name":"AVeryLongIdentifierNumber3ThatTakesSpace"}]},"consequent":{"kind":"Opaque","name":"AVeryLongIdentifierNumber4ThatTakesSpace"},"alternative":{"kind":"Opaque","name":"AVeryLongIdentifierNumber5ThatTakesSpace"}},"hyps":[],"output":"IF\n  ?AVeryLongIdentifierNumber1ThatTakesSpace\n  /\\ ?AVeryLongIdentifierNumber2ThatTakesSpace\n  /\\ ?AVeryLongIdentifierNumber3ThatTakesSpace\n  THEN ?AVeryLongIdentifierNumber4ThatTakesSpace\n  ELSE ?AVeryLongIdentifierNumber5ThatTakesSpace"},
{"mode":"expression","input":{"kind":"Tquant","quantifier":"Forall","names":["x","x"],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}},"hyps":[],"output":"\\AA x, x_1 : x_1 = x"},
{"mode":"expression","input":{"kind":"Tquant","quantifier":"Exists","names":["v"],"body":{"kind":"Ix","index":1}},"hyps":[],"output":"\\EE v : v"},
{"mode":"expression","input":{"kind":"Parens","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Opaque","name":"a"},{"kind":"Opaque","name":"c"}]},"form":{"kind":"Syntax"}},"hyps":[],"output":"?a + ?c"},
{"mode":"expression","input":{"kind":"Parens","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Opaque","name":"a"},{"kind":"Opaque","name":"c"}]},"form":{"kind":"Nlabel","label":"P","names":[]}},"hyps":[],"output":"P::(?a + ?c)"},
{"mode":"expression","input":{"kind":"Parens","expression":{"kind":"Opaque","name":"a"},"form":{"kind":"Nlabel","label":"P","names":[]}},"hyps":[],"output":"P::?a"},
{"mode":"expression","input":{"kind":"Parens","expression":{"kind":"Opaque","name":"a"},"form":{"kind":"Nlabel","label":"P","names":["x","y"]}},"hyps":[],"output":"P(x,\ny)::?a"},
{"mode":"expression","input":{"kind":"Parens","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Opaque","name":"a"},{"kind":"Opaque","name":"c"}]},"form":{"kind":"Nlabel","label":"P","names":["x"]}},"hyps":[],"output":"(P(x):: ?a + ?c)"},
{"mode":"expression","input":{"kind":"Parens","expression":{"kind":"If","condition":{"kind":"Opaque","name":"a"},"consequent":{"kind":"Opaque","name":"c"},"alternative":{"kind":"Opaque","name":"d"}},"form":{"kind":"Nlabel","label":"P","names":["x"]}},"hyps":[],"output":"P(x)::(IF ?a THEN ?c ELSE ?d)"},
{"mode":"expression","input":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"x","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Parens","expression":{"kind":"Ix","index":1},"form":{"kind":"Xlabel","label":"P","indices":[{"name":"x","index":1},{"name":"q","index":2},{"name":"z","index":0}]}}},"hyps":[],"output":"\\A x : P(x, ¶2, ¶0)::x"},
{"mode":"expression","input":{"kind":"With","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Opaque","name":"a"},{"kind":"Opaque","name":"c"}]},"method":{"name":"zenon"}},"hyps":[],"output":"?a + ?c"},
{"mode":"expression","input":{"kind":"Lambda","params":[{"name":"x","shape":0},{"name":"G","shape":3}],"body":{"kind":"Ix","index":2}},"hyps":[],"output":"LAMBDA x, G(_, _, _) : x"},
{"mode":"expression","input":{"kind":"Sequent","sequent":{"context":[{"kind":"Fresh","name":"x","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Ix","index":1}}},"hyps":[],"output":"ASSUME NEW CONSTANT x\nPROVE  x"},
{"mode":"expression","input":{"kind":"Sequent","sequent":{"context":[],"active":{"kind":"Opaque","name":"a"}}},"hyps":[],"output":"?a"},
{"mode":"obligation","input":{"context":[],"active":{"kind":"Opaque","name":"a"}},"output":"?a"},
{"mode":"obligation","input":{"context":[{"kind":"Fresh","name":"x","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fresh","name":"x","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fresh","name":"x_1","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Flex","name":"v"},{"kind":"Fresh","name":"S","shape":2,"level":"State","domainVisibility":"Visible"},{"kind":"Fresh","name":"y","shape":0,"level":"Constant","domain":{"kind":"Ix","index":3},"domainVisibility":"Visible"},{"kind":"Fresh","name":"z","shape":0,"level":"Constant","domain":{"kind":"Opaque","name":"a"},"domainVisibility":"Hidden"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":1},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":5},{"kind":"Ix","index":6}]}]}},"output":"ASSUME NEW CONSTANT x,\n       NEW CONSTANT x_1,\n       NEW CONSTANT x_1_1,\n       NEW VARIABLE v,\n       NEW STATE S(_, _),\n       NEW CONSTANT y \\in x_1_1,\n       NEW CONSTANT z\nPROVE  z /\\ x_1_1 = x_1"},
{"mode":"obligation","input":{"context":[{"kind":"Fresh","name":"x","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":1},{"kind":"Opaque","name":"a"}]},"visibility":"Visible","time":"Now"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Opaque","name":"c"}]},"visibility":"Hidden","time":"Now"},{"kind":"Fact","expression":{"kind":"With","expression":{"kind":"Opaque","name":"a"},"method":{"name":"smt"}},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":4},{"kind":"Opaque","name":"a"}]}},"output":"ASSUME NEW CONSTANT x,\n       x \\in ?a \nPROVE  x \\in ?a"},
{"mode":"obligation","input":{"context":[{"kind":"Defn","definition":{"kind":"Operator","name":"Op","body":{"kind":"Opaque","name":"a"}},"whereDefined":"User","visibility":"Visible","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"Hidden","body":{"kind":"Opaque","name":"a"}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"Bi","body":{"kind":"Opaque","name":"a"}},"whereDefined":"Builtin","visibility":"Visible","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"Pf","body":{"kind":"Opaque","name":"c"}},"whereDefined":{"kind":"Proof","time":"Now"},"visibility":"Visible","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"W","body":{"kind":"Lambda","params":[{"name":"x","shape":0}],"body":{"kind":"With","expression":{"kind":"Opaque","name":"a"},"method":{"name":"smt"}}}},"whereDefined":"User","visibility":"Visible","isLocal":false}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":1},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":2},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":3},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":4},{"kind":"Ix","index":5}]}]}]}]}},"output":"ASSUME Op == ?a\nPROVE  W + (Pf + (Bi + (Hidden + Op)))"},
{"mode":"obligation","input":{"context":[{"kind":"Fresh","name":"x","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Opaque","name":"a"}]},"visibility":"Hidden","time":"Now"}],"active":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"x","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":3}]}}},"output":"ASSUME NEW CONSTANT x\nPROVE  \\A x_1 : x_1 = x"},
{"mode":"obligation","input":{"context":[{"kind":"Fresh","name":"Some","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Opaque","name":"AVeryLongIdentifierNumber1ThatTakesSpace"},{"kind":"Opaque","name":"AVeryLongIdentifierNumber2ThatTakesSpace"}]},{"kind":"Opaque","name":"AVeryLongIdentifierNumber3ThatTakesSpace"}]},{"kind":"Opaque","name":"AVeryLongIdentifierNumber4ThatTakesSpace"}]},{"kind":"Opaque","name":"AVeryLongIdentifierNumber5ThatTakesSpace"}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Sequent","sequent":{"context":[{"kind":"Fresh","name":"x","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":1},{"kind":"Opaque","name":"AVeryLongIdentifierNumber1ThatTakesSpace"}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Opaque","name":"AVeryLongIdentifierNumber1ThatTakesSpace"},{"kind":"Opaque","name":"AVeryLongIdentifierNumber2ThatTakesSpace"}]},{"kind":"Opaque","name":"AVeryLongIdentifierNumber3ThatTakesSpace"}]},{"kind":"Opaque","name":"AVeryLongIdentifierNumber4ThatTakesSpace"}]}}}},"output":"ASSUME NEW CONSTANT Some,\n       ?AVeryLongIdentifierNumber1ThatTakesSpace\n       /\\ ?AVeryLongIdentifierNumber2ThatTakesSpace\n       /\\ ?AVeryLongIdentifierNumber3ThatTakesSpace\n       /\\ ?AVeryLongIdentifierNumber4ThatTakesSpace\n       /\\ ?AVeryLongIdentifierNumber5ThatTakesSpace \nPROVE  ASSUME NEW CONSTANT x,\n              x \\in ?AVeryLongIdentifierNumber1ThatTakesSpace \n       PROVE  ?AVeryLongIdentifierNumber1ThatTakesSpace\n              \\/ ?AVeryLongIdentifierNumber2ThatTakesSpace\n              \\/ ?AVeryLongIdentifierNumber3ThatTakesSpace\n              \\/ ?AVeryLongIdentifierNumber4ThatTakesSpace"},
{"mode":"obligation","input":{"context":[{"kind":"Defn","definition":{"kind":"Instance","name":"I","instance":{"args":["a","a"],"module":"M","substitutions":[{"name":"v","expression":{"kind":"Ix","index":1}},{"name":"w","expression":{"kind":"Ix","index":2}}]}},"whereDefined":"User","visibility":"Visible","isLocal":false},{"kind":"Defn","definition":{"kind":"Recursive","name":"R","shape":1},"whereDefined":"User","visibility":"Visible","isLocal":false}],"active":{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Ix","index":2}]}},"output":"ASSUME I (a, a_1) == INSTANCE M WITH v <- a_1, w <- a,\n       NEW CONSTANT R(_)\nPROVE  R(I)"},
{"mode":"obligation","input":{"context":[{"kind":"Fact","expression":{"kind":"Opaque","name":"a"},"visibility":"Hidden","time":"Now"}],"active":{"kind":"Opaque","name":"c"}},"output":"?c"},
{"mode":"obligation","input":{"context":[{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Neg"},"args":[{"kind":"Opaque","name":"a"},{"kind":"Opaque","name":"c"}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Opaque","name":"c"}},"error":"TlaProofError: Arity mismatch for operator ~"},
{"mode":"obligation","input":{"context":[{"kind":"Fresh","name":"x","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Product","factors":[]}},"error":"TlaProofError: Expr.Fmt.fmt_expr: PRODUCT []"},
{"mode":"sequent","input":{"context":[{"kind":"Defn","definition":{"kind":"Recursive","name":"","shape":2},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Fresh","name":"λ","shape":2,"level":"Temporal","domain":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"x_1","level":"Constant","domain":{"kind":"NoDomain"}},{"name":"z","level":"Constant","domain":{"kind":"Ditto"}},{"name":"y_1","level":"Constant","domain":{"kind":"Ditto"}}],"body":{"kind":"Arrow","domain":{"kind":"Internal","builtin":"Range"},"range":{"kind":"Ix","index":-2}}},"domainVisibility":"Visible"},{"kind":"Defn","definition":{"kind":"Operator","name":"x_2","body":{"kind":"Apply","operator":{"kind":"Ix","index":5},"args":[{"kind":"SetSt","name":"Foo","domain":{"kind":"At","isExcept":false},"body":{"kind":"Num","integer":"956","fraction":"25"}}]}},"whereDefined":"User","visibility":"Visible","isLocal":false}],"active":{"kind":"Apply","operator":{"kind":"Opaque","name":"="},"args":[{"kind":"Bang","expression":{"kind":"At","isExcept":false},"selectors":[]},{"kind":"Apply","operator":{"kind":"Opaque","name":"@@"},"args":[{"kind":"Internal","builtin":"Eq"},{"kind":"Internal","builtin":"Any"}]}]}},"output":"ASSUME NEW TEMPORAL λ(_, _) \\in \\A x_1, z, y_1 : [.. -> #$$2],\n       x_2 == #$5({Foo \\in @ : 956.25})\nPROVE  @ ?= = ?@@ Any"},
{"mode":"obligation","input":{"context":[{"kind":"Fresh","name":"λ","shape":2,"level":"Temporal","domain":{"kind":"List","bullet":"Or","items":[]},"domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"Rect","fields":[{"name":"a","value":{"kind":"Choose","name":"λ","domain":{"kind":"Num","integer":"100","fraction":"5"},"body":{"kind":"Num","integer":"254","fraction":"25"}}},{"name":"a","value":{"kind":"Bang","expression":{"kind":"Opaque","name":"AnotherQuiteLongName"},"selectors":[{"kind":"Instance","args":[{"kind":"Num","integer":"655","fraction":""}]}]}}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Opaque","name":"^+"},"args":[{"kind":"Parens","expression":{"kind":"Opaque","name":"Foo"},"form":{"kind":"Xlabel","label":"R","indices":[{"name":"n","index":4}]}}]}},"output":"ASSUME NEW TEMPORAL λ(_, _) \\in ,\n       [a : CHOOSE λ_1 \\in 100.5 : 254.25, a : ?AnotherQuiteLongName!(655)] \nPROVE  R(¶4)::?Foo?^+"},
{"mode":"obligation","input":{"context":[],"active":{"kind":"Sequent","sequent":{"context":[{"kind":"Fresh","name":"λ","shape":1,"level":"State","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"With","expression":{"kind":"At","isExcept":false},"method":{"name":"smt"}},"visibility":"Visible","time":"Now"},{"kind":"Flex","name":"λ"}],"active":{"kind":"Apply","operator":{"kind":"Ix","index":3},"args":[{"kind":"Opaque","name":"*"}]}}}},"output":"ASSUME NEW STATE λ(_),\n       NEW VARIABLE λ_1\nPROVE  λ(?*)"},
{"mode":"expression","input":{"kind":"Bang","expression":{"kind":"Quant","quantifier":"Exists","bounds":[{"name":"y_1","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Opaque","name":"[]"}}},{"name":"x","level":"Constant","domain":{"kind":"Ditto"}}],"body":{"kind":"Ix","index":-1}},"selectors":[{"kind":"Left"},{"kind":"Down"}]},"hyps":[{"kind":"Defn","definition":{"kind":"Operator","name":"a","body":{"kind":"Lambda","params":[{"name":"x","shape":0}],"body":{"kind":"Tquant","quantifier":"Forall","names":["z","z"],"body":{"kind":"Internal","builtin":"Times"}}}},"whereDefined":"User","visibility":"Visible","isLocal":false}],"output":"\\E y_1, x \\in ?[] : #$$1!<<!:"},
{"mode":"sequent","input":{"context":[{"kind":"Defn","definition":{"kind":"Operator","name":"y","body":{"kind":"Tsub","modal":"Dia","action":{"kind":"Apply","operator":{"kind":"Ix","index":3},"args":[{"kind":"Ix","index":1}]},"subscript":{"kind":"String","value":"he said \"hi\""}}},"whereDefined":"User","visibility":"Visible","isLocal":false},{"kind":"Fresh","name":"λ","shape":2,"level":"Action","domain":{"kind":"Quant","quantifier":"Exists","bounds":[{"name":"λ","level":"Constant","domain":{"kind":"Ditto"}}],"body":{"kind":"Tsub","modal":"Dia","action":{"kind":"Num","integer":"80","fraction":""},"subscript":{"kind":"String","value":"back\\slash"}}},"domainVisibility":"Visible"}],"active":{"kind":"SetSt","name":"","domain":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"x_2","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Internal","builtin":"JavaTime"}}},{"name":"Foo","level":"Constant","domain":{"kind":"Ditto"}}],"body":{"kind":"Opaque","name":"ThirdLongIdentifier"}},"body":{"kind":"Apply","operator":{"kind":"Ix","index":5},"args":[{"kind":"String","value":"a"},{"kind":"Num","integer":"573","fraction":"25"}]}}},"output":"ASSUME y == <><<#$3(#$1)>>_\"he said \"hi\"\",\n       NEW ACTION λ(_, _) \\in \\E λ \\in ?????? : <><<80>>_\"back\\slash\"\nPROVE  { \\in \\A x_2, Foo \\in JavaTime : ?ThirdLongIdentifier :\n          #$5(\"a\", 573.25)}"},
{"mode":"obligation","input":{"context":[{"kind":"Defn","definition":{"kind":"Operator","name":"y_1","body":{"kind":"Lambda","params":[{"name":"y_1","shape":0}],"body":{"kind":"Lambda","params":[{"name":"y_1","shape":1}],"body":{"kind":"Sequent","sequent":{"context":[],"active":{"kind":"Num","integer":"290","fraction":"25"}}}}}},"whereDefined":"User","visibility":"Visible","isLocal":false},{"kind":"Defn","definition":{"kind":"Instance","name":"x","instance":{"args":["a","+"],"module":"Naturals","substitutions":[{"name":"Foo","expression":{"kind":"Tquant","quantifier":"Forall","names":["x"],"body":{"kind":"With","expression":{"kind":"At","isExcept":false},"method":{"name":"smt"}}}}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false}],"active":{"kind":"Tuple","elements":[]}},"output":"ASSUME y_1(y_1) == LAMBDA y_1(_) : 290.25\nPROVE  <<>>"},
{"mode":"expression","input":{"kind":"SetEnum","elements":[{"kind":"Let","definitions":[{"kind":"Operator","name":"+","body":{"kind":"Internal","builtin":"Gt"}}],"body":{"kind":"Internal","builtin":"ENABLED"}},{"kind":"Bang","expression":{"kind":"Internal","builtin":"TLCGet"},"selectors":[{"kind":"Right"},{"kind":"At"}]}]},"output":"{LET + == >\n IN  ENABLED, TLCGet!>>!@}"},
{"mode":"expression","input":{"kind":"List","bullet":"Or","items":[]},"output":""},
{"mode":"sequent","input":{"context":[],"active":{"kind":"Apply","operator":{"kind":"Bang","expression":{"kind":"List","bullet":"Or","items":[{"kind":"Opaque","name":"\\lnot"},{"kind":"Num","integer":"268","fraction":"25"},{"kind":"Internal","builtin":"Conj"},{"kind":"Opaque","name":"AnotherQuiteLongName"}]},"selectors":[{"kind":"Instance","args":[{"kind":"Choose","name":"a","domain":{"kind":"Internal","builtin":"SubSeq"},"body":{"kind":"Opaque","name":"ThirdLongIdentifier"}},{"kind":"Apply","operator":{"kind":"Lambda","params":[{"name":"λ","shape":2}],"body":{"kind":"String","value":"back\\slash"}},"args":[{"kind":"String","value":"😀 emoji"}]}]}]},"args":[]}},"output":"\\/ ?~\n\\/ 268.25\n\\/ /\\\n\\/ ?AnotherQuiteLongName!(CHOOSE a \\in SubSeq : ?ThirdLongIdentifier,\n                          (LAMBDA λ(_, _) : \"back\\slash\") (\"😀 emoji\"))"},
{"mode":"obligation","input":{"context":[{"kind":"Fresh","name":"+","shape":2,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"With","expression":{"kind":"Apply","operator":{"kind":"Opaque","name":"UNION"},"args":[{"kind":"At","isExcept":false}]},"method":{"name":"smt"}},"visibility":"Visible","time":"Now"}],"active":{"kind":"Sequent","sequent":{"context":[{"kind":"Fact","expression":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"x","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Opaque","name":"SomeVeryLongIdentifierName"}}}],"body":{"kind":"Internal","builtin":"BoxFalse"}},"visibility":"Hidden","time":"Now"},{"kind":"Flex","name":"y_1"},{"kind":"Fresh","name":"x","shape":0,"level":"Action","domain":{"kind":"Quant","quantifier":"Exists","bounds":[{"name":"y_1","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Opaque","name":"ThirdLongIdentifier"}}},{"name":"","level":"Constant","domain":{"kind":"Ditto"}},{"name":"y","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Opaque","name":"UNCHANGED"}}}],"body":{"kind":"At","isExcept":false}},"domainVisibility":"Hidden"}],"active":{"kind":"Bang","expression":{"kind":"Num","integer":"418","fraction":"5"},"selectors":[{"kind":"At"},{"kind":"Right"}]}}}},"output":"ASSUME NEW CONSTANT +(_, _)\nPROVE  ASSUME NEW VARIABLE y_1,\n              NEW ACTION x\n       PROVE  418.5!@!>>"},
{"mode":"expression","input":{"kind":"List","bullet":"Refs","items":[{"kind":"Apply","operator":{"kind":"Lambda","params":[{"name":"λ","shape":1},{"name":"x","shape":0}],"body":{"kind":"String","value":"%s@[<h>"}},"args":[]},{"kind":"If","condition":{"kind":"At","isExcept":false},"consequent":{"kind":"At","isExcept":false},"alternative":{"kind":"String","value":"%s@[<h>"}}]},"hyps":[{"kind":"Defn","definition":{"kind":"Operator","name":"a","body":{"kind":"Case","arms":[{"condition":{"kind":"Opaque","name":"^"},"body":{"kind":"At","isExcept":false}},{"condition":{"kind":"String","value":"naïve λ → ∀"},"body":{"kind":"Num","integer":"398","fraction":"5"}}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Flex","name":""}],"output":"/\\ (LAMBDA λ(_), x : \"%s@[<h>\") ()\n/\\ IF @ THEN @ ELSE \"%s@[<h>\""},
{"mode":"expression","input":{"kind":"Apply","operator":{"kind":"Opaque","name":"@@"},"args":[{"kind":"Apply","operator":{"kind":"Opaque","name":"-."},"args":[{"kind":"Ix","index":1}]},{"kind":"Lambda","params":[{"name":"z","shape":1},{"name":"x_1","shape":1}],"body":{"kind":"At","isExcept":false}}]},"hyps":[{"kind":"Defn","definition":{"kind":"Bpragma","name":"x_2","body":{"kind":"Lambda","params":[{"name":"x_2","shape":0},{"name":"Foo","shape":0},{"name":"x","shape":1}],"body":{"kind":"Quant","quantifier":"Exists","bounds":[{"name":"x","level":"Constant","domain":{"kind":"NoDomain"}},{"name":"x","level":"Constant","domain":{"kind":"Ditto"}}],"body":{"kind":"String","value":"he said \"hi\""}}},"methods":[]},"whereDefined":"Builtin","visibility":"Visible","isLocal":false},{"kind":"Flex","name":"z"}],"output":"?-.z ?@@ (LAMBDA z(_), x_1(_) : @)"},
{"mode":"sequent","input":{"context":[],"active":{"kind":"Dot","expression":{"kind":"Apply","operator":{"kind":"Ix","index":3},"args":[{"kind":"At","isExcept":false}]},"field":"a"}},"output":"#$3(@).a"},
{"mode":"obligation","input":{"context":[{"kind":"Fact","expression":{"kind":"With","expression":{"kind":"Case","arms":[{"condition":{"kind":"Arrow","domain":{"kind":"Opaque","name":"AnotherQuiteLongName"},"range":{"kind":"String","value":"he said \"hi\""}},"body":{"kind":"Quant","quantifier":"Exists","bounds":[{"name":"y","level":"Constant","domain":{"kind":"Ditto"}},{"name":"x","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Opaque","name":"y"}}}],"body":{"kind":"Ix","index":2}}}]},"method":{"name":"zenon"}},"visibility":"Hidden","time":"Now"}],"active":{"kind":"Fair","fairness":"Strong","subscript":{"kind":"Apply","operator":{"kind":"Internal","builtin":"SubSeq"},"args":[{"kind":"Opaque","name":"ThirdLongIdentifier"},{"kind":"Internal","builtin":"Diamond"},{"kind":"String","value":"back\\slash"}]},"action":{"kind":"Bang","expression":{"kind":"Ix","index":0},"selectors":[]}}},"output":"SF_(SubSeq(?ThirdLongIdentifier, <>, \"back\\slash\")) (#$0)"},
{"mode":"obligation","input":{"context":[{"kind":"Defn","definition":{"kind":"Operator","name":"λ","body":{"kind":"If","condition":{"kind":"Arrow","domain":{"kind":"Opaque","name":"^+"},"range":{"kind":"At","isExcept":false}},"consequent":{"kind":"Parens","expression":{"kind":"Num","integer":"670","fraction":""},"form":{"kind":"Syntax"}},"alternative":{"kind":"Fair","fairness":"Strong","subscript":{"kind":"String","value":"line\nbreak"},"action":{"kind":"String","value":"he said \"hi\""}}}},"whereDefined":"User","visibility":"Visible","isLocal":false},{"kind":"Defn","definition":{"kind":"Recursive","name":"λ","shape":0},"whereDefined":"User","visibility":"Hidden","isLocal":false}],"active":{"kind":"Apply","operator":{"kind":"Ix","index":3},"args":[{"kind":"Parens","expression":{"kind":"Internal","builtin":"Neg"},"form":{"kind":"Syntax"}}]}},"output":"ASSUME λ == IF [?^+ -> @] THEN 670 ELSE SF_(\"line\nbreak\") (\"he said \"hi\"\")\nPROVE  #$3(~)"},
{"mode":"obligation","input":{"context":[],"active":{"kind":"SetEnum","elements":[{"kind":"Parens","expression":{"kind":"Internal","builtin":"Len"},"form":{"kind":"Syntax"}},{"kind":"Parens","expression":{"kind":"At","isExcept":false},"form":{"kind":"Nlabel","label":"Q","names":["x","y"]}},{"kind":"FcnApp","function":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"String","value":"a"},{"kind":"At","isExcept":false}]}]}},"output":"{Len, Q(x, y)::@, \\/[\"a\", @]}"},
{"mode":"obligation","input":{"context":[],"active":{"kind":"Apply","operator":{"kind":"Ix","index":4},"args":[{"kind":"If","condition":{"kind":"String","value":"tab\there"},"consequent":{"kind":"At","isExcept":false},"alternative":{"kind":"Internal","builtin":"FALSE"}}]}},"output":"#$4(IF \"tab\there\" THEN @ ELSE FALSE)"},
{"mode":"obligation","input":{"context":[{"kind":"Fact","expression":{"kind":"Case","arms":[{"condition":{"kind":"Apply","operator":{"kind":"Opaque","name":"^#"},"args":[{"kind":"Ix","index":0}]},"body":{"kind":"FcnApp","function":{"kind":"Internal","builtin":"DOMAIN"},"args":[{"kind":"At","isExcept":false}]}},{"condition":{"kind":"Sequent","sequent":{"context":[{"kind":"Fact","expression":{"kind":"Num","integer":"786","fraction":""},"visibility":"Visible","time":"Now"}],"active":{"kind":"Num","integer":"882","fraction":"5"}}},"body":{"kind":"Fcn","bounds":[{"name":"","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Internal","builtin":"Cup"}}}]},"visibility":"Visible","time":"Now"},{"kind":"Fact","expression":{"kind":"SetSt","name":"y_1","domain":{"kind":"Case","arms":[{"condition":{"kind":"Internal","builtin":"TLCSet"},"body":{"kind":"Internal","builtin":"Uminus"}},{"condition":{"kind":"Ix","index":2},"body":{"kind":"Opaque","name":"AnotherQuiteLongName"}}],"other":{"kind":"Opaque","name":"SomeVeryLongIdentifierName"}},"body":{"kind":"Choose","name":"a","body":{"kind":"Num","integer":"728","fraction":"5"}}},"visibility":"Hidden","time":"Now"},{"kind":"Flex","name":"y_1"}],"active":{"kind":"Fcn","bounds":[{"name":"Foo","level":"Constant","domain":{"kind":"Ditto"}}],"body":{"kind":"With","expression":{"kind":"Ix","index":-2},"method":{"name":"smt"}}}},"output":"ASSUME CASE #$0?^# -> DOMAIN[@]\n         [] ASSUME 786 \n            PROVE  882.5 -> [ |-> \\cup] ,\n       NEW VARIABLE y_1\nPROVE  [Foo \\in ?????? |-> #$$2]"},
{"mode":"obligation","input":{"context":[],"active":{"kind":"Bang","expression":{"kind":"Apply","operator":{"kind":"Ix","index":2},"args":[{"kind":"String","value":"back\\slash"},{"kind":"Ix","index":2}]},"selectors":[{"kind":"Down"},{"kind":"At"}]}},"output":"#$2(\"back\\slash\", #$2)!:!@"},
{"mode":"obligation","input":{"context":[{"kind":"Fresh","name":"x","shape":1,"level":"Constant","domain":{"kind":"Let","definitions":[{"kind":"Instance","name":"y_1","instance":{"args":["x"],"module":"M","substitutions":[{"name":"Foo","expression":{"kind":"Opaque","name":"AnotherQuiteLongName"}},{"name":"Foo","expression":{"kind":"Let","definitions":[{"kind":"Bpragma","name":"a","body":{"kind":"String","value":""},"methods":[]},{"kind":"Recursive","name":"y_1","shape":2}],"body":{"kind":"Opaque","name":"LongOperatorName"}}}]}}],"body":{"kind":"Tuple","elements":[{"kind":"Opaque","name":"="},{"kind":"String","value":"back\\slash"},{"kind":"Internal","builtin":"StrongPrime"}]}},"domainVisibility":"Hidden"}],"active":{"kind":"Sequent","sequent":{"context":[{"kind":"Defn","definition":{"kind":"Operator","name":"Foo","body":{"kind":"Lambda","params":[{"name":"x_2","shape":0}],"body":{"kind":"Let","definitions":[{"kind":"Operator","name":"+","body":{"kind":"At","isExcept":false}},{"kind":"Operator","name":"x","body":{"kind":"Internal","builtin":"Neg"}}],"body":{"kind":"Ix","index":4}}}},"whereDefined":"User","visibility":"Visible","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"λ","body":{"kind":"SetOf","element":{"kind":"Ix","index":3},"bounds":[{"name":"y","level":"Constant","domain":{"kind":"Ditto"}}]}},"whereDefined":"User","visibility":"Visible","isLocal":false},{"kind":"Fresh","name":"λ","shape":2,"level":"Temporal","domainVisibility":"Hidden"}],"active":{"kind":"Dot","expression":{"kind":"Internal","builtin":"OneArg"},"field":"a"}}}},"output":"ASSUME NEW CONSTANT x(_)\nPROVE  ASSUME Foo(x_2) == LET + == @\n                              x_1 == ~\n                          IN  x,\n              λ == {x : y \\in ??????},\n              NEW TEMPORAL λ_1(_, _)\n       PROVE  :>.a"},
{"mode":"sequent","input":{"context":[],"active":{"kind":"Choose","name":"y_1","body":{"kind":"SetSt","name":"Foo","domain":{"kind":"Opaque","name":"y"},"body":{"kind":"String","value":"he said \"hi\""}}}},"output":"CHOOSE y_1 : {Foo \\in ?y : \"he said \"hi\"\"}"},
{"mode":"obligation","input":{"context":[{"kind":"Fact","expression":{"kind":"Sequent","sequent":{"context":[{"kind":"Fact","expression":{"kind":"List","bullet":"And","items":[]},"visibility":"Hidden","time":"Now"},{"kind":"Defn","definition":{"kind":"Operator","name":"Foo","body":{"kind":"Lambda","params":[{"name":"Foo","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Lambda","params":[{"name":"y_1","shape":0}],"body":{"kind":"Opaque","name":"ThirdLongIdentifier"}},"args":[{"kind":"String","value":"naïve λ → ∀"}]}}},"whereDefined":{"kind":"Proof","time":"Now"},"visibility":"Visible","isLocal":false},{"kind":"Flex","name":"x"}],"active":{"kind":"Sub","modal":"Box","action":{"kind":"Opaque","name":"\\X"},"subscript":{"kind":"Opaque","name":"<="}}}},"visibility":"Visible","time":"Now"}],"active":{"kind":"Opaque","name":"SomeVeryLongIdentifierName"}},"output":"ASSUME ASSUME NEW VARIABLE x\n       PROVE  [?\\X]_?=< \nPROVE  ?SomeVeryLongIdentifierName"},
{"mode":"obligation","input":{"context":[{"kind":"Flex","name":""}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Equiv"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"String","value":"line\nbreak"}]},{"kind":"With","expression":{"kind":"Internal","builtin":"PrintT"},"method":{"name":"smt"}}]}},"output":"ASSUME NEW VARIABLE \nPROVE  (\"line\nbreak\") <=> PrintT"},
{"mode":"obligation","input":{"context":[{"kind":"Fresh","name":"","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Fcn","bounds":[{"name":"","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Tquant","quantifier":"Exists","names":["y_1","x_2"],"body":{"kind":"At","isExcept":false}}}},"output":"ASSUME NEW CONSTANT \nPROVE  [_1 |-> \\EE y_1, x_2 : @]"},
{"mode":"obligation","input":{"context":[],"active":{"kind":"Arrow","domain":{"kind":"Apply","operator":{"kind":"Bang","expression":{"kind":"Opaque","name":"/\\"},"selectors":[{"kind":"Label","label":"P","args":[]}]},"args":[]},"range":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"λ","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"String","value":"tab\there"}}},{"name":"y_1","level":"Constant","domain":{"kind":"NoDomain"}},{"name":"Foo","level":"Constant","domain":{"kind":"Ditto"}}],"body":{"kind":"String","value":"he said \"hi\""}}}},"output":"[?/\\!P -> \\A λ \\in \"tab\there\", y_1, Foo : \"he said \"hi\"\"]"},
{"mode":"sequent","input":{"context":[{"kind":"Fact","expression":{"kind":"Choose","name":"y_1","domain":{"kind":"List","bullet":"Refs","items":[{"kind":"Opaque","name":"y"},{"kind":"Ix","index":4},{"kind":"Opaque","name":"SomeVeryLongIdentifierName"}]},"body":{"kind":"List","bullet":"Refs","items":[{"kind":"String","value":"a"},{"kind":"Opaque","name":"ThirdLongIdentifier"},{"kind":"Num","integer":"960","fraction":""}]}},"visibility":"Visible","time":"Now"},{"kind":"Defn","definition":{"kind":"Operator","name":"a","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Len"},"args":[{"kind":"Fcn","bounds":[{"name":"","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Internal","builtin":"Ratio"}}]}},"whereDefined":"User","visibility":"Visible","isLocal":false}],"active":{"kind":"Arrow","domain":{"kind":"Case","arms":[{"condition":{"kind":"Internal","builtin":"PrintT"},"body":{"kind":"Opaque","name":"ThirdLongIdentifier"}}]},"range":{"kind":"Fair","fairness":"Strong","subscript":{"kind":"At","isExcept":false},"action":{"kind":"Internal","builtin":"Extend"}}}},"output":"ASSUME CHOOSE y_1 \\in /\\ ?y\n                      /\\ #$4\n                      /\\ ?SomeVeryLongIdentifierName :\n         /\\ \"a\"\n         /\\ ?ThirdLongIdentifier\n         /\\ 960 ,\n       a == Len([_1 |-> /])\nPROVE  [CASE PrintT -> ?ThirdLongIdentifier -> SF_(@) (@@)]"},
{"mode":"obligation","input":{"context":[{"kind":"Flex","name":"z"}],"active":{"kind":"Record","fields":[{"name":"bb","value":{"kind":"Dot","expression":{"kind":"At","isExcept":false},"field":"a"}}]}},"output":"ASSUME NEW VARIABLE z\nPROVE  [bb |-> @.a]"},
{"mode":"expression","input":{"kind":"Choose","name":"a","domain":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"λ","level":"Constant","domain":{"kind":"Ditto"}},{"name":"x","level":"Constant","domain":{"kind":"Ditto"}},{"name":"x_1","level":"Constant","domain":{"kind":"Ditto"}}],"body":{"kind":"Num","integer":"226","fraction":"5"}},"body":{"kind":"Arrow","domain":{"kind":"String","value":"naïve λ → ∀"},"range":{"kind":"String","value":"😀 emoji"}}},"output":"CHOOSE a \\in \\A λ, x, x_1 \\in ?????? : 226.5 :\n  [\"naïve λ → ∀\" -> \"😀 emoji\"]"},
{"mode":"obligation","input":{"context":[],"active":{"kind":"Tuple","elements":[{"kind":"Tquant","quantifier":"Exists","names":["+","a"],"body":{"kind":"Num","integer":"887","fraction":"25"}},{"kind":"SetSt","name":"x","domain":{"kind":"Opaque","name":"<="},"body":{"kind":"String","value":"a"}},{"kind":"Apply","operator":{"kind":"Opaque","name":"*"},"args":[{"kind":"Ix","index":2},{"kind":"String","value":"a"}]}]}},"output":"<<\\EE +, a : 887.25, {x \\in ?=< : \"a\"}, #$2 ?* \"a\">>"},
{"mode":"obligation","input":{"context":[{"kind":"Fact","expression":{"kind":"Sequent","sequent":{"context":[{"kind":"Flex","name":"λ"},{"kind":"Fact","expression":{"kind":"SetSt","name":"λ","domain":{"kind":"Num","integer":"441","fraction":"5"},"body":{"kind":"Opaque","name":"ENABLED"}},"visibility":"Hidden","time":"Now"},{"kind":"Fresh","name":"+","shape":1,"level":"Unknown","domainVisibility":"Visible"}],"active":{"kind":"Tquant","quantifier":"Exists","names":["x_2"],"body":{"kind":"Ix","index":-2}}}},"visibility":"Visible","time":"Now"},{"kind":"Fresh","name":"y_1","shape":2,"level":"Temporal","domainVisibility":"Visible"}],"active":{"kind":"Quant","quantifier":"Exists","bounds":[{"name":"λ","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Lambda","params":[{"name":"x","shape":0},{"name":"z","shape":0}],"body":{"kind":"Internal","builtin":"Subseteq"}}}},{"name":"z","level":"Constant","domain":{"kind":"Ditto"}},{"name":"x_2","level":"Constant","domain":{"kind":"Ditto"}}],"body":{"kind":"Num","integer":"887","fraction":"25"}}},"output":"ASSUME ASSUME NEW VARIABLE λ,\n              NEW UNKNOWN +(_)\n       PROVE  \\EE x_2 : #$$2 ,\n       NEW TEMPORAL y_1(_, _)\nPROVE  \\E λ, z, x_2 \\in LAMBDA x, z : \\subseteq : 887.25"},
{"mode":"obligation","input":{"context":[{"kind":"Fact","expression":{"kind":"Dot","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"TLCGet"},"args":[{"kind":"Num","integer":"632","fraction":""},{"kind":"Num","integer":"21","fraction":""}]},"field":"field"},"visibility":"Visible","time":"Now"},{"kind":"Flex","name":"x"}],"active":{"kind":"FcnApp","function":{"kind":"Apply","operator":{"kind":"Opaque","name":"\\in"},"args":[{"kind":"Opaque","name":"ThirdLongIdentifier"},{"kind":"At","isExcept":false}]},"args":[{"kind":"Tquant","quantifier":"Exists","names":["x_1"],"body":{"kind":"Opaque","name":"ThirdLongIdentifier"}}]}},"output":"ASSUME TLCGet(632, 21).field ,\n       NEW VARIABLE x\nPROVE  (?ThirdLongIdentifier ?\\in @)[\\EE x_1 : ?ThirdLongIdentifier]"},
{"mode":"obligation","input":{"context":[{"kind":"Flex","name":"a"}],"active":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"x","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Let","definitions":[{"kind":"Operator","name":"y_1","body":{"kind":"Lambda","params":[{"name":"a","shape":0}],"body":{"kind":"Ix","index":-2}}},{"kind":"Operator","name":"λ","body":{"kind":"Lambda","params":[{"name":"+","shape":1},{"name":"x_2","shape":2}],"body":{"kind":"Opaque","name":"AnotherQuiteLongName"}}}],"body":{"kind":"Opaque","name":"/\\"}}}}],"body":{"kind":"FcnApp","function":{"kind":"Opaque","name":"<>"},"args":[{"kind":"Internal","builtin":"Cup"}]}}},"output":"ASSUME NEW VARIABLE a\nPROVE  \\A x\n          \\in LET y_1(a) == #$$2\n                  λ(+(_), x_2(_, _)) == ?AnotherQuiteLongName\n              IN  ?/\\ :\n          ?<>[\\cup]"},
{"mode":"obligation","input":{"context":[{"kind":"Defn","definition":{"kind":"Recursive","name":"","shape":2},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Flex","name":""},{"kind":"Fresh","name":"x_1","shape":2,"level":"Temporal","domain":{"kind":"Quant","quantifier":"Exists","bounds":[{"name":"z","level":"Constant","domain":{"kind":"NoDomain"}},{"name":"+","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"a","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Internal","builtin":"TLCSet"}}},{"name":"λ","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Internal","builtin":"Lt"}}},{"name":"x_2","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Internal","builtin":"Mem"}}}],"body":{"kind":"Ix","index":-1}}}},{"name":"+","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Tquant","quantifier":"Exists","names":["x","y_1"],"body":{"kind":"String","value":""}}}}],"body":{"kind":"Bang","expression":{"kind":"At","isExcept":false},"selectors":[]}},"domainVisibility":"Visible"}],"active":{"kind":"Tquant","quantifier":"Forall","names":["y","x"],"body":{"kind":"Tuple","elements":[{"kind":"Opaque","name":".."},{"kind":"Internal","builtin":"Infinity"}]}}},"output":"ASSUME NEW VARIABLE _1,\n       NEW TEMPORAL x_1(_, _) \\in \\E z,\n                                     +\n                                     \\in \\A a \\in TLCSet, λ \\in <,\n                                            x_2 \\in \\in : #$$1,\n                                     +_1 \\in \\EE x, y_1 : \"\" : @\nPROVE  \\AA y, x : <<?.., Infinity>>"},
{"mode":"obligation","input":{"context":[{"kind":"Fact","expression":{"kind":"FcnApp","function":{"kind":"Dot","expression":{"kind":"Opaque","name":"\\/"},"field":"field"},"args":[{"kind":"Rect","fields":[{"name":"a","value":{"kind":"Internal","builtin":"Remainder"}}]}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Fcn","bounds":[{"name":"x","level":"Constant","domain":{"kind":"NoDomain"}},{"name":"y_1","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Let","definitions":[{"kind":"Instance","name":"","instance":{"args":[],"module":"M","substitutions":[{"name":"y_1","expression":{"kind":"Internal","builtin":"STRING"}},{"name":"a","expression":{"kind":"Opaque","name":"SomeVeryLongIdentifierName"}}]}}],"body":{"kind":"Ix","index":3}}}},{"name":"x","level":"Constant","domain":{"kind":"Ditto"}}],"body":{"kind":"Choose","name":"+","body":{"kind":"Ix","index":1}}}},"output":"ASSUME (?\\/.field)[[a : %]] \nPROVE  [x,\n          y_1, x_1\n          \\in LET _1 == INSTANCE M WITH y_1 <- STRING,\n                          a <- ?SomeVeryLongIdentifierName\n              IN  #$3 |->\n          CHOOSE + : +]"},
{"mode":"expression","input":{"kind":"Apply","operator":{"kind":"Opaque","name":"*"},"args":[{"kind":"Quant","quantifier":"Exists","bounds":[{"name":"z","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"At","isExcept":false}}}],"body":{"kind":"Opaque","name":"AnotherQuiteLongName"}},{"kind":"SetEnum","elements":[{"kind":"At","isExcept":false},{"kind":"Opaque","name":"@@"}]}]},"hyps":[{"kind":"Flex","name":"x_2"}],"output":"(\\E z \\in @ : ?AnotherQuiteLongName) ?* {@, ?@@}"},
{"mode":"obligation","input":{"context":[],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"BSeq"},"args":[{"kind":"Apply","operator":{"kind":"Opaque","name":"-"},"args":[{"kind":"String","value":"%s@[<h>"},{"kind":"At","isExcept":false}]},{"kind":"Quant","quantifier":"Exists","bounds":[{"name":"","level":"Constant","domain":{"kind":"NoDomain"}},{"name":"y","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Num","integer":"683","fraction":""}}}],"body":{"kind":"Num","integer":"401","fraction":"25"}}]}},"output":"BSeq(\"%s@[<h>\" ?- @, \\E , y \\in 683 : 401.25)"},
{"mode":"sequent","input":{"context":[{"kind":"Defn","definition":{"kind":"Recursive","name":"","shape":1},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Fact","expression":{"kind":"With","expression":{"kind":"Record","fields":[{"name":"λ","value":{"kind":"Let","definitions":[{"kind":"Operator","name":"a","body":{"kind":"Lambda","params":[{"name":"x_1","shape":2},{"name":"x","shape":2}],"body":{"kind":"Opaque","name":"SomeVeryLongIdentifierName"}}},{"kind":"Operator","name":"x","body":{"kind":"At","isExcept":false}}],"body":{"kind":"Num","integer":"997","fraction":""}}},{"name":"a","value":{"kind":"Product","factors":[{"kind":"Ix","index":5},{"kind":"Internal","builtin":"Ratio"},{"kind":"At","isExcept":false}]}}]},"method":{"name":"zenon"}},"visibility":"Hidden","time":"Now"}],"active":{"kind":"List","bullet":"And","items":[]}},"output":""},
{"mode":"obligation","input":{"context":[{"kind":"Flex","name":"λ"},{"kind":"Flex","name":"λ"}],"active":{"kind":"Record","fields":[{"name":"λ","value":{"kind":"Except","function":{"kind":"Opaque","name":"+"},"specs":[{"trail":[{"kind":"Apply","expression":{"kind":"Internal","builtin":"BSeq"}}],"value":{"kind":"Num","integer":"496","fraction":"5"}}]}}]}},"output":"ASSUME NEW VARIABLE λ,\n       NEW VARIABLE λ_1\nPROVE  [λ |-> [?+ EXCEPT ![BSeq] = 496.5]]"},
{"mode":"obligation","input":{"context":[{"kind":"Fresh","name":"x","shape":2,"level":"Constant","domainVisibility":"Hidden"}],"active":{"kind":"Arrow","domain":{"kind":"Apply","operator":{"kind":"Opaque","name":"\\cdot"},"args":[{"kind":"Num","integer":"628","fraction":""},{"kind":"At","isExcept":false}]},"range":{"kind":"Tuple","elements":[{"kind":"String","value":"back\\slash"}]}}},"output":"ASSUME NEW CONSTANT x(_, _)\nPROVE  [628 ?\\cdot @ -> <<\"back\\slash\">>]"},
{"mode":"obligation","input":{"context":[{"kind":"Fact","expression":{"kind":"Sub","modal":"Dia","action":{"kind":"Fcn","bounds":[{"name":"x_1","level":"Constant","domain":{"kind":"NoDomain"}},{"name":"","level":"Constant","domain":{"kind":"Ditto"}},{"name":"Foo","level":"Constant","domain":{"kind":"Ditto"}}],"body":{"kind":"Internal","builtin":"Neg"}},"subscript":{"kind":"If","condition":{"kind":"Ix","index":1},"consequent":{"kind":"Internal","builtin":"SelectSeq"},"alternative":{"kind":"Opaque","name":"AnotherQuiteLongName"}}},"visibility":"Hidden","time":"Now"},{"kind":"Flex","name":"x"}],"active":{"kind":"Arrow","domain":{"kind":"SetSt","name":"x","domain":{"kind":"Num","integer":"695","fraction":""},"body":{"kind":"Opaque","name":"\\in"}},"range":{"kind":"Sequent","sequent":{"context":[],"active":{"kind":"Ix","index":-1}}}}},"output":"ASSUME NEW VARIABLE x\nPROVE  [{x_1 \\in 695 : ?\\in} -> #$$1]"}
]"##;

    #[test]
    fn prints_as_the_typescript_does() {
        assert_eq!(check_cases(CASES), 0);
    }

    /// Expected names from `src/obligations/printer.ts` under Bun.
    #[test]
    fn names_binders_apart_as_the_typescript_does() {
        let mut context = create_context();
        let pushed: Vec<String> = ["x", "x", "x_1", "", "x_1_1", "x"]
            .iter()
            .map(|name| push_name(&mut context, name))
            .collect();
        assert_eq!(pushed, ["x", "x_1", "x_1_1", "", "x_1_1_1", "x_2"]);
        let bound: Vec<Option<String>> = [-1, 0, 1, 2, 3, 4, 5, 6, 7]
            .iter()
            .map(|&index| get_bound_name(&context, index))
            .collect();
        let expected = [
            None,
            None,
            Some("x_2"),
            Some("x_1_1_1"),
            Some(""),
            Some("x_1_1"),
            Some("x_1"),
            Some("x"),
            None,
        ];
        assert_eq!(bound, expected.map(|name| name.map(str::to_owned)));
        pop_names(&mut context, 3);
        assert_eq!(push_name(&mut context, "x"), "x_2");
        assert_eq!(push_name(&mut context, "x_1"), "x_1_2");
        assert_eq!(context.stack.len(), 5);
        pop_names(&mut context, 99);
        assert_eq!(context.stack.len(), 0);
        assert_eq!(push_name(&mut context, "x"), "x");
        assert_eq!(push_name(&mut context, "x_2"), "x_2");
        assert_eq!(push_name(&mut context, "x"), "x_1");
    }
}
