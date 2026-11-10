// Ported from tlapm's src/backend/isabelle.ml (BSD licensed, see LICENSE-tlapm).
//! An obligation as the Isabelle/TLA+ theory tlapm writes for Isabelle to prove with a tactic. A
//! port of `src/prover/isabelle/encode.ts`.

use crate::errors::{ObligationError, Result};
use crate::expression::{
    Bound, BoundDomain, Builtin, Bullet, DefnCore, ExceptPoint, Expr, ExprCore, Fairness, Hyp,
    HypCore, Modal, Quantifier, Sequent, Visibility,
};
use crate::first_order::{
    get_unprintable_error, pickle, print_fact, repeat_parsed, split_first_bound,
};
use crate::printer::{Context, create_context, get_bound_name, pop_names, push_name};

fn cook(name: &str) -> Result<String> {
    Ok(format!("is{}", pickle(name)?))
}

fn get_atom(builtin: Builtin) -> Result<Option<String>> {
    Ok(Some(match builtin {
        Builtin::TRUE => "TRUE".to_owned(),
        Builtin::FALSE => "FALSE".to_owned(),
        Builtin::STRING => "STRING".to_owned(),
        Builtin::BOOLEAN => "BOOLEAN".to_owned(),
        Builtin::Nat => "Nat".to_owned(),
        Builtin::Int => "Int".to_owned(),
        Builtin::Real => cook("Real")?,
        Builtin::Infinity => cook("Infinity")?,
        Builtin::Any => "Any".to_owned(),
        _ => return Ok(None),
    }))
}

fn get_unary(builtin: Builtin) -> Option<&'static str> {
    Some(match builtin {
        Builtin::Neg => "~",
        Builtin::DOMAIN => "DOMAIN",
        Builtin::SUBSET => "SUBSET",
        Builtin::UNION => "UNION",
        _ => return None,
    })
}

fn get_binary(builtin: Builtin) -> Option<&'static str> {
    Some(match builtin {
        Builtin::Implies => "\\<Rightarrow>",
        Builtin::Equiv => "\\<Leftrightarrow>",
        Builtin::Conj => "\\<and>",
        Builtin::Disj => "\\<or>",
        Builtin::Eq => "=",
        Builtin::Neq => "\\<noteq>",
        Builtin::Subseteq => "\\<subseteq>",
        Builtin::Mem => "\\<in>",
        Builtin::Notmem => "\\<notin>",
        Builtin::Setminus => "\\\\",
        Builtin::Cap => "\\<inter>",
        Builtin::Cup => "\\<union>",
        Builtin::OneArg => ":>",
        Builtin::Extend => "@@",
        _ => return None,
    })
}

fn get_nonfix(builtin: Builtin) -> Result<Option<(String, usize)>> {
    let plain = |name: &str, arity: usize| Ok(Some((name.to_owned(), arity)));
    match builtin {
        Builtin::Plus => plain("addint", 2),
        Builtin::Minus => plain("subint", 2),
        Builtin::Uminus => plain("minus", 1),
        Builtin::Times => plain("mult", 2),
        Builtin::Ratio => Ok(Some((cook("/")?, 2))),
        Builtin::Quotient => Ok(Some((cook("\\div")?, 2))),
        Builtin::Remainder => Ok(Some((cook("%")?, 2))),
        Builtin::Exp => Ok(Some((cook("^")?, 2))),
        Builtin::Lteq => plain("leq", 2),
        Builtin::Lt => plain("less", 2),
        Builtin::Gteq => plain("geq", 2),
        Builtin::Gt => plain("greater", 2),
        Builtin::Range => plain("intvl", 2),
        Builtin::Seq => plain("Seq", 1),
        Builtin::Len => plain("Len", 1),
        Builtin::BSeq => plain("BSeq", 1),
        Builtin::Cat => Ok(Some((cook("\\circ")?, 2))),
        Builtin::Append => plain("Append", 2),
        Builtin::Head => plain("Head", 1),
        Builtin::Tail => plain("Tail", 1),
        Builtin::SubSeq => plain("SubSeq", 3),
        Builtin::SelectSeq => plain("SelectSeq", 2),
        Builtin::Print => plain("Print", 2),
        Builtin::PrintT => plain("PrintT", 1),
        Builtin::Assert => plain("Assert", 2),
        Builtin::JavaTime => plain("JavaTime", 0),
        Builtin::TLCGet => plain("TLCGet", 1),
        Builtin::TLCSet => plain("TLCSet", 2),
        Builtin::Permutations => plain("Permutations", 1),
        Builtin::SortSeq => plain("SortSeq", 2),
        Builtin::RandomElement => plain("RandomElement", 1),
        Builtin::ToString => plain("ToString", 1),
        _ => Ok(None),
    }
}

/// thy_header's tdoms_table: the operators the theory declares, with their arities.
const DECLARED: [(&str, usize); 8] = [
    ("Real", 0),
    ("/", 2),
    ("\\div", 2),
    ("%", 2),
    ("..", 2),
    ("Infinity", 0),
    ("[]", 1),
    ("<>", 1),
];

fn get_header() -> Result<String> {
    let mut lines = vec!["consts".to_owned()];
    for (name, arity) in DECLARED {
        let domain = if arity == 0 {
            "c".to_owned()
        } else {
            format!("\"[{}] => c\"", vec!["c"; arity].join(","))
        };
        lines.push(format!("  \"{}\" :: {domain}", cook(name)?));
    }
    lines.push(String::new());
    Ok(lines.join("\n"))
}

fn get_successors(integer: &str) -> Result<String> {
    Ok(format!(
        "{}0{}",
        repeat_parsed("succ[", integer)?,
        repeat_parsed("]", integer)?
    ))
}

/// thy_header.
fn get_theory_header(name: &str, is_verbose: bool) -> Result<Vec<String>> {
    let mut lines = vec![
        "(* automatically generated -- do not edit manually *)".to_owned(),
        format!("theory {name} imports Constant Zenon begin"),
    ];
    if is_verbose {
        lines.push("ML_command \\<open> writeln (\"*** TLAPS PARSED\\n\"); \\<close>".to_owned());
    }
    lines.push(get_header()?);
    Ok(lines)
}

/// The closures of `printLemma`, over the names bound where they print.
struct Printer {
    context: Context,
}

impl AsMut<Context> for Printer {
    fn as_mut(&mut self) -> &mut Context {
        &mut self.context
    }
}

struct Lemma {
    text: String,
    is_assumed: bool,
}

impl Printer {
    fn adjoin(&mut self, name: &str) -> Result<String> {
        let pickled = pickle(name)?;
        Ok(push_name(&mut self.context, &pickled))
    }

    fn bump(&mut self) {
        push_name(&mut self.context, "");
    }

    /// A binder's name binds in what prints inside it.
    fn with_bound(
        &mut self,
        name: &str,
        print: impl FnOnce(&mut Self, &str) -> Result<String>,
    ) -> Result<String> {
        let bound = self.adjoin(name)?;
        let printed = print(self, &bound)?;
        pop_names(&mut self.context, 1);
        Ok(printed)
    }

    /// pp_print_expr: every expression, apart from the obligation's sequent, prints in parentheses.
    fn print_expr(&mut self, expression: &Expr) -> Result<String> {
        Ok(format!("({})", self.format_expr(expression)?))
    }

    fn delimited(&mut self, args: &[Expr]) -> Result<String> {
        Ok(args
            .iter()
            .map(|arg| self.print_expr(arg))
            .collect::<Result<Vec<_>>>()?
            .join(", "))
    }

    fn nonfix(&mut self, name: &str, args: &[Expr]) -> Result<String> {
        Ok(format!("({name} ({}))", self.delimited(args)?))
    }

    fn print_internal(&mut self, builtin: Builtin, args: &[Expr]) -> Result<String> {
        if let Some(atom) = get_atom(builtin)?
            && args.is_empty()
        {
            return Ok(atom);
        }
        if let (Some(unary), [arg]) = (get_unary(builtin), args) {
            return Ok(format!("({unary} {})", self.print_expr(arg)?));
        }
        if let (Some(binary), [left, right]) = (get_binary(builtin), args) {
            let left = self.print_expr(left)?;
            return Ok(format!("({left} {binary} {})", self.print_expr(right)?));
        }
        if let Some((name, arity)) = get_nonfix(builtin)?
            && arity == args.len()
        {
            return self.nonfix(&name, args);
        }
        if let (Builtin::Unprimable, [arg]) = (builtin, args) {
            return self.print_expr(arg);
        }
        // tlapm prints an irregular expression as the hash of its TLA+ text, but never makes one.
        if let (Builtin::Irregular, [_]) = (builtin, args) {
            return Err(ObligationError::unsupported("Irregular"));
        }
        Err(get_unprintable_error(
            builtin,
            args.len(),
            "Backend.Isabelle.pp_apply",
        ))
    }

    fn print_apply(&mut self, operator: &Expr, args: &[Expr]) -> Result<String> {
        match &operator.core {
            ExprCore::Ix { index } => {
                let name = get_bound_name(&self.context, *index);
                let Some(name) = name.filter(|_| *index > 0) else {
                    return Err(ObligationError::assert_failure());
                };
                if args.is_empty() {
                    Ok(name)
                } else {
                    Ok(format!("({name} ({}))", self.delimited(args)?))
                }
            }
            ExprCore::Opaque { name } => {
                let name = pickle(name)?;
                if args.is_empty() {
                    Ok(format!("({name} :: c)"))
                } else {
                    Ok(format!("({name} ({}) :: c)", self.delimited(args)?))
                }
            }
            ExprCore::Internal { builtin } => self.print_internal(*builtin, args),
            // tlapm prints a lambda without the arguments it's applied to.
            ExprCore::Lambda { params, body } => {
                let names = params
                    .iter()
                    .map(|param| Ok(format!("{} ", self.adjoin(&param.name)?)))
                    .collect::<Result<String>>()?;
                let printed = format!("\\<lambda> {names}. {}", self.print_expr(body)?);
                pop_names(&mut self.context, params.len());
                Ok(printed)
            }
            _ => Err(ObligationError::assert_failure()),
        }
    }

    fn print_quant(
        &mut self,
        quantifier: Quantifier,
        bounds: &[Bound],
        body: &Expr,
    ) -> Result<String> {
        if bounds.is_empty() {
            return self.format_expr(body);
        }
        let split = split_first_bound(quantifier, bounds, body)?;
        let symbol = if quantifier == Quantifier::Forall {
            "\\<forall>"
        } else {
            "\\<exists>"
        };
        match &split.first.domain {
            BoundDomain::NoDomain => self.with_bound(&split.first.name, |printer, name| {
                Ok(format!(
                    "{symbol}{name} : {}",
                    printer.print_expr(&split.inner)?
                ))
            }),
            BoundDomain::Domain(expression) => {
                let domain = self.print_expr(expression)?;
                self.with_bound(&split.first.name, |printer, name| {
                    Ok(format!(
                        "{symbol} {name} \\<in> {domain} : {}",
                        printer.print_expr(&split.inner)?
                    ))
                })
            }
            BoundDomain::Ditto => Err(ObligationError::assert_failure()),
        }
    }

    /// pp_print_sequent_inner: a sequent inside an expression, as a meta-level implication.
    fn print_nested_sequent(&mut self, context: &[Hyp], active: &Expr) -> Result<String> {
        let Some((hyp, rest)) = context.split_first() else {
            return self.print_expr(active);
        };
        match &hyp.core {
            HypCore::Flex { name } => self.with_bound(name, |printer, name| {
                Ok(format!(
                    "(\\<And> {name} {name}'.{})",
                    printer.print_nested_sequent(rest, active)?
                ))
            }),
            HypCore::Fresh {
                name,
                shape,
                domain,
                domain_visibility,
                ..
            } => {
                if let Some(domain) = domain
                    && *domain_visibility == Visibility::Visible
                {
                    let domain = self.print_expr(domain)?;
                    return self.with_bound(name, |printer, name| {
                        Ok(format!(
                            "(\\<And> {name} :: c. {name} \\<in> {domain} \\<Longrightarrow> {})",
                            printer.print_nested_sequent(rest, active)?
                        ))
                    });
                }
                let shape = format!("{}c", "c => ".repeat(*shape));
                self.with_bound(name, |printer, name| {
                    Ok(format!(
                        "(\\<And> {name} :: {shape}. {})",
                        printer.print_nested_sequent(rest, active)?
                    ))
                })
            }
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
                let printed = match fact {
                    Some(fact) => format!("({fact} \\<Longrightarrow> {printed_rest})"),
                    None => printed_rest,
                };
                pop_names(&mut self.context, 1);
                Ok(printed)
            }
            HypCore::Defn { .. } => Err(ObligationError::unsupported("Inner definition")),
        }
    }

    #[allow(clippy::too_many_lines)]
    fn format_expr(&mut self, expression: &Expr) -> Result<String> {
        match &expression.core {
            ExprCore::Ix { .. }
            | ExprCore::Internal { .. }
            | ExprCore::Opaque { .. }
            | ExprCore::Lambda { .. } => self.print_apply(expression, &[]),
            ExprCore::Apply { operator, args } => self.print_apply(operator, args),
            ExprCore::Bang { .. } => Err(ObligationError::prover("Backend.Isabelle.module")),
            ExprCore::Sequent { sequent } => {
                self.print_nested_sequent(&sequent.context, &sequent.active)
            }
            ExprCore::With {
                expression: inner, ..
            }
            | ExprCore::Parens {
                expression: inner, ..
            } => self.format_expr(inner),
            ExprCore::Let { .. } => Err(ObligationError::unsupported("LET")),
            ExprCore::List { bullet, items } => {
                if *bullet == Bullet::Refs {
                    match items.as_slice() {
                        [] => return Ok("TRUE".to_owned()),
                        [item] => return self.format_expr(item),
                        _ => {}
                    }
                }
                Ok(items
                    .iter()
                    .map(|item| self.print_expr(item))
                    .collect::<Result<Vec<_>>>()?
                    .join(if *bullet == Bullet::Or { " | " } else { " & " }))
            }
            ExprCore::If {
                condition,
                consequent,
                alternative,
            } => {
                let condition = self.print_expr(condition)?;
                let consequent = self.print_expr(consequent)?;
                Ok(format!(
                    "cond({condition}, {consequent}, {})",
                    self.print_expr(alternative)?
                ))
            }
            ExprCore::Quant {
                quantifier,
                bounds,
                body,
            } => self.print_quant(*quantifier, bounds, body),
            ExprCore::Tquant { quantifier, .. } => Err(ObligationError::unsupported(
                if *quantifier == Quantifier::Forall {
                    "\\\\AA"
                } else {
                    "\\\\EE"
                },
            )),
            ExprCore::Choose { name, domain, body } => {
                let Some(domain) = domain else {
                    return self.with_bound(name, |printer, name| {
                        Ok(format!("Choice(%{name}. {})", printer.print_expr(body)?))
                    });
                };
                let domain = self.print_expr(domain)?;
                self.with_bound(name, |printer, name| {
                    Ok(format!(
                        "bChoice({domain}, %{name}. {})",
                        printer.print_expr(body)?
                    ))
                })
            }
            ExprCore::SetSt { name, domain, body } => {
                let domain = self.print_expr(domain)?;
                self.with_bound(name, |printer, name| {
                    Ok(format!(
                        "subsetOf({domain}, %{name}. {})",
                        printer.print_expr(body)?
                    ))
                })
            }
            ExprCore::SetOf { element, bounds } => {
                let Some(bound) = bounds.first() else {
                    return Err(ObligationError::assert_failure());
                };
                let (1, BoundDomain::Domain(domain)) = (bounds.len(), &bound.domain) else {
                    return Err(ObligationError::unsupported(
                        "SetOf (multiple declared constants)",
                    ));
                };
                let domain = self.print_expr(domain)?;
                self.with_bound(&bound.name, |printer, name| {
                    Ok(format!(
                        "setOfAll({domain}, %{name}. {})",
                        printer.print_expr(element)?
                    ))
                })
            }
            ExprCore::SetEnum { elements } => Ok(format!("{{{}}}", self.delimited(elements)?)),
            ExprCore::Fcn { bounds, body } => {
                let [bound] = bounds.as_slice() else {
                    return Err(ObligationError::unsupported(
                        "function (multiple declared constants)",
                    ));
                };
                let domain = match &bound.domain {
                    BoundDomain::Ditto => return Err(ObligationError::assert_failure()),
                    BoundDomain::Domain(domain) => Some(self.print_expr(domain)?),
                    BoundDomain::NoDomain => None,
                };
                self.with_bound(&bound.name, |printer, name| {
                    let printed = match &domain {
                        None => name.to_owned(),
                        Some(domain) => format!(" {name} \\<in> {domain} "),
                    };
                    Ok(format!(
                        "[{printed} \\<mapsto> {}]",
                        printer.print_expr(body)?
                    ))
                })
            }
            ExprCore::FcnApp { function, args } => {
                let printed_function = self.print_expr(function)?;
                if let [arg] = args.as_slice() {
                    return Ok(format!(
                        "fapply ({printed_function}, {})",
                        self.print_expr(arg)?
                    ));
                }
                Ok(format!(
                    "fapply ({printed_function}, <<{}>>)",
                    self.delimited(args)?
                ))
            }
            ExprCore::Arrow { domain, range } => {
                let domain = self.print_expr(domain)?;
                Ok(format!(
                    "[{domain} \\<rightarrow> {}]",
                    self.print_expr(range)?
                ))
            }
            ExprCore::Rect { fields } => {
                let printed = fields
                    .iter()
                    .map(|field| {
                        Ok(format!(
                            "''{}'' : {}",
                            field.name,
                            self.print_expr(&field.value)?
                        ))
                    })
                    .collect::<Result<Vec<_>>>()?;
                Ok(format!("[{}]", printed.join(", ")))
            }
            ExprCore::Record { fields } => {
                let printed = fields
                    .iter()
                    .map(|field| {
                        Ok(format!(
                            "(''{}'' :> {})",
                            field.name,
                            self.print_expr(&field.value)?
                        ))
                    })
                    .collect::<Result<Vec<_>>>()?;
                Ok(format!("({})", printed.join(" @@ ")))
            }
            ExprCore::Except { function, specs } => {
                let specs = specs
                    .iter()
                    .map(|spec| {
                        let trail = spec
                            .trail
                            .iter()
                            .map(|point| match point {
                                ExceptPoint::Dot(field) => Ok(format!("[''{field}'']")),
                                ExceptPoint::Apply(expression) => {
                                    Ok(format!("[{}]", self.print_expr(expression)?))
                                }
                            })
                            .collect::<Result<String>>()?;
                        Ok(format!("!{trail} = {}", self.print_expr(&spec.value)?))
                    })
                    .collect::<Result<Vec<_>>>()?;
                Ok(format!(
                    "[{} EXCEPT {}]",
                    self.print_expr(function)?,
                    specs.join(", ")
                ))
            }
            ExprCore::Dot {
                expression: inner,
                field,
            } => Ok(format!(
                "fapply ({}, (''{field}''))",
                self.print_expr(inner)?
            )),
            ExprCore::Tuple { elements } => Ok(format!("<<{}>>", self.delimited(elements)?)),
            ExprCore::Product { factors } => {
                if let [left, right] = factors.as_slice() {
                    let left = self.print_expr(left)?;
                    return Ok(format!("({left} \\<times> {})", self.print_expr(right)?));
                }
                Ok(format!(
                    "Product(\\<langle>{}\\<rangle>)",
                    self.delimited(factors)?
                ))
            }
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
                let suffix = if matches!(expression.core, ExprCore::Sub { .. }) {
                    "sub"
                } else {
                    "tsub"
                };
                let name = if *modal == Modal::Box {
                    cook(&format!("a'box'{suffix}"))?
                } else {
                    format!("a'dia'{suffix}")
                };
                let action = self.print_expr(action)?;
                Ok(format!("{name}({action},{})", self.print_expr(subscript)?))
            }
            ExprCore::Fair {
                fairness,
                subscript,
                action,
            } => {
                let name = cook(if *fairness == Fairness::Weak {
                    "a'wf"
                } else {
                    "a'sf"
                })?;
                let subscript = self.print_expr(subscript)?;
                Ok(format!("{name}({subscript},{})", self.print_expr(action)?))
            }
            ExprCore::Case { arms, other } => {
                let conditions: Vec<Expr> = arms.iter().map(|arm| arm.condition.clone()).collect();
                let conditions = self.delimited(&conditions)?;
                let bodies: Vec<Expr> = arms.iter().map(|arm| arm.body.clone()).collect();
                let bodies = self.delimited(&bodies)?;
                match other {
                    Some(other) => Ok(format!(
                        "CaseOther(<<{conditions}>>,<<{bodies}>>,{})",
                        self.print_expr(other)?
                    )),
                    None => Ok(format!("Case(<<{conditions}>>,<<{bodies}>>)")),
                }
            }
            ExprCore::String { value } => Ok(format!("''{value}''")),
            ExprCore::Num { integer, fraction } => {
                if !fraction.is_empty() {
                    return Err(ObligationError::unsupported("real constants"));
                }
                Ok(format!("({})", get_successors(integer)?))
            }
            ExprCore::At { .. } => Err(ObligationError::assert_failure()),
        }
    }

    /// pp_print_sequent_outer: the obligation's sequent as the lines of a lemma's fixes, assumes
    /// and shows. A pragma's definition ends it with an empty line in place of the goal.
    fn print_sequent(&mut self, sequent: &Sequent) -> Result<Vec<String>> {
        let mut lines = Vec::new();
        for hyp in &sequent.context {
            match &hyp.core {
                HypCore::Flex { name } => {
                    let name = self.adjoin(name)?;
                    lines.push(format!("fixes {name} {name}'"));
                }
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
                    lines.push(format!("fixes {name}"));
                    let Some(domain) = domain else {
                        continue;
                    };
                    lines.push(format!("assumes {name}_in : \"({name} \\<in> {domain})\""));
                }
                HypCore::Fact {
                    expression,
                    visibility,
                    ..
                } => {
                    let count = self.context.stack.len();
                    let fact = if *visibility == Visibility::Visible {
                        Some(print_fact(self, |printer| printer.print_expr(expression))?)
                    } else {
                        None
                    };
                    self.bump();
                    match fact {
                        Some(Err(error)) => lines.push(format!(
                            "(* omitted temporal assumption : {} *)",
                            error.message()
                        )),
                        Some(Ok(fact)) => lines.push(format!("assumes v'{count}: \"{fact}\"")),
                        None => {}
                    }
                }
                HypCore::Defn { definition, .. } => {
                    if let DefnCore::Bpragma { .. } = definition.core {
                        lines.push(String::new());
                        return Ok(lines);
                    }
                    lines.push(format!(
                        "(* usable definition {} suppressed *)",
                        definition.name()
                    ));
                    self.adjoin(definition.name())?;
                }
            }
        }
        lines.push(format!("shows \"{}\"", self.print_expr(&sequent.active)?));
        Ok(lines)
    }
}

/// pp_print_expr on an obligation after Backend.Prep has shipped it.
fn print_lemma(sequent: &Sequent) -> Result<Lemma> {
    let mut printer = Printer {
        context: create_context(),
    };
    match printer.print_sequent(sequent) {
        Ok(lines) => Ok(Lemma {
            text: lines.join("\n"),
            is_assumed: lines.iter().any(|line| line.starts_with("assumes ")),
        }),
        Err(ObligationError::Unsupported(message)) => Err(ObligationError::prover(format!(
            "isabelle : unsupported operator {message}"
        ))),
        Err(error) => Err(error),
    }
}

/// thy_temp: the theory tlapm writes for Isabelle to prove obligation id.
pub fn encode_isabelle(id: usize, sequent: &Sequent, tactic: &str) -> Result<String> {
    let lemma = print_lemma(sequent)?;
    let mut lines = get_theory_header(&format!("tlapm_{id}"), false)?;
    lines.extend([
        format!("lemma ob'{id}:"),
        format!("{}(is \"PROP ?ob'{id}\")", lemma.text),
        "proof -".to_owned(),
        format!("show \"PROP ?ob'{id}\""),
        format!(
            "{}by {tactic}",
            if lemma.is_assumed { "using assms " } else { "" }
        ),
        "qed".to_owned(),
        "end".to_owned(),
        String::new(),
    ]);
    Ok(lines.join("\n"))
}

pub struct IsabelleProof {
    pub id: usize,
    pub sequent: Sequent,
    pub tactic: String,
}

/// Isabelle.thy_init, thy_write and thy_close.
pub fn encode_isabelle_theory(name: &str, proofs: &[IsabelleProof]) -> Result<String> {
    let mut lines = get_theory_header(name, true)?;
    for proof in proofs {
        let id = proof.id;
        lines.extend([
            format!("lemma ob'{id}:"),
            format!(
                "{}(is \"PROP ?ob'{id}\")",
                print_lemma(&proof.sequent)?.text
            ),
            "proof -".to_owned(),
            format!("ML_command \\<open> writeln \"*** TLAPS ENTER {id}\"; \\<close>"),
            format!("show \"PROP ?ob'{id}\""),
            format!("using assms by {}", proof.tactic),
            format!("ML_command \\<open> writeln \"*** TLAPS EXIT {id}\"; \\<close> qed"),
        ]);
    }
    lines.extend(["end".to_owned(), String::new()]);
    Ok(lines.join("\n"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::first_order::test_cases::{describe, get_cases, to_sequent};

    /// Every shared case encodes to the same theory, or fails with the same error, as
    /// `src/prover/isabelle/encode.ts` under Bun, and so does a theory of several proofs.
    #[test]
    fn encodes_as_the_typescript_does() {
        let cases = get_cases();
        let mut failures = 0;
        for case in cases.items("cases") {
            let actual = encode_isabelle(
                case.count("id"),
                &to_sequent(case.field("input")),
                &case.text("tactic"),
            )
            .map_err(|error| describe(&error));
            let expected = case.field("isabelle").outcome();
            if actual != expected {
                failures += 1;
                eprintln!("expected {expected:?}\nactual   {actual:?}\n");
            }
        }
        assert_eq!(failures, 0);
        let theory = cases.field("theory");
        let proofs: Vec<IsabelleProof> = theory
            .items("proofs")
            .iter()
            .map(|proof| {
                let case = &cases.items("cases")[proof.count("case")];
                IsabelleProof {
                    id: case.count("id"),
                    sequent: to_sequent(case.field("input")),
                    tactic: proof.text("tactic"),
                }
            })
            .collect();
        assert_eq!(
            encode_isabelle_theory(&theory.text("name"), &proofs).map_err(|error| describe(&error)),
            theory.outcome()
        );
    }
}
