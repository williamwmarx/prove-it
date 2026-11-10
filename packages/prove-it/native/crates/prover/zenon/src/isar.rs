// Ported from Zenon's lltoisar.ml and the -oisar path of main.ml, as shipped in tlapm. Copyright
// 2008 INRIA, see LICENSE.
//! Prints a proof as the Isar text that Zenon writes with -oisar, which tlapm checks with Isabelle.
//! Zenon numbers each formula the first time it prints or names it: z_H<n> names a hypothesis and
//! ?z_h<n> abbreviates a formula that an earlier (is "...") pattern bound.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use prove_decide::Limits;

use crate::ZenonError;
use crate::eqrel::Relations;
use crate::expr::{Expr, Expressions, GOAL_NAME, Kind, compare_utf16, efalse, etrue};
use crate::isar_case::{print_case_lemma, print_record_lemma};
use crate::limits::get_limit_failure;
use crate::llproof::{Lemma, LlProof, LlRule, optimise};
use crate::mltoll::{TranslateContext, is_meta_name, translate_proof};
use crate::parse::Phrase;
use crate::proof::{Proof, ProofKey};
use crate::tla::llproof::postprocess_tla;

fn get_infix(symbol: &str) -> Option<&'static str> {
    Some(match symbol {
        "=" => "=",
        "TLA.cup" => " \\\\cup ",
        "TLA.cap" => " \\\\cap ",
        "TLA.setminus" => " \\\\ ",
        "TLA.in" => " \\\\in ",
        "TLA.subseteq" => " \\\\subseteq ",
        "arith.natrange" => "..",
        "arith.add" => " + ",
        "arith.sub" => " - ",
        "arith.mul" => " * ",
        "arith.le" => " <= ",
        "arith.lt" => " < ",
        "TLA.concat" => " \\\\circ ",
        "TLA.oneArg" => " :> ",
        "TLA.extend" => " @@ ",
        _ => return None,
    })
}

fn get_constant(symbol: &str) -> Option<&'static str> {
    Some(match symbol {
        "TLA.emptyset" => "{}",
        "arith.N" => "Nat",
        "arith.Z" => "Int",
        "arith.R" => "isReal",
        "arith.Infinity" => "isInfinity",
        _ => return None,
    })
}

fn get_prefix(symbol: &str) -> Option<&'static str> {
    Some(match symbol {
        "arith.div" => "isa'slash",
        "arith.euclidiv" => "isa'div",
        "arith.mod" => "isa'pc",
        "arith.minus" => " -.",
        "arith.intrange" => "isa'dotdot",
        "TLA.box" => "isa'box",
        _ => return None,
    })
}

/// Zenon drops the namespace of the symbols it doesn't rename.
fn strip_namespace(symbol: &str) -> &str {
    if symbol.len() > 4 && symbol.starts_with("TLA.") {
        &symbol[4..]
    } else if symbol.len() > 6 && symbol.starts_with("arith.") {
        &symbol[6..]
    } else {
        symbol
    }
}

/// Zenon's Misc.base26.
fn to_base26(number: usize) -> String {
    let letter = char::from(b'a' + (number % 26) as u8);
    if number < 26 {
        letter.to_string()
    } else {
        format!("{}{letter}", to_base26(number / 26))
    }
}

fn get_pairs(items: &[Expr]) -> impl Iterator<Item = (&Expr, &Expr)> {
    items
        .as_chunks::<2>()
        .0
        .iter()
        .map(|pair| (&pair[0], &pair[1]))
}

/// The numeral that Zenon prints for 0 and its successors, up to 15.
fn get_numeral(expression: &Expr, limit: i64) -> Option<u32> {
    if limit < 0 {
        return None;
    }
    if expression.kind == Kind::Var && &*expression.symbol == "0" {
        return Some(0);
    }
    if expression.is_app_with_arity("TLA.fapply", 2)
        && expression.args[0].kind == Kind::Var
        && &*expression.args[0].symbol == "TLA.Succ"
    {
        return get_numeral(&expression.args[1], limit - 1).map(|previous| previous + 1);
    }
    None
}

fn get_single(proof: &LlProof) -> Result<&LlProof, ZenonError> {
    match proof.subproofs.as_slice() {
        [single] => Ok(single),
        _ => Err(ZenonError::new("Zenon: expected one subproof")),
    }
}

fn get_last_branch_is_other(branches: &[Vec<Expr>]) -> Result<bool, ZenonError> {
    match branches.last() {
        Some(last) if last.len() == 1 || last.len() == 2 => Ok(last.len() == 2),
        _ => Err(ZenonError::new(
            "Zenon: a CASE rule with a malformed last branch",
        )),
    }
}

/// Zenon's iinc: the indentation stops growing at 15.
fn increment(indent: usize) -> usize {
    if indent >= 15 { indent } else { indent + 1 }
}

/// A length as JavaScript prints it after subtracting from it.
fn to_signed(length: usize) -> i64 {
    i64::try_from(length).unwrap_or(i64::MAX)
}

/// What the search knew when it found a proof: the .znn file's phrases, the proofs that it reused
/// and the properties of relations that the hypotheses stated. The printer stops at the search's
/// limits.
pub struct IsarContext<'a> {
    pub exprs: &'a Expressions,
    pub phrases: &'a [Phrase],
    pub shared_proofs: &'a HashSet<ProofKey>,
    pub relations: &'a Relations,
    pub limits: &'a Limits,
}

/// The Isar text that Zenon prints with -oisar for a proof that the search found, or `None` when
/// the limits stop the printer first.
pub fn print_isar(proof: &Rc<Proof>, context: IsarContext) -> Result<Option<String>, ZenonError> {
    let exprs = context.exprs;
    let numbers: RefCell<HashMap<Expr, usize>> = RefCell::default();
    // Zenon's Index.get_number.
    let get_number = |expression: &Expr| {
        let mut numbers = numbers.borrow_mut();
        let next = numbers.len();
        *numbers.entry(expression.clone()).or_insert(next)
    };
    let lemmas = optimise(
        exprs,
        &postprocess_tla(
            exprs,
            translate_proof(
                &TranslateContext {
                    exprs,
                    get_number: &get_number,
                    shared_proofs: context.shared_proofs,
                    relations: context.relations,
                },
                context.phrases,
                proof,
            )?,
        )?,
    )?;
    print_lemmas(&lemmas, &get_number, context)
}

/// Prints the optimised lemmas, the theorem last, numbering formulas with `get_number`, which the
/// translation numbered formulas with before.
pub fn print_lemmas(
    lemmas: &[Lemma],
    get_number: &dyn Fn(&Expr) -> usize,
    context: IsarContext,
) -> Result<Option<String>, ZenonError> {
    let mut printer = Printer {
        exprs: context.exprs,
        get_number,
        limits: context.limits,
        output: String::new(),
        dict_log: Vec::new(),
        dict_positions: HashMap::new(),
    };
    printer.print_theorem(lemmas, context.phrases)?;
    Ok(get_limit_failure(printer.limits)
        .is_none()
        .then_some(printer.output))
}

struct Printer<'a> {
    exprs: &'a Expressions,
    get_number: &'a dyn Fn(&Expr) -> usize,
    limits: &'a Limits,
    output: String,
    /// The formulas that (is "...") patterns bound, as a persistent set: a version is the length
    /// of the log, and a version only reads the log's prefix, which later additions from it don't
    /// change. `None` stands for a hole that JavaScript leaves when it lengthens an array.
    dict_log: Vec<Option<usize>>,
    dict_positions: HashMap<usize, usize>,
}

impl Printer<'_> {
    fn write(&mut self, text: &str) {
        self.output.push_str(text);
    }

    fn line(&mut self, indent: usize, text: &str) {
        self.output.push_str(&" ".repeat(indent));
        self.output.push_str(text);
    }

    fn get_number(&self, expression: &Expr) -> usize {
        (self.get_number)(expression)
    }

    fn hname(&self, expression: &Expr) -> String {
        format!("z_H{}", to_base26(self.get_number(expression)))
    }

    fn vname(&self, expression: &Expr) -> String {
        format!("?z_h{}", to_base26(self.get_number(expression)))
    }

    fn equal(&self, left: &Expr, right: &Expr) -> Expr {
        self.exprs.eapp("=", &[left.clone(), right.clone()])
    }

    fn to_lambda(&self, binder: &Expr) -> Result<Expr, ZenonError> {
        if binder.kind != Kind::All && binder.kind != Kind::Ex {
            return Err(ZenonError::new("Zenon: expected a quantifier"));
        }
        Ok(self
            .exprs
            .elam(&binder.args[0], &binder.symbol, &binder.args[1]))
    }

    fn is_bound(&self, dict: usize, number: usize) -> bool {
        self.dict_positions.get(&number).is_some_and(|position| {
            *position < dict && self.dict_log.get(*position) == Some(&Some(number))
        })
    }

    fn bind(&mut self, dict: usize, number: usize) -> usize {
        self.dict_log.resize(dict, None);
        self.dict_positions.insert(number, dict);
        self.dict_log.push(Some(number));
        dict + 1
    }

    /// Zenon's p_expr: the bound variables are those that a pattern can't abbreviate.
    fn print_expr(
        &self,
        env: &[Rc<str>],
        dict: usize,
        expression: &Expr,
    ) -> Result<String, ZenonError> {
        let number = self.get_number(expression);
        if self.is_bound(dict, number)
            && !expression.free_vars.iter().any(|name| env.contains(name))
        {
            return Ok(format!("?z_h{}", to_base26(number)));
        }
        let print = |operand: &Expr| self.print_expr(env, dict, operand);
        let print_list = |operands: &[Expr]| -> Result<String, ZenonError> {
            Ok(operands
                .iter()
                .map(print)
                .collect::<Result<Vec<_>, _>>()?
                .join(", "))
        };
        let print_binder =
            |opening: &str, binder: &Expr, separator: &str| -> Result<String, ZenonError> {
                let variable = &binder.args[0].symbol;
                let inner_env: Vec<Rc<str>> = std::iter::once(variable.clone())
                    .chain(env.iter().cloned())
                    .collect();
                Ok(format!(
                    "({opening}{variable}{separator}{})",
                    self.print_expr(&inner_env, dict, &binder.args[1])?
                ))
            };
        Ok(match expression.kind {
            Kind::Var => {
                if is_meta_name(&expression.symbol) {
                    "(CHOOSE x : TRUE)".to_string()
                } else {
                    get_constant(&expression.symbol)
                        .unwrap_or_else(|| strip_namespace(&expression.symbol))
                        .to_string()
                }
            }
            Kind::App => {
                let args = &expression.args;
                match &*expression.symbol {
                    "$string" => {
                        let text = match args.as_slice() {
                            [text] if text.kind == Kind::Var => {
                                text.symbol.encode_utf16().collect::<Vec<_>>()
                            }
                            _ => return Err(ZenonError::new("Zenon: a malformed string")),
                        };
                        if text.len() < 2 {
                            return Err(ZenonError::new("Zenon: a malformed string"));
                        }
                        return Ok(format!(
                            "''{}''",
                            String::from_utf16_lossy(&text[1..text.len() - 1])
                        ));
                    }
                    "TLA.set" => return Ok(format!("{{{}}}", print_list(args)?)),
                    "TLA.tuple" => return Ok(format!("<<{}>>", print_list(args)?)),
                    "TLA.record" => {
                        let pairs = get_pairs(args)
                            .map(|pair| Ok(format!("{} :> ({})", print(pair.0)?, print(pair.1)?)))
                            .collect::<Result<Vec<_>, ZenonError>>()?;
                        return Ok(format!("({})", pairs.join(" @@ ")));
                    }
                    "TLA.recordset" => {
                        let pairs = get_pairs(args)
                            .map(|pair| Ok(format!("{} : ({})", print(pair.0)?, print(pair.1)?)))
                            .collect::<Result<Vec<_>, ZenonError>>()?;
                        return Ok(format!("[{}]", pairs.join(", ")));
                    }
                    "TLA.CASE" => {
                        return Ok(format!("(CASE {})", self.print_case_arms(env, dict, args)?));
                    }
                    _ => {}
                }
                if expression.is_app_with_arity("TLA.fapply", 2) {
                    let numeral = if args[0].kind == Kind::Var && &*args[0].symbol == "TLA.Succ" {
                        get_numeral(&args[1], 14)
                    } else {
                        None
                    };
                    if let Some(numeral) = numeral {
                        return Ok((numeral + 1).to_string());
                    }
                    return Ok(format!("({}[{}])", print(&args[0])?, print(&args[1])?));
                }
                if let Some(infix) = get_infix(&expression.symbol)
                    && args.len() == 2
                {
                    return Ok(format!("({}{infix}{})", print(&args[0])?, print(&args[1])?));
                }
                if args.is_empty() {
                    return Ok(expression.symbol.to_string());
                }
                format!(
                    "{}({})",
                    get_prefix(&expression.symbol)
                        .unwrap_or_else(|| strip_namespace(&expression.symbol)),
                    print_list(args)?
                )
            }
            Kind::Not => {
                let operand = &expression.args[0];
                if operand.is_app_with_arity("=", 2) {
                    format!(
                        "({}~={})",
                        print(&operand.args[0])?,
                        print(&operand.args[1])?
                    )
                } else {
                    format!("(~{})", print(operand)?)
                }
            }
            Kind::And => format!(
                "({}&{})",
                print(&expression.args[0])?,
                print(&expression.args[1])?
            ),
            Kind::Or => format!(
                "({}|{})",
                print(&expression.args[0])?,
                print(&expression.args[1])?
            ),
            Kind::Imply => format!(
                "({}=>{})",
                print(&expression.args[0])?,
                print(&expression.args[1])?
            ),
            Kind::Equiv => format!(
                "({}<=>{})",
                print(&expression.args[0])?,
                print(&expression.args[1])?
            ),
            Kind::True => "TRUE".to_string(),
            Kind::False => "FALSE".to_string(),
            Kind::All => print_binder("\\\\A ", expression, ":")?,
            Kind::Ex => print_binder("\\\\E ", expression, ":")?,
            Kind::Lam => print_binder("\\<lambda>", expression, ". ")?,
            Kind::Tau => print_binder("CHOOSE ", expression, ":")?,
            Kind::Meta => return Err(ZenonError::new("Zenon: a metavariable in the Isar output")),
        })
    }

    fn print_case_arms(
        &self,
        env: &[Rc<str>],
        dict: usize,
        arms: &[Expr],
    ) -> Result<String, ZenonError> {
        let print = |operand: &Expr| self.print_expr(env, dict, operand);
        match arms {
            [] => Err(ZenonError::new("Zenon: a CASE without arms")),
            [other] => Ok(format!("OTHER -> {}", print(other)?)),
            [condition, value, rest @ ..] => {
                let head = format!("{} -> {}", print(condition)?, print(value)?);
                if rest.is_empty() {
                    Ok(head)
                } else {
                    Ok(format!(
                        "{head} [] {}",
                        self.print_case_arms(env, dict, rest)?
                    ))
                }
            }
        }
    }

    fn expr(&self, dict: usize, expression: &Expr) -> Result<String, ZenonError> {
        self.print_expr(&[], dict, expression)
    }

    /// Zenon's p_apply: the instance of a lambda, through the lambda's abbreviation if it has one.
    fn print_apply(
        &self,
        dict: usize,
        lambda: &Expr,
        argument: &Expr,
    ) -> Result<String, ZenonError> {
        let number = self.get_number(lambda);
        if self.is_bound(dict, number) {
            Ok(format!(
                "?z_h{}({})",
                to_base26(number),
                self.expr(dict, argument)?
            ))
        } else {
            self.expr(dict, &self.exprs.apply(lambda, argument)?)
        }
    }

    /// Zenon's mk_pat: a pattern variable for a formula that has none yet.
    fn make_pattern(&mut self, dict: usize, expression: &Expr) -> (String, usize) {
        if expression.kind == Kind::Var && !is_meta_name(&expression.symbol) {
            return ("_".to_string(), dict);
        }
        let number = self.get_number(expression);
        if self.is_bound(dict, number) {
            ("_".to_string(), dict)
        } else {
            (self.vname(expression), self.bind(dict, number))
        }
    }

    fn print_is_binary(
        &mut self,
        dict: usize,
        prefix: &str,
        left: &Expr,
        operator: &str,
        right: &Expr,
        suffix: &str,
    ) -> usize {
        let first = self.make_pattern(dict, left);
        let second = self.make_pattern(first.1, right);
        if first.0 == "_" && second.0 == "_" {
            self.write("\n");
        } else {
            self.write(&format!(
                " (is \"{prefix}{}{operator}{}{suffix}\")\n",
                first.0, second.0
            ));
        }
        second.1
    }

    fn print_is_unary(&mut self, dict: usize, prefix: &str, operand: &Expr, suffix: &str) -> usize {
        let pattern = self.make_pattern(dict, operand);
        if pattern.0 == "_" {
            self.write("\n");
        } else {
            self.write(&format!(" (is \"{prefix}{}{suffix}\")\n", pattern.0));
        }
        pattern.1
    }

    /// Zenon's p_is: binds the formula's parts to pattern variables.
    fn print_is(&mut self, dict: usize, formula: &Expr) -> Result<usize, ZenonError> {
        let args = &formula.args;
        match formula.kind {
            Kind::And => return Ok(self.print_is_binary(dict, "", &args[0], "&", &args[1], "")),
            Kind::Or => return Ok(self.print_is_binary(dict, "", &args[0], "|", &args[1], "")),
            Kind::Imply => return Ok(self.print_is_binary(dict, "", &args[0], "=>", &args[1], "")),
            Kind::Equiv => return Ok(self.print_is_binary(dict, "", &args[0], "<=>", &args[1], "")),
            Kind::All => {
                let lambda = self.to_lambda(formula)?;
                return Ok(self.print_is_unary(dict, "\\\\A x : ", &lambda, "(x)"));
            }
            Kind::Ex => {
                let lambda = self.to_lambda(formula)?;
                return Ok(self.print_is_unary(dict, "\\\\E x : ", &lambda, "(x)"));
            }
            _ => {}
        }
        if formula.is_app_with_arity("=", 2) {
            return Ok(self.print_is_binary(dict, "", &args[0], "=", &args[1], ""));
        }
        if formula.kind != Kind::Not {
            return Ok(self.print_is_unary(dict, "", formula, ""));
        }
        let operand = &args[0];
        let inner = &operand.args;
        Ok(match operand.kind {
            Kind::And => self.print_is_binary(dict, "~(", &inner[0], "&", &inner[1], ")"),
            Kind::Or => self.print_is_binary(dict, "~(", &inner[0], "|", &inner[1], ")"),
            Kind::Imply => self.print_is_binary(dict, "~(", &inner[0], "=>", &inner[1], ")"),
            Kind::Equiv => self.print_is_binary(dict, "~(", &inner[0], "<=>", &inner[1], ")"),
            Kind::All => {
                let lambda = self.to_lambda(operand)?;
                self.print_is_unary(dict, "~(\\\\A x : ", &lambda, "(x))")
            }
            Kind::Ex => {
                let lambda = self.to_lambda(operand)?;
                self.print_is_unary(dict, "~(\\\\E x : ", &lambda, "(x))")
            }
            Kind::Not => self.print_is_unary(dict, "~~", &inner[0], ""),
            _ if operand.is_app_with_arity("=", 2) => {
                self.print_is_binary(dict, "", &inner[0], "~=", &inner[1], "")
            }
            _ => self.print_is_unary(dict, "~", operand, ""),
        })
    }

    fn print_let(
        &mut self,
        dict: usize,
        indent: usize,
        expression: &Expr,
    ) -> Result<usize, ZenonError> {
        let pattern = self.make_pattern(dict, expression);
        if pattern.0 != "_" {
            let text = format!("let {} = \"{}\"\n", pattern.0, self.expr(dict, expression)?);
            self.line(indent, &text);
        }
        Ok(pattern.1)
    }

    fn print_sequent(
        &mut self,
        indent: usize,
        dict: usize,
        formulas: &[Expr],
    ) -> Result<usize, ZenonError> {
        formulas.iter().try_fold(dict, |current, formula| {
            let text = format!(
                "assume {}:\"{}\"",
                self.hname(formula),
                self.expr(current, formula)?
            );
            self.line(indent, &text);
            self.print_is(current, formula)
        })
    }

    /// Zenon's p_sub: each branch assumes its formulas and proves FALSE.
    fn print_branches(
        &mut self,
        indent: usize,
        dict: usize,
        branches: &[Vec<Expr>],
        subproofs: &[Rc<LlProof>],
    ) -> Result<(), ZenonError> {
        if branches.len() != subproofs.len() {
            return Err(ZenonError::new(
                "Zenon: a rule whose branches don't match its subproofs",
            ));
        }
        for (position, branch) in branches.iter().enumerate() {
            let sequent = self.print_sequent(increment(indent), dict, branch)?;
            self.print_tree(increment(indent), sequent, &subproofs[position])?;
            self.line(
                indent,
                if position == branches.len() - 1 {
                    "qed\n"
                } else {
                    "next\n"
                },
            );
        }
        Ok(())
    }

    /// A have for each formula of the branch that the subproof uses, then the subproof.
    fn print_haves(
        &mut self,
        indent: usize,
        dict: usize,
        formulas: &[Expr],
        subproof: &LlProof,
        get_justification: impl Fn(&Self, usize, usize) -> Result<String, ZenonError>,
    ) -> Result<(), ZenonError> {
        let mut current = dict;
        for (position, formula) in formulas.iter().enumerate() {
            if !subproof.conclusions.contains(formula) {
                continue;
            }
            let text = format!(
                "have {}: \"{}\"",
                self.hname(formula),
                self.expr(current, formula)?
            );
            self.line(indent, &text);
            let next = self.print_is(current, formula)?;
            let justification = get_justification(self, next, position)?;
            self.line(indent, &justification);
            current = next;
        }
        self.print_tree(indent, current, subproof)
    }

    fn print_alpha(
        &mut self,
        indent: usize,
        dict: usize,
        lemma: &str,
        conclusion: &Expr,
        formulas: &[Expr],
        proof: &LlProof,
    ) -> Result<(), ZenonError> {
        let subproof = get_single(proof)?;
        let conclusion_name = self.hname(conclusion);
        self.print_haves(indent, dict, formulas, subproof, |_, _, position| {
            Ok(format!(
                "by (rule zenon_{lemma}_{position} [OF {conclusion_name}])\n"
            ))
        })
    }

    fn print_beta(
        &mut self,
        indent: usize,
        dict: usize,
        lemma: &str,
        conclusion: &Expr,
        branches: &[Vec<Expr>],
        proof: &LlProof,
    ) -> Result<(), ZenonError> {
        let conclusion_name = self.hname(conclusion);
        self.line(indent, "show FALSE\n");
        self.line(
            indent,
            &format!("proof (rule zenon_{lemma} [OF {conclusion_name}])\n"),
        );
        self.print_branches(indent, dict, branches, &proof.subproofs)
    }

    /// Zenon's p_gamma and p_delta: the instance of a quantified formula.
    #[expect(clippy::too_many_arguments, reason = "a literal port of printInstance")]
    fn print_instance(
        &mut self,
        indent: usize,
        dict: usize,
        lemma: &str,
        is_negated: bool,
        quantified: &Expr,
        term: &Expr,
        conclusion: &Expr,
        proof: &LlProof,
        is_gamma: bool,
    ) -> Result<(), ZenonError> {
        let subproof = get_single(proof)?;
        let lambda = self.to_lambda(quantified)?;
        let instance = self.exprs.apply(&lambda, term)?;
        let body = if is_negated {
            self.exprs.enot(&instance)
        } else {
            instance
        };
        let text = format!(
            "have {}: \"{}{}\"",
            self.hname(&body),
            if is_negated { "~" } else { "" },
            self.print_apply(dict, &lambda, term)?
        );
        self.line(indent, &text);
        let next = self.print_is(dict, &body)?;
        let conclusion_name = self.hname(conclusion);
        let terms = if is_gamma {
            format!(
                "\"{}\" \"{}\"",
                self.expr(next, &lambda)?,
                self.expr(next, term)?
            )
        } else {
            format!("\"{}\"", self.expr(next, &lambda)?)
        };
        self.line(
            indent,
            &format!("by (rule zenon_{lemma}_0 [of {terms}, OF {conclusion_name}])\n"),
        );
        self.print_tree(indent, next, subproof)
    }

    /// Zenon's p_sub_equal: proves an argument equal to the other, unless the subproof needn't.
    fn print_sub_equal(
        &mut self,
        indent: usize,
        dict: usize,
        left: &Expr,
        right: &Expr,
        subproof: &LlProof,
    ) -> Result<usize, ZenonError> {
        let equality = self.equal(left, right);
        if left == right || subproof.conclusions.contains(&equality) {
            return Ok(dict);
        }
        let negation = self.exprs.enot(&equality);
        let text = format!(
            "have {}: \"{}\"",
            self.hname(&equality),
            self.expr(dict, &equality)?
        );
        self.line(indent, &text);
        let next = self.print_is(dict, &equality)?;
        let reversed = self.equal(right, left);
        if subproof.conclusions.contains(&reversed) {
            let text = format!("by (rule sym [OF {}])\n", self.hname(&reversed));
            self.line(indent, &text);
            return Ok(next);
        }
        let text = format!(
            "proof (rule zenon_nnpp [of \"{}\"])\n",
            self.expr(next, &equality)?
        );
        self.line(indent, &text);
        let sequent = self.print_sequent(increment(indent), next, &[negation])?;
        self.print_tree(increment(indent), sequent, subproof)?;
        self.line(indent, "qed\n");
        Ok(next)
    }

    /// Zenon's p_subst: rewrites the arguments that differ one at a time.
    #[expect(
        clippy::too_many_arguments,
        reason = "a literal port of printSubstitution"
    )]
    fn print_substitution(
        &mut self,
        indent: usize,
        dict: usize,
        make: &dyn Fn(&[Expr]) -> Expr,
        lefts: &[Expr],
        rights: &[Expr],
        done: Vec<Expr>,
        previous: &Expr,
    ) -> Result<(), ZenonError> {
        if lefts.len() != rights.len() {
            return Err(ZenonError::new("Zenon: arguments of different lengths"));
        }
        let (Some(left), Some(right)) = (lefts.first(), rights.first()) else {
            let text = format!("thus \"{}\" .\n", self.expr(dict, previous)?);
            self.line(increment(indent), &text);
            self.line(indent, "qed\n");
            return Ok(());
        };
        let done_with_right = [done.as_slice(), std::slice::from_ref(right)].concat();
        if left == right {
            return self.print_substitution(
                indent,
                dict,
                make,
                &lefts[1..],
                &rights[1..],
                done_with_right,
                previous,
            );
        }
        let variable = self.exprs.new_var();
        let context = self.exprs.elam(
            &variable,
            "",
            &make(
                &[
                    done.as_slice(),
                    std::slice::from_ref(&variable),
                    &lefts[1..],
                ]
                .concat(),
            ),
        );
        let instance = self.exprs.apply(&context, right)?;
        let text = format!(
            "have {}: \"{}\"",
            self.hname(&instance),
            self.expr(dict, &instance)?
        );
        self.line(increment(indent), &text);
        let next = self.print_is(dict, &instance)?;
        let previous_name = self.hname(previous);
        let equality_name = self.hname(&self.equal(left, right));
        let text = format!(
            "by (rule subst [where P=\"{}\", OF {equality_name}], fact {previous_name})\n",
            self.expr(next, &context)?
        );
        self.line(increment(indent), &text);
        self.print_substitution(
            indent,
            next,
            make,
            &lefts[1..],
            &rights[1..],
            done_with_right,
            &instance,
        )
    }

    fn print_args(&self, dict: usize, args: &[Expr]) -> Result<String, ZenonError> {
        Ok(args
            .iter()
            .map(|arg| Ok(format!("\"{}\"", self.expr(dict, arg)?)))
            .collect::<Result<Vec<_>, ZenonError>>()?
            .join(" "))
    }

    fn print_names(&self, formulas: &[Expr]) -> String {
        formulas
            .iter()
            .map(|formula| self.hname(formula))
            .collect::<Vec<_>>()
            .join(" ")
    }

    fn print_tree(
        &mut self,
        indent: usize,
        dict: usize,
        proof: &LlProof,
    ) -> Result<(), ZenonError> {
        if get_limit_failure(self.limits).is_some() {
            return Ok(());
        }
        let exprs = self.exprs;
        match &proof.rule {
            LlRule::Connect {
                connective,
                left,
                right,
            } => match connective {
                Kind::And => self.print_alpha(
                    indent,
                    dict,
                    "and",
                    &exprs.eand(left, right),
                    &[left.clone(), right.clone()],
                    proof,
                ),
                Kind::Or => self.print_beta(
                    indent,
                    dict,
                    "or",
                    &exprs.eor(left, right),
                    &[vec![left.clone()], vec![right.clone()]],
                    proof,
                ),
                Kind::Imply => {
                    let conclusion = exprs.eimply(left, right);
                    let branches = [vec![exprs.enot(left)], vec![right.clone()]];
                    self.print_beta(indent, dict, "imply", &conclusion, &branches, proof)
                }
                Kind::Equiv => {
                    let conclusion = exprs.eequiv(left, right);
                    let branches = [
                        vec![exprs.enot(left), exprs.enot(right)],
                        vec![left.clone(), right.clone()],
                    ];
                    self.print_beta(indent, dict, "equiv", &conclusion, &branches, proof)
                }
                _ => Ok(()),
            },
            LlRule::NotConnect {
                connective,
                left,
                right,
            } => match connective {
                Kind::And => {
                    let conclusion = exprs.enot(&exprs.eand(left, right));
                    let branches = [vec![exprs.enot(left)], vec![exprs.enot(right)]];
                    self.print_beta(indent, dict, "notand", &conclusion, &branches, proof)
                }
                Kind::Or => {
                    let conclusion = exprs.enot(&exprs.eor(left, right));
                    let formulas = [exprs.enot(left), exprs.enot(right)];
                    self.print_alpha(indent, dict, "notor", &conclusion, &formulas, proof)
                }
                Kind::Imply => {
                    let conclusion = exprs.enot(&exprs.eimply(left, right));
                    let formulas = [left.clone(), exprs.enot(right)];
                    self.print_alpha(indent, dict, "notimply", &conclusion, &formulas, proof)
                }
                Kind::Equiv => {
                    let conclusion = exprs.enot(&exprs.eequiv(left, right));
                    let branches = [
                        vec![exprs.enot(left), right.clone()],
                        vec![left.clone(), exprs.enot(right)],
                    ];
                    self.print_beta(indent, dict, "notequiv", &conclusion, &branches, proof)
                }
                _ => Ok(()),
            },
            LlRule::Extension {
                name,
                args,
                conclusions,
                branches,
            } => self.print_extension(indent, dict, proof, name, args, conclusions, branches),
            LlRule::NotNot(formula) => self.print_alpha(
                indent,
                dict,
                "notnot",
                &exprs.enot(&exprs.enot(formula)),
                std::slice::from_ref(formula),
                proof,
            ),
            LlRule::Ex { quantified, term } => self.print_instance(
                indent,
                dict,
                "ex_choose",
                false,
                quantified,
                term,
                quantified,
                proof,
                false,
            ),
            LlRule::NotAll { quantified, term } => self.print_instance(
                indent,
                dict,
                "notall_choose",
                true,
                quantified,
                term,
                &exprs.enot(quantified),
                proof,
                false,
            ),
            LlRule::All { quantified, term } => self.print_instance(
                indent, dict, "all", false, quantified, term, quantified, proof, true,
            ),
            LlRule::NotEx { quantified, term } => self.print_instance(
                indent,
                dict,
                "notex",
                true,
                quantified,
                term,
                &exprs.enot(quantified),
                proof,
                true,
            ),
            LlRule::Lemma { name, args } => {
                let variables = args
                    .iter()
                    .filter_map(|arg| match arg.kind {
                        Kind::Var => Some(Ok(arg.symbol.clone())),
                        Kind::Tau => None,
                        _ => Some(Err(ZenonError::new(
                            "Zenon: a lemma argument that is neither a variable nor a tau",
                        ))),
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                self.line(indent, "show FALSE\n");
                self.line(indent, &format!("by (rule {name} ["));
                if !variables.is_empty() {
                    let text = variables
                        .iter()
                        .map(|variable| format!("?{variable}={variable}"))
                        .collect::<Vec<_>>()
                        .join(" and ");
                    self.write(&format!("where {text}, "));
                }
                let text = format!("OF {}])\n", self.print_names(&proof.conclusions));
                self.write(&text);
                Ok(())
            }
            LlRule::Cut(formula) => {
                self.line(indent, "show FALSE\n");
                let text = format!(
                    "proof (rule zenon_em [of \"{}\"])\n",
                    self.expr(dict, formula)?
                );
                self.line(indent, &text);
                let branches = [vec![formula.clone()], vec![exprs.enot(formula)]];
                self.print_branches(indent, dict, &branches, &proof.subproofs)
            }
            LlRule::Axiom(formula) => {
                let positive_name = self.hname(formula);
                let negative_name = self.hname(&exprs.enot(formula));
                self.line(indent, "show FALSE\n");
                self.line(
                    indent,
                    &format!("by (rule notE [OF {negative_name} {positive_name}])\n"),
                );
                Ok(())
            }
            LlRule::Definition {
                name,
                folded,
                unfolded,
            } => {
                let conclusion_name = self.hname(folded);
                let hypothesis_name = self.hname(unfolded);
                let text = format!(
                    "have {hypothesis_name}_{conclusion_name}: \"{} == {}\"",
                    self.expr(dict, unfolded)?,
                    self.expr(dict, folded)?
                );
                self.line(indent, &text);
                let hypothesis_pattern = self.make_pattern(dict, unfolded);
                let conclusion_pattern = self.make_pattern(hypothesis_pattern.1, folded);
                self.write(&format!(
                    " (is \"{} == {}\")\n",
                    hypothesis_pattern.0, conclusion_pattern.0
                ));
                self.line(indent, &format!("by (unfold {name})\n"));
                let text = format!(
                    "have {hypothesis_name}: \"{}\"",
                    self.expr(conclusion_pattern.1, unfolded)?
                );
                self.line(indent, &text);
                let next = self.print_is(conclusion_pattern.1, unfolded)?;
                self.line(
                    indent,
                    &format!(
                        "by (unfold {hypothesis_name}_{conclusion_name}, fact {conclusion_name})\n"
                    ),
                );
                self.print_tree(indent, next, get_single(proof)?)
            }
            LlRule::NotEqual { left, right } => {
                if left.kind != Kind::App || right.kind != Kind::App || left.symbol != right.symbol
                {
                    return Err(ZenonError::new("Zenon: notequal on different applications"));
                }
                let negation = exprs.enot(&self.equal(left, right));
                self.line(indent, "show FALSE\n");
                let text = format!(
                    "proof (rule zenon_noteq [of \"{}\"])\n",
                    self.expr(dict, right)?
                );
                self.line(indent, &text);
                let next = self.print_argument_equalities(
                    indent,
                    dict,
                    &left.args,
                    &right.args,
                    &proof.subproofs,
                )?;
                let make = |args: &[Expr]| {
                    exprs.enot(&exprs.eapp("=", &[exprs.eapp(&left.symbol, args), right.clone()]))
                };
                self.print_substitution(
                    indent,
                    next,
                    &make,
                    &left.args,
                    &right.args,
                    Vec::new(),
                    &negation,
                )
            }
            LlRule::PNotP { positive, negative } => {
                let negated = (negative.kind == Kind::Not).then(|| &negative.args[0]);
                let Some(negated) = negated.filter(|negated| {
                    positive.kind == Kind::App
                        && negated.kind == Kind::App
                        && positive.symbol == negated.symbol
                }) else {
                    return Err(ZenonError::new("Zenon: pnotp on different applications"));
                };
                self.line(indent, "show FALSE\n");
                let text = format!("proof (rule notE [OF {}])\n", self.hname(negative));
                self.line(indent, &text);
                let next = self.print_argument_equalities(
                    indent,
                    dict,
                    &positive.args,
                    &negated.args,
                    &proof.subproofs,
                )?;
                let make = |args: &[Expr]| exprs.eapp(&positive.symbol, args);
                self.print_substitution(
                    indent,
                    next,
                    &make,
                    &positive.args,
                    &negated.args,
                    Vec::new(),
                    positive,
                )
            }
            LlRule::NotEq(term) => {
                let name = self.hname(&exprs.enot(&self.equal(term, term)));
                self.line(indent, "show FALSE\n");
                self.line(indent, &format!("by (rule zenon_noteq [OF {name}])\n"));
                Ok(())
            }
            LlRule::EqSym { left, right } => {
                let equality_name = self.hname(&self.equal(left, right));
                let negation_name = self.hname(&exprs.enot(&self.equal(right, left)));
                self.line(indent, "show FALSE\n");
                self.line(
                    indent,
                    &format!("by (rule zenon_eqsym [OF {equality_name} {negation_name}])\n"),
                );
                Ok(())
            }
            LlRule::NotTrue => {
                self.line(indent, "show FALSE\n");
                let text = format!(
                    "by (rule zenon_nottrue [OF {}])\n",
                    self.hname(&exprs.enot(&etrue()))
                );
                self.line(indent, &text);
                Ok(())
            }
            LlRule::False => {
                self.line(indent, "show FALSE\n");
                let text = format!("by (rule {})\n", self.hname(&efalse()));
                self.line(indent, &text);
                Ok(())
            }
            LlRule::CongruenceLr {
                context,
                left,
                right,
            }
            | LlRule::CongruenceRl {
                context,
                left,
                right,
            } => {
                let is_left_to_right = matches!(proof.rule, LlRule::CongruenceLr { .. });
                let subproof = get_single(proof)?;
                let equality = if is_left_to_right {
                    self.equal(left, right)
                } else {
                    self.equal(right, left)
                };
                let hypothesis = exprs.apply(context, left)?;
                let conclusion = exprs.apply(context, right)?;
                let text = format!(
                    "have {}: \"{}\"",
                    self.hname(&conclusion),
                    self.expr(dict, &conclusion)?
                );
                self.line(indent, &text);
                let next = self.print_is(dict, &conclusion)?;
                let hypothesis_name = self.hname(&hypothesis);
                let equality_name = self.hname(&equality);
                let lemma = if is_left_to_right { "subst" } else { "ssubst" };
                let text = format!(
                    "by (rule {lemma} [where P=\"{}\", OF {equality_name} {hypothesis_name}])\n",
                    self.expr(next, context)?
                );
                self.line(indent, &text);
                self.print_tree(indent, next, subproof)
            }
        }
    }

    fn print_argument_equalities(
        &mut self,
        indent: usize,
        dict: usize,
        lefts: &[Expr],
        rights: &[Expr],
        subproofs: &[Rc<LlProof>],
    ) -> Result<usize, ZenonError> {
        if lefts.len() != rights.len() || lefts.len() != subproofs.len() {
            return Err(ZenonError::new("Zenon: list_fold_left3"));
        }
        lefts
            .iter()
            .enumerate()
            .try_fold(dict, |current, (position, left)| {
                self.print_sub_equal(
                    increment(indent),
                    current,
                    left,
                    &rights[position],
                    &subproofs[position],
                )
            })
    }

    /// A hypothesis of a product or record set's rules, and its negation, each in its own branch.
    fn print_negated_haves(
        &mut self,
        indent: usize,
        dict: usize,
        branches: &[Vec<Expr>],
        subproofs: &[Rc<LlProof>],
    ) -> Result<usize, ZenonError> {
        if branches.len() != subproofs.len() {
            return Err(ZenonError::new("Zenon: List.fold_left2"));
        }
        branches
            .iter()
            .enumerate()
            .try_fold(dict, |current, (position, branch)| {
                let negation = get_negation(branch)?;
                let formula = &negation.args[0];
                let text = format!(
                    "have {}: \"{}\"",
                    self.hname(formula),
                    self.expr(current, formula)?
                );
                self.line(indent, &text);
                let next = self.print_is(current, formula)?;
                self.line(indent, "proof (rule zenon_nnpp)\n");
                let text = format!(
                    "assume {}: \"{}\"",
                    self.hname(negation),
                    self.expr(next, negation)?
                );
                self.line(indent + 1, &text);
                let sequent = self.print_is(next, negation)?;
                self.print_tree(indent + 1, sequent, &subproofs[position])?;
                self.line(indent, "qed\n");
                Ok(next)
            })
    }

    fn get_negated_names(&self, branches: &[Vec<Expr>]) -> Result<String, ZenonError> {
        branches
            .iter()
            .map(|branch| Ok(format!("{} ", self.hname(&get_negation(branch)?.args[0]))))
            .collect()
    }

    #[expect(clippy::too_many_arguments, reason = "the fields of an extension rule")]
    fn print_extension(
        &mut self,
        indent: usize,
        dict: usize,
        proof: &LlProof,
        name: &str,
        args: &[Expr],
        conclusions: &[Expr],
        branches: &[Vec<Expr>],
    ) -> Result<(), ZenonError> {
        let exprs = self.exprs;
        let malformed = || ZenonError::new(format!("Zenon: a malformed {name} rule"));
        match name {
            "zenon_case" => {
                if args.len() != 1 || conclusions.len() != 1 {
                    return Err(malformed());
                }
                let is_other = get_last_branch_is_other(branches)?;
                let conclusion_name = self.hname(&conclusions[0]);
                self.line(indent, "show FALSE\n");
                let text = format!(
                    "proof (rule zenon_case{}{} [of \"{}\", OF {conclusion_name}])\n",
                    if is_other { "other" } else { "" },
                    to_signed(branches.len()) - 1,
                    self.expr(dict, &args[0])?
                );
                self.line(indent, &text);
                return self.print_branches(indent, dict, branches, &proof.subproofs);
            }
            "zenon_stringequal" => {
                if args.len() != 2 || conclusions.len() != 1 || !branches.is_empty() {
                    return Err(malformed());
                }
                let conclusion = &conclusions[0];
                let negation = exprs.enot(conclusion);
                let text = format!(
                    "have {}: \"{}\"\n",
                    self.hname(&negation),
                    self.expr(dict, &negation)?
                );
                self.line(indent, &text);
                self.line(indent, "by (simp only: zenon_sa_1 zenon_sa_2,\n");
                self.line(indent, "    ((rule zenon_sa_diff_2)+)?,\n");
                self.line(indent, "    (rule zenon_sa_diff_3, auto)?,\n");
                self.line(indent, "    (rule zenon_sa_diff_1, auto)?,\n");
                self.line(
                    indent,
                    "    (rule zenon_sa_diff_0a)?, (rule zenon_sa_diff_0b)?)\n",
                );
                self.line(indent, "show FALSE\n");
                let conclusion_name = self.hname(conclusion);
                let text = format!(
                    "by (rule notE [OF {} {conclusion_name}])\n",
                    self.hname(&negation)
                );
                self.line(indent, &text);
                return Ok(());
            }
            "zenon_stringdiffll" | "zenon_stringdifflr" | "zenon_stringdiffrl"
            | "zenon_stringdiffrr" => {
                let hypothesis = match branches {
                    [branch] if branch.len() == 1 => &branch[0],
                    _ => return Err(malformed()),
                };
                if args.len() != 4 || conclusions.len() != 2 {
                    return Err(malformed());
                }
                let subproof = get_single(proof)?;
                let difference = exprs.enot(&self.equal(&args[1], &args[3]));
                let text = format!(
                    "have {}: \"{}\"\n",
                    self.hname(&difference),
                    self.expr(dict, &difference)?
                );
                self.line(indent, &text);
                self.line(indent, "by auto\n");
                let text = format!(
                    "have {}: \"{}\"",
                    self.hname(hypothesis),
                    self.expr(dict, hypothesis)?
                );
                self.line(indent, &text);
                let next = self.print_is(dict, hypothesis)?;
                let second_name = self.hname(&conclusions[1]);
                let first_name = self.hname(&conclusions[0]);
                let text = format!(
                    "by (rule {name} [OF {} {first_name} {second_name}])\n",
                    self.hname(&difference)
                );
                self.line(indent, &text);
                return self.print_tree(increment(indent), next, subproof);
            }
            "zenon_tuple_eq_match" | "zenon_record_eq_match" => {
                if !args.is_empty() || conclusions.len() != 1 || branches.len() != 1 {
                    return Err(malformed());
                }
                let conclusion = &conclusions[0];
                return self.print_haves(
                    indent,
                    dict,
                    &branches[0],
                    get_single(proof)?,
                    |printer, _, _| Ok(format!("using {} by auto\n", printer.hname(conclusion))),
                );
            }
            "zenon_tuple_eq_mismatch" | "zenon_record_eq_mismatch" => {
                if args.len() != 1 || conclusions.len() != 1 || !branches.is_empty() {
                    return Err(malformed());
                }
                self.line(indent, "show FALSE\n");
                let text = format!("using {} by auto\n", self.hname(&args[0]));
                self.line(indent, &text);
                return Ok(());
            }
            "zenon_tuple_access" | "zenon_tuple_len" | "zenon_record_domain" => {
                let hypothesis = match branches {
                    [branch] if branch.len() == 1 => &branch[0],
                    _ => return Err(malformed()),
                };
                if args.len() != 3 || conclusions.len() != 1 {
                    return Err(malformed());
                }
                let subproof = get_single(proof)?;
                let equation = self.equal(&args[1], &args[2]);
                let text = format!(
                    "have {}: \"{}\"",
                    self.hname(&equation),
                    self.expr(dict, &equation)?
                );
                self.line(indent, &text);
                let after_equation = self.print_is(dict, &equation)?;
                self.line(indent, "by auto\n");
                let text = format!(
                    "have {}: \"{}\"",
                    self.hname(hypothesis),
                    self.expr(after_equation, hypothesis)?
                );
                self.line(indent, &text);
                let next = self.print_is(after_equation, hypothesis)?;
                let conclusion_name = self.hname(&conclusions[0]);
                let equation_name = self.hname(&equation);
                let text = format!(
                    "by (rule subst [where P=\"{}\", OF {equation_name} {conclusion_name}])\n",
                    self.expr(dict, &args[0])?
                );
                self.line(indent, &text);
                return self.print_tree(indent, next, subproof);
            }
            "zenon_record_access" => {
                let hypothesis = match branches {
                    [branch] if branch.len() == 1 => &branch[0],
                    _ => return Err(malformed()),
                };
                if args.len() != 3 || conclusions.len() != 1 {
                    return Err(malformed());
                }
                let old = &args[1];
                let is_application = old.is_app_with_arity("TLA.fapply", 2);
                if !is_application || !old.args[0].is_app("TLA.record") {
                    return Err(malformed());
                }
                let record = &old.args[0];
                let field = &old.args[1];
                let subproof = get_single(proof)?;
                let Some(field_position) = record.args.iter().position(|arg| arg == field) else {
                    return Err(ZenonError::new("Zenon: list_indexq"));
                };
                let position = field_position / 2 + 1;
                let length = record.args.len() / 2;
                let in_domain = exprs.eapp(
                    "TLA.in",
                    &[
                        field.clone(),
                        exprs.eapp("TLA.DOMAIN", std::slice::from_ref(record)),
                    ],
                );
                let equation = self.equal(old, &args[2]);
                let both = exprs.eand(&in_domain, &equation);
                let text = format!(
                    "have {}: \"{}\"",
                    self.hname(&both),
                    self.expr(dict, &both)?
                );
                self.line(indent, &text);
                let after_both = self.print_is(dict, &both)?;
                let text = if position == 1 {
                    "by ((rule zenon_recfield_1)+, rule zenon_recfield_2b)\n".to_string()
                } else {
                    format!(
                        "by ({}rule zenon_recfield_2, ((rule zenon_recfield_3)+)?, rule zenon_recfield_3b, auto)\n",
                        "rule zenon_recfield_1, ".repeat(length.saturating_sub(position))
                    )
                };
                self.line(indent, &text);
                let text = format!(
                    "have {}: \"{}\"",
                    self.hname(&equation),
                    self.expr(after_both, &equation)?
                );
                self.line(indent, &text);
                let after_equation = self.print_is(after_both, &equation)?;
                let text = format!("by (rule conjD2 [OF {}])\n", self.hname(&both));
                self.line(indent, &text);
                let text = format!(
                    "have {}: \"{}\"",
                    self.hname(hypothesis),
                    self.expr(after_equation, hypothesis)?
                );
                self.line(indent, &text);
                let next = self.print_is(after_equation, hypothesis)?;
                let conclusion_name = self.hname(&conclusions[0]);
                let equation_name = self.hname(&equation);
                let text = format!(
                    "by (rule subst [where P=\"{}\", OF {equation_name} {conclusion_name}])\n",
                    self.expr(next, &args[0])?
                );
                self.line(indent, &text);
                return self.print_tree(indent, next, subproof);
            }
            "zenon_in_product" | "zenon_in_recordset" => {
                return self.print_in_product(
                    indent,
                    dict,
                    proof,
                    name,
                    args,
                    conclusions,
                    branches,
                );
            }
            "zenon_notin_product" => {
                if args.len() != 2 || conclusions.len() != 1 {
                    return Err(malformed());
                }
                let after_element = self.print_let(dict, indent, &args[0])?;
                let last =
                    self.print_negated_haves(indent, after_element, branches, &proof.subproofs)?;
                let text = format!("show FALSE using {} ", self.hname(&conclusions[0]));
                self.line(indent, &text);
                let names = self.get_negated_names(branches)?;
                self.write(&names);
                let text = format!("inProductI[where s=\"{}\"] ", self.expr(last, &args[1])?);
                self.write(&text);
                self.write("by auto\n");
                return Ok(());
            }
            "zenon_notin_recordset" => {
                if args.len() != 2 || conclusions.len() != 1 {
                    return Err(malformed());
                }
                let after_element = self.print_let(dict, indent, &args[0])?;
                self.print_negated_haves(indent, after_element, branches, &proof.subproofs)?;
                let text = format!(
                    "show FALSE by (rule notE [OF {}],\n",
                    self.hname(&conclusions[0])
                );
                self.line(indent, &text);
                self.line(
                    indent,
                    &format!(
                        "               rule zenon_inrecordsetI{} [OF ",
                        to_signed(branches.len()) - 2
                    ),
                );
                let names = self.get_negated_names(branches)?;
                self.write(&names);
                self.write("])\n");
                return Ok(());
            }
            "zenon_tuple_notisaseq" | "zenon_record_notisafcn" => {
                if !args.is_empty() || conclusions.len() != 1 || !branches.is_empty() {
                    return Err(malformed());
                }
                let text = format!("show FALSE using {} by auto\n", self.hname(&conclusions[0]));
                self.line(indent, &text);
                return Ok(());
            }
            "zenon_record_neq_match" => {
                self.line(indent, "sorry\n");
                return Ok(());
            }
            "zenon_neq_record" | "zenon_record_neq" => {
                if args.len() != 2 || conclusions.len() != 1 || branches.len() < 2 {
                    return Err(malformed());
                }
                self.line(indent, "sorry\n");
                return Ok(());
            }
            _ => {}
        }
        match branches {
            [] => {
                self.line(indent, "show FALSE\n");
                let text = format!(
                    "by (rule {name} [of {}, OF {}])\n",
                    self.print_args(dict, args)?,
                    self.print_names(conclusions)
                );
                self.line(indent, &text);
                Ok(())
            }
            [branch] => self.print_haves(
                indent,
                dict,
                branch,
                get_single(proof)?,
                |printer, next, position| {
                    Ok(format!(
                        "by (rule {name}_{position} [of {}, OF {}])\n",
                        printer.print_args(next, args)?,
                        printer.print_names(conclusions)
                    ))
                },
            ),
            _ => {
                self.line(indent, "show FALSE\n");
                let text = format!(
                    "proof (rule {name} [of {}, OF {}])\n",
                    self.print_args(dict, args)?,
                    self.print_names(conclusions)
                );
                self.line(indent, &text);
                self.print_branches(indent, dict, branches, &proof.subproofs)
            }
        }
    }

    #[expect(clippy::too_many_arguments, reason = "the fields of an extension rule")]
    fn print_in_product(
        &mut self,
        indent: usize,
        dict: usize,
        proof: &LlProof,
        name: &str,
        args: &[Expr],
        conclusions: &[Expr],
        branches: &[Vec<Expr>],
    ) -> Result<(), ZenonError> {
        let exprs = self.exprs;
        let malformed = || ZenonError::new(format!("Zenon: a malformed {name} rule"));
        let hypotheses = branches.first().map_or(&[][..], Vec::as_slice);
        if args.len() != 2 || conclusions.len() != 1 || branches.len() != 1 || hypotheses.len() < 2
        {
            return Err(malformed());
        }
        let subproof = get_single(proof)?;
        let conclusion = &conclusions[0];
        let element = &args[0];
        let set = &args[1];
        let is_product = name == "zenon_in_product";
        let after_element = self.print_let(dict, indent, element)?;
        let after_set = if is_product {
            self.print_let(after_element, indent, set)?
        } else {
            after_element
        };
        for formula in &hypotheses[..2] {
            if !subproof.conclusions.contains(formula) {
                continue;
            }
            let conclusion_name = self.hname(conclusion);
            let text = format!(
                "have {}: \"{}\" using {conclusion_name} by auto\n",
                self.hname(formula),
                self.expr(after_set, formula)?
            );
            self.line(indent, &text);
        }
        let one = exprs.eapp("TLA.fapply", &[exprs.evar("TLA.Succ"), exprs.evar("0")]);
        let succ =
            |number: &Expr| exprs.eapp("TLA.fapply", &[exprs.evar("TLA.Succ"), number.clone()]);
        if is_product {
            let is_sequence = exprs.eapp("TLA.isASeq", std::slice::from_ref(set));
            let text = format!(
                "have {}: \"{}\" by auto\n",
                self.hname(&is_sequence),
                self.expr(after_set, &is_sequence)?
            );
            self.line(indent, &text);
            let mut current = after_set;
            let mut index = one.clone();
            for formula in &hypotheses[2..] {
                if !subproof.conclusions.contains(formula) {
                    index = succ(&index);
                    continue;
                }
                let in_length = exprs.eapp(
                    "TLA.in",
                    &[
                        index.clone(),
                        exprs.eapp(
                            "arith.natrange",
                            &[
                                one.clone(),
                                exprs.eapp("TLA.Len", std::slice::from_ref(set)),
                            ],
                        ),
                    ],
                );
                let text = format!(
                    "have {}: \"{}\" by auto\n",
                    self.hname(&in_length),
                    self.expr(current, &in_length)?
                );
                self.line(indent, &text);
                let component = exprs.eapp(
                    "TLA.in",
                    &[
                        exprs.eapp("TLA.fapply", &[element.clone(), index.clone()]),
                        exprs.eapp("TLA.fapply", &[set.clone(), index.clone()]),
                    ],
                );
                let text = format!(
                    "have {}: \"{}\"",
                    self.hname(&component),
                    self.expr(current, &component)?
                );
                self.line(indent, &text);
                let after_component = self.print_is(current, &component)?;
                let in_length_name = self.hname(&in_length);
                let is_sequence_name = self.hname(&is_sequence);
                let text = format!(
                    "by (rule zenon_in_product_i [OF {} {is_sequence_name} {in_length_name}])\n",
                    self.hname(conclusion)
                );
                self.line(indent, &text);
                let text = format!(
                    "have {}: \"{}\"",
                    self.hname(formula),
                    self.expr(after_component, formula)?
                );
                self.line(indent, &text);
                let after_formula = self.print_is(after_component, formula)?;
                let text = format!("using {} by auto\n", self.hname(&component));
                self.line(indent, &text);
                current = after_formula;
                index = succ(&index);
            }
            return self.print_tree(indent, current, subproof);
        }
        if !set.is_app("TLA.recordset") {
            return Err(malformed());
        }
        let domains = exprs.eapp(
            "TLA.tuple",
            &get_pairs(&set.args)
                .map(|pair| pair.0.clone())
                .collect::<Vec<_>>(),
        );
        let ranges = exprs.eapp(
            "TLA.tuple",
            &get_pairs(&set.args)
                .map(|pair| pair.1.clone())
                .collect::<Vec<_>>(),
        );
        let after_domains = self.print_let(after_set, indent, &domains)?;
        let after_ranges = self.print_let(after_domains, indent, &ranges)?;
        let mut current = after_ranges;
        let mut index = one;
        for formula in &hypotheses[2..] {
            if !subproof.conclusions.contains(formula) {
                index = succ(&index);
                continue;
            }
            let in_domain = exprs.eapp(
                "TLA.in",
                &[
                    index.clone(),
                    exprs.eapp("TLA.DOMAIN", std::slice::from_ref(&domains)),
                ],
            );
            let text = format!(
                "have {}: \"{}\" by auto\n",
                self.hname(&in_domain),
                self.expr(current, &in_domain)?
            );
            self.line(indent, &text);
            let component = exprs.eapp(
                "TLA.in",
                &[
                    exprs.eapp(
                        "TLA.fapply",
                        &[
                            element.clone(),
                            exprs.eapp("TLA.fapply", &[domains.clone(), index.clone()]),
                        ],
                    ),
                    exprs.eapp("TLA.fapply", &[ranges.clone(), index.clone()]),
                ],
            );
            let text = format!(
                "have {}: \"{}\"",
                self.hname(&component),
                self.expr(current, &component)?
            );
            self.line(indent, &text);
            let after_component = self.print_is(current, &component)?;
            let in_domain_name = self.hname(&in_domain);
            let text = format!(
                "by (rule zenon_in_recordset_field [OF {} {in_domain_name}])\n",
                self.hname(conclusion)
            );
            self.line(indent, &text);
            let text = format!(
                "have {}: \"{}\"",
                self.hname(formula),
                self.expr(after_component, formula)?
            );
            self.line(indent, &text);
            let after_formula = self.print_is(after_component, formula)?;
            let text = format!("using {} by auto\n", self.hname(&component));
            self.line(indent, &text);
            current = after_formula;
            index = succ(&index);
        }
        self.print_tree(indent, current, subproof)
    }

    fn print_lemma(&mut self, indent: usize, dict: usize, lemma: &Lemma) -> Result<(), ZenonError> {
        if get_limit_failure(self.limits).is_some() {
            return Ok(());
        }
        let params = lemma
            .params
            .iter()
            .filter_map(|param| match param.1.kind {
                Kind::Var => Some(Ok(param.1.symbol.clone())),
                Kind::Tau => None,
                _ => Some(Err(ZenonError::new(
                    "Zenon: a lemma parameter that is neither a variable nor a tau",
                ))),
            })
            .collect::<Result<Vec<_>, _>>()?;
        let conclusions = &lemma.proof.conclusions;
        self.line(indent, &format!("have {}: \"", lemma.name));
        let text: String = params.iter().map(|param| format!("!!{param}. ")).collect();
        self.write(&text);
        let text = conclusions
            .iter()
            .map(|conclusion| Ok(format!("{} ==> ", self.expr(dict, conclusion)?)))
            .collect::<Result<String, ZenonError>>()?;
        self.write(&text);
        self.write("FALSE\"");
        let mut patterns = Vec::new();
        let mut after_patterns = dict;
        for conclusion in conclusions {
            let pattern = self.make_pattern(after_patterns, conclusion);
            patterns.push(pattern.0);
            after_patterns = pattern.1;
        }
        if patterns.iter().all(|pattern| pattern == "_") {
            self.write("\n");
        } else {
            let text: String = patterns
                .iter()
                .map(|pattern| format!("{pattern} ==> "))
                .collect();
            self.write(&format!(" (is \"{text}FALSE\")\n"));
        }
        self.line(indent, "proof -\n");
        for param in &params {
            self.line(increment(indent), &format!("fix \"{param}\"\n"));
        }
        let sequent = self.print_sequent(increment(indent), after_patterns, conclusions)?;
        self.print_tree(increment(indent), sequent, &lemma.proof)?;
        self.line(indent, "qed\n");
        Ok(())
    }

    /// Zenon's p_theorem.
    fn print_theorem(&mut self, lemmas: &[Lemma], phrases: &[Phrase]) -> Result<(), ZenonError> {
        let exprs = self.exprs;
        let theorem = lemmas.last();
        let hypotheses: Vec<(&str, &Expr)> = phrases
            .iter()
            .filter_map(|phrase| match phrase {
                Phrase::Hyp { name, formula, .. } => Some((name.as_str(), formula)),
                Phrase::Def(_) => None,
            })
            .collect();
        let negated_goal = hypotheses
            .iter()
            .find(|phrase| phrase.0 == GOAL_NAME)
            .map_or_else(|| exprs.enot(&efalse()), |phrase| phrase.1.clone());
        if negated_goal.kind != Kind::Not {
            return Err(ZenonError::new("Zenon: a goal that isn't negated"));
        }
        let goal = &negated_goal.args[0];
        // TypeScript reads the theorem's proof here, and throws a TypeError without one.
        let Some(theorem) = theorem else {
            return Err(ZenonError::new("Zenon: a proof without a theorem"));
        };
        let assumptions: Vec<&Expr> = theorem
            .proof
            .conclusions
            .iter()
            .filter(|formula| **formula != negated_goal)
            .collect();
        let mut real_names: HashMap<usize, &str> = HashMap::new();
        for phrase in &hypotheses {
            if !phrase.0.is_empty() {
                real_names.insert(self.get_number(phrase.1), phrase.0);
            }
        }
        self.write("(* PROOF-FOUND *)\n(* BEGIN-PROOF *)\n");
        self.line(0, "proof (rule zenon_nnpp)\n");
        let mut nary_rules: Vec<(String, String)> = Vec::new();
        std::iter::once(theorem)
            .chain(&lemmas[..lemmas.len() - 1])
            .try_for_each(|lemma| collect_nary_rules(&mut nary_rules, &lemma.proof))?;
        nary_rules.sort_by(|left, right| compare_utf16(&left.0, &right.0));
        for rule in &nary_rules {
            self.write(&rule.1);
        }
        let indent = increment(0);
        let mut dict = 0;
        for formula in assumptions {
            let text = format!(
                "have {}:\"{}\"",
                self.hname(formula),
                self.expr(dict, formula)?
            );
            self.line(indent, &text);
            let next = self.print_is(dict, formula)?;
            let text = match real_names.get(&self.get_number(formula)) {
                None => "by fact\n".to_string(),
                Some(real_name) => format!("using {real_name} by blast\n"),
            };
            self.line(indent, &text);
            dict = next;
        }
        for lemma in &lemmas[..lemmas.len() - 1] {
            self.print_lemma(indent, dict, lemma)?;
        }
        let sequent = self.print_sequent(indent, dict, &[exprs.enot(goal)])?;
        self.print_tree(indent, sequent, &theorem.proof)?;
        self.line(0, "qed\n");
        self.write("(* END-PROOF *)\n");
        Ok(())
    }
}

fn get_negation(branch: &[Expr]) -> Result<&Expr, ZenonError> {
    match branch {
        [negation] if negation.kind == Kind::Not => Ok(negation),
        _ => Err(ZenonError::new("Zenon: a branch that isn't one negation")),
    }
}

/// The lemmas for CASE rules and record sets that Zenon.thy lacks, by their sort key. A key set
/// twice keeps its first place, as a JavaScript `Map` does.
fn collect_nary_rules(rules: &mut Vec<(String, String)>, tree: &LlProof) -> Result<(), ZenonError> {
    let mut set = |key: String, value: String| match rules.iter_mut().find(|rule| rule.0 == key) {
        Some(rule) => rule.1 = value,
        None => rules.push((key, value)),
    };
    if let LlRule::Extension { name, branches, .. } = &tree.rule {
        if name == "zenon_case" {
            let arity = to_signed(branches.len()) - 1;
            let is_other = get_last_branch_is_other(branches)?;
            if arity > 5 {
                set(
                    format!("0 {arity:0>9} {}", u8::from(is_other)),
                    print_case_lemma(arity, is_other)?,
                );
            }
        }
        if name == "zenon_notin_recordset" {
            let arity = to_signed(branches.len()) - 2;
            if arity > 7 {
                set(format!("1 {arity:0>9}"), print_record_lemma(arity)?);
            }
        }
    }
    tree.subproofs
        .iter()
        .try_for_each(|subproof| collect_nary_rules(rules, subproof))
}

#[cfg(test)]
mod tests {
    //! Each fixture in testdata/isar holds what the TypeScript printer printed from for a .znn file
    //! of tests/fixtures/zenon: the expressions the run had created, in the order it created them,
    //! the lemmas after `optimise`, the order the translation numbered formulas in, the hypotheses
    //! and the fresh-name counter; and the Isar text the TypeScript printed.

    use std::cell::RefCell;
    use std::collections::{HashMap, HashSet};
    use std::rc::Rc;

    use prove_decide::Limits;

    use super::{IsarContext, print_lemmas};
    use crate::eqrel::Relations;
    use crate::expr::{Expr, Expressions, Kind, VAR_PREFIX, efalse, etrue};
    use crate::llproof::{Lemma, LlProof, LlRule};
    use crate::parse::Phrase;

    fn unescape(text: &str) -> String {
        let mut result = String::new();
        let mut chars = text.chars();
        while let Some(char) = chars.next() {
            if char != '\\' {
                result.push(char);
                continue;
            }
            match chars.next() {
                Some('t') => result.push('\t'),
                Some('n') => result.push('\n'),
                Some('r') => result.push('\r'),
                Some(other) => result.push(other),
                None => {}
            }
        }
        result
    }

    fn get_kind(name: &str) -> Kind {
        [
            Kind::Var,
            Kind::Meta,
            Kind::App,
            Kind::Not,
            Kind::And,
            Kind::Or,
            Kind::Imply,
            Kind::Equiv,
            Kind::All,
            Kind::Ex,
            Kind::Tau,
            Kind::Lam,
        ]
        .into_iter()
        .find(|kind| kind.name() == name)
        .unwrap_or_else(|| panic!("no kind {name}"))
    }

    struct Fixture {
        exprs: Expressions,
        built: HashMap<usize, Expr>,
    }

    impl Fixture {
        fn get(&self, id: &str) -> Expr {
            let id: usize = id.parse().unwrap();
            match id {
                0 => etrue(),
                1 => efalse(),
                _ => self.built[&id].clone(),
            }
        }

        fn get_list(&self, ids: &str) -> Vec<Expr> {
            ids.split(',')
                .filter(|id| !id.is_empty())
                .map(|id| self.get(id))
                .collect()
        }

        fn build(&mut self, id: &str, kind: &str, symbol: &str, args: &str) {
            let args = self.get_list(args);
            let exprs = &self.exprs;
            let expression = match get_kind(kind) {
                Kind::Var => exprs.evar(symbol),
                Kind::Meta => exprs.emeta(&args[0]),
                Kind::App => exprs.eapp(symbol, &args),
                Kind::Not => exprs.enot(&args[0]),
                kind if kind.is_binary() => exprs.binary(kind, &args[0], &args[1]),
                kind => exprs.binder(kind, &args[0], symbol, &args[1]),
            };
            self.built.insert(id.parse().unwrap(), expression);
        }

        fn read_node<'a>(&self, lines: &mut impl Iterator<Item = &'a str>) -> Rc<LlProof> {
            let line = lines.next().unwrap();
            let fields: Vec<&str> = line.split('\t').collect();
            assert_eq!(fields[0], "node");
            let get = |position: usize| self.get(fields[position]);
            let get_connective = || get_kind(fields[4]);
            let rule = match fields[3] {
                "false" => LlRule::False,
                "nottrue" => LlRule::NotTrue,
                "axiom" => LlRule::Axiom(get(4)),
                "cut" => LlRule::Cut(get(4)),
                "notnot" => LlRule::NotNot(get(4)),
                "noteq" => LlRule::NotEq(get(4)),
                "eqsym" => LlRule::EqSym {
                    left: get(4),
                    right: get(5),
                },
                "notequal" => LlRule::NotEqual {
                    left: get(4),
                    right: get(5),
                },
                "connect" => LlRule::Connect {
                    connective: get_connective(),
                    left: get(5),
                    right: get(6),
                },
                "notconnect" => LlRule::NotConnect {
                    connective: get_connective(),
                    left: get(5),
                    right: get(6),
                },
                "ex" => LlRule::Ex {
                    quantified: get(4),
                    term: get(5),
                },
                "all" => LlRule::All {
                    quantified: get(4),
                    term: get(5),
                },
                "notex" => LlRule::NotEx {
                    quantified: get(4),
                    term: get(5),
                },
                "notall" => LlRule::NotAll {
                    quantified: get(4),
                    term: get(5),
                },
                "pnotp" => LlRule::PNotP {
                    positive: get(4),
                    negative: get(5),
                },
                "congruencelr" => LlRule::CongruenceLr {
                    context: get(4),
                    left: get(5),
                    right: get(6),
                },
                "congruencerl" => LlRule::CongruenceRl {
                    context: get(4),
                    left: get(5),
                    right: get(6),
                },
                "definition" => LlRule::Definition {
                    name: unescape(fields[4]),
                    folded: get(5),
                    unfolded: get(6),
                },
                "extension" => LlRule::Extension {
                    name: unescape(fields[4]),
                    args: self.get_list(fields[5]),
                    conclusions: self.get_list(fields[6]),
                    branches: if fields[7].is_empty() {
                        Vec::new()
                    } else {
                        fields[7]
                            .split(';')
                            .map(|branch| self.get_list(branch))
                            .collect()
                    },
                },
                "lemma" => LlRule::Lemma {
                    name: unescape(fields[4]),
                    args: self.get_list(fields[5]),
                },
                other => panic!("no rule {other}"),
            };
            let count: usize = fields[1].parse().unwrap();
            Rc::new(LlProof {
                conclusions: self.get_list(fields[2]),
                rule,
                subproofs: (0..count).map(|_| self.read_node(lines)).collect(),
            })
        }
    }

    /// What the port prints for a fixture, the steps it took, and the steps the TypeScript took.
    fn print_fixture(dump: &str, step_limit: Option<u64>) -> (Option<String>, u64, u64) {
        let mut fixture = Fixture {
            exprs: Expressions::new(),
            built: HashMap::new(),
        };
        let mut lines = dump.lines();
        let mut counter = "e";
        let mut expected_steps = 0;
        let mut lemmas = Vec::new();
        let mut numbering = Vec::new();
        let mut phrases = Vec::new();
        while let Some(line) = lines.next() {
            let fields: Vec<&str> = line.split('\t').collect();
            match fields[0] {
                "counter" => counter = fields[1],
                "steps" => expected_steps = fields[1].parse().unwrap(),
                "expr" => fixture.build(fields[1], fields[2], &unescape(fields[3]), fields[4]),
                "lemma" => {
                    let params = fields[2]
                        .split(',')
                        .filter(|param| !param.is_empty())
                        .map(|param| {
                            let (name, id) = param.rsplit_once('=').unwrap();
                            (unescape(name), fixture.get(id))
                        })
                        .collect();
                    let proof = fixture.read_node(&mut lines);
                    lemmas.push(Lemma {
                        name: unescape(fields[1]),
                        params,
                        proof,
                    });
                }
                "numbers" => numbering = fixture.get_list(fields[1]),
                "hyp" => phrases.push(Phrase::Hyp {
                    name: unescape(fields[1]),
                    formula: fixture.get(fields[2]),
                    goalness: fields[3].parse().unwrap(),
                }),
                other => panic!("unexpected line {other}"),
            }
        }
        if counter != "e" {
            let last = format!("{VAR_PREFIX}{counter}");
            while *fixture.exprs.new_var().symbol != *last {}
        }
        let numbers: RefCell<HashMap<Expr, usize>> = RefCell::default();
        let get_number = |expression: &Expr| {
            let mut numbers = numbers.borrow_mut();
            let next = numbers.len();
            *numbers.entry(expression.clone()).or_insert(next)
        };
        for expression in &numbering {
            get_number(expression);
        }
        let limits = Limits::new(f64::INFINITY, step_limit, None);
        let printed = print_lemmas(
            &lemmas,
            &get_number,
            IsarContext {
                exprs: &fixture.exprs,
                phrases: &phrases,
                shared_proofs: &HashSet::new(),
                relations: &Relations::new(),
                limits: &limits,
            },
        )
        .unwrap();
        (printed, limits.steps(), expected_steps)
    }

    #[test]
    fn prints_what_the_typescript_prints() {
        let directory = concat!(env!("CARGO_MANIFEST_DIR"), "/testdata/isar");
        let mut names: Vec<String> = std::fs::read_dir(directory)
            .unwrap()
            .map(|entry| entry.unwrap().file_name().to_string_lossy().into_owned())
            .filter_map(|name| name.strip_suffix(".dump").map(str::to_string))
            .collect();
        names.sort();
        assert!(!names.is_empty());
        for name in names {
            let dump = std::fs::read_to_string(format!("{directory}/{name}.dump")).unwrap();
            let expected = std::fs::read_to_string(format!("{directory}/{name}.isar")).unwrap();
            let (printed, steps, expected_steps) = print_fixture(&dump, None);
            assert!(
                printed.as_deref() == Some(expected.as_str()),
                "{name} prints differently"
            );
            assert_eq!(steps, expected_steps, "{name} takes other steps");
        }
    }

    #[test]
    fn stops_at_the_step_limit() {
        let directory = concat!(env!("CARGO_MANIFEST_DIR"), "/testdata/isar");
        let dump = std::fs::read_to_string(format!("{directory}/case.dump")).unwrap();
        let expected_steps = print_fixture(&dump, None).2;
        assert!(print_fixture(&dump, Some(expected_steps)).0.is_some());
        assert!(print_fixture(&dump, Some(expected_steps - 1)).0.is_none());
    }

    #[test]
    fn refuses_a_proof_without_a_theorem() {
        let limits = Limits::new(f64::INFINITY, None, None);
        let printed = print_lemmas(
            &[],
            &|_| 0,
            IsarContext {
                exprs: &Expressions::new(),
                phrases: &[],
                shared_proofs: &HashSet::new(),
                relations: &Relations::new(),
                limits: &limits,
            },
        );
        assert!(printed.is_err());
    }
}
