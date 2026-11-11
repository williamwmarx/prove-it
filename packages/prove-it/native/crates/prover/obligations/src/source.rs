//! Converts the tla-front AST into tlapm's parse trees: expressions name operators opaquely until
//! anonymization resolves them, and proof steps get tlapm's levels and anonymous step numbers.
//! A port of `src/obligations/source.ts`, on tla-front's AST of `parse_tlapm_module`.

use std::rc::Rc;

use tla_front::ast;

use crate::errors::{ObligationError, Result};
use crate::expression::{
    Bound, BoundDomain, Builtin, Bullet, CaseArm, Defn, DefnCore, ExceptPoint, ExceptSpec, Expr,
    ExprCore, ExprProps, Fairness, Field, Hyp, HypCore, HypNode, InstanceDefinition, Level, Locus,
    Modal, Param, ParenForm, Quantifier, Selector, Sequent, Substitution, Time, Visibility,
    WhereDefined, at, at_expr, expr, get_fact, located,
};
use crate::module::{Declaration, ModuleUnit, ModuleUnitCore, Mule, MutateMode};
use crate::operators::{Fixity, lookup_operator};
use crate::pragma::{OldMethod, Position, find_pragma, read_new_method, read_old_method};
use crate::proof::{
    Counter, Omission, Proof, ProofCore, ProofProps, QedStep, Step, StepCore, StepNumber, Usable,
    UseDef, UseDefCore, get_unique,
};
use crate::regroup::regroup;
use crate::tuples::{
    TuplyBinder, TuplyBound, expand_choose, expand_fcn, expand_quant, expand_set_of, get_unbounded,
};

fn get_builtin(name: &str) -> Option<Builtin> {
    Some(match name {
        "=>" => Builtin::Implies,
        "<=>" => Builtin::Equiv,
        "/\\" => Builtin::Conj,
        "\\/" => Builtin::Disj,
        "~" => Builtin::Neg,
        "=" => Builtin::Eq,
        "#" => Builtin::Neq,
        "SUBSET" => Builtin::SUBSET,
        "UNION" => Builtin::UNION,
        "DOMAIN" => Builtin::DOMAIN,
        "\\subseteq" => Builtin::Subseteq,
        "\\in" => Builtin::Mem,
        "\\notin" => Builtin::Notmem,
        "\\" => Builtin::Setminus,
        "\\cap" => Builtin::Cap,
        "\\cup" => Builtin::Cup,
        "'" => Builtin::Prime,
        "~>" => Builtin::Leadsto,
        "ENABLED" => Builtin::ENABLED,
        "UNCHANGED" => Builtin::UNCHANGED,
        "\\cdot" => Builtin::Cdot,
        "-+->" => Builtin::Actplus,
        "[]" => Builtin::BoxTrue,
        "<>" => Builtin::Diamond,
        "TRUE" => Builtin::TRUE,
        "FALSE" => Builtin::FALSE,
        "BOOLEAN" => Builtin::BOOLEAN,
        "STRING" => Builtin::STRING,
        _ => return None,
    })
}

fn get_canonical_name(name: &str) -> String {
    lookup_operator(name).name
}

/// A step token's level (digits, `*` or `+`) and label, as `/^<(\d+|\*|\+)>([A-Za-z0-9_]*)\.*$/`
/// matches it.
struct StepToken {
    level: String,
    label: String,
}

fn match_step_token(token: &str) -> Option<StepToken> {
    let rest = token.strip_prefix('<')?;
    let close = rest.find('>')?;
    let level = &rest[..close];
    let is_level = level == "*"
        || level == "+"
        || (!level.is_empty() && level.bytes().all(|byte| byte.is_ascii_digit()));
    if !is_level {
        return None;
    }
    let after = &rest[close + 1..];
    let label_end = after
        .find(|character: char| !(character.is_ascii_alphanumeric() || character == '_'))
        .unwrap_or(after.len());
    if !after[label_end..].bytes().all(|byte| byte == b'.') {
        return None;
    }
    Some(StepToken {
        level: level.to_owned(),
        label: after[..label_end].to_owned(),
    })
}

fn merge_loci(left: Option<&Locus>, right: Option<&Locus>) -> Option<Locus> {
    let (Some(left), Some(right)) = (left, right) else {
        return left.or(right).cloned();
    };
    let is_left_first = left.start_line < right.start_line
        || (left.start_line == right.start_line && left.start_column <= right.start_column);
    let is_left_last = left.end_line > right.end_line
        || (left.end_line == right.end_line && left.end_column >= right.end_column);
    Some(Locus {
        file: left.file.clone(),
        start_line: if is_left_first {
            left.start_line
        } else {
            right.start_line
        },
        start_column: if is_left_first {
            left.start_column
        } else {
            right.start_column
        },
        end_line: if is_left_last {
            left.end_line
        } else {
            right.end_line
        },
        end_column: if is_left_last {
            left.end_column
        } else {
            right.end_column
        },
    })
}

const TUPLY_FAILURE: &str = "use instead the class`E_visit.iter_concrete`";

fn get_tuple_error() -> ObligationError {
    ObligationError::proof_failure("Unexpected tuple declaration", TUPLY_FAILURE)
}

fn is_ditto(bounds: &[ast::Bound], index: usize) -> bool {
    index > 0 && Rc::ptr_eq(&bounds[index - 1].set, &bounds[index].set)
}

fn has_tuple(bounds: &[ast::Bound]) -> bool {
    bounds
        .iter()
        .any(|bound| matches!(bound.pattern, ast::BoundPattern::Tuple { .. }))
}

fn get_names(names: &[ast::Name]) -> Vec<String> {
    names.iter().map(ToString::to_string).collect()
}

/// A 1-based line or column as a 0-based index; 0 becomes an index no line has, as -1 is in the
/// TypeScript.
fn get_index(position: u32) -> usize {
    (position as usize).wrapping_sub(1)
}

/// `lines[line].indexOf(needle, from)` on UTF-16 code units.
fn find_units(line: &[u16], needle: &[u16], from: usize) -> Option<usize> {
    (from..=line.len().checked_sub(needle.len())?).find(|&start| line[start..].starts_with(needle))
}

fn get_utf16_length(text: &str) -> u32 {
    text.encode_utf16().count() as u32
}

/// The string a literal `"..."` that ends `text` holds as written, as
/// `/"((?:[^"\\]|\\.)*)"$/.exec(text)?.[1]` finds it.
fn get_written_string(text: &[u16]) -> Option<String> {
    let is_quote = |unit: u16| unit == u16::from(b'"');
    let is_backslash = |unit: u16| unit == u16::from(b'\\');
    let is_line_terminator = |unit: u16| matches!(unit, 0x0a | 0x0d | 0x2028 | 0x2029);
    let last = text.len().checked_sub(1)?;
    (0..last)
        .filter(|&start| is_quote(text[start]))
        .find_map(|start| {
            let mut index = start + 1;
            while index < text.len() {
                let unit = text[index];
                if is_quote(unit) {
                    return (index == last)
                        .then(|| String::from_utf16_lossy(&text[start + 1..last]));
                }
                if is_backslash(unit) {
                    match text.get(index + 1) {
                        Some(&next) if !is_line_terminator(next) => index += 2,
                        _ => return None,
                    }
                } else {
                    index += 1;
                }
            }
            None
        })
}

fn get_level(level: ast::SymbolLevel) -> Level {
    match level {
        ast::SymbolLevel::Constant | ast::SymbolLevel::Variable => Level::Constant,
        ast::SymbolLevel::State => Level::State,
        ast::SymbolLevel::Action => Level::Action,
        ast::SymbolLevel::Temporal => Level::Temporal,
    }
}

fn get_quantifier(quantifier: ast::Quantifier) -> Quantifier {
    match quantifier {
        ast::Quantifier::Forall => Quantifier::Forall,
        ast::Quantifier::Exists => Quantifier::Exists,
    }
}

fn get_fact_location(fact: &ast::Fact) -> &ast::Location {
    match fact {
        ast::Fact::Expression(expression) => &expression.location,
        ast::Fact::Module { location, .. } => location,
    }
}

fn get_statement_range(statement: &ast::Statement) -> Option<&ast::SourceRange> {
    match statement {
        ast::Statement::Expression(expression) => expression.location.range.as_ref(),
        ast::Statement::AssumeProve(assume_prove) => assume_prove.location.range.as_ref(),
    }
}

fn get_definition_location(definition: &ast::DefinitionUnit) -> &ast::Location {
    match definition {
        ast::DefinitionUnit::Definition(definition) => &definition.location,
        ast::DefinitionUnit::Instance(instance) => &instance.location,
    }
}

fn props(location: Option<Locus>) -> ExprProps {
    ExprProps {
        location,
        is_atomic: false,
    }
}

fn proof_props(location: Option<Locus>, step: Option<StepNumber>) -> ProofProps {
    ProofProps {
        location,
        step,
        ..ProofProps::default()
    }
}

/// `createSource`: the conversion of one file's module.
pub struct Source {
    file: Rc<str>,
    lines: Vec<Vec<u16>>,
    counter: Rc<Counter>,
    is_expanding_tuples: bool,
}

pub fn create_source(
    file: &str,
    text: &str,
    counter: Rc<Counter>,
    is_expanding_tuples: bool,
) -> Source {
    Source {
        file: Rc::from(file),
        lines: text
            .split('\n')
            .map(|line| line.encode_utf16().collect())
            .collect(),
        counter,
        is_expanding_tuples,
    }
}

impl Source {
    fn get_range_locus(&self, range: &ast::SourceRange) -> Locus {
        Locus {
            file: self.file.clone(),
            start_line: range.start.line,
            start_column: range.start.column,
            end_line: range.end.line,
            end_column: range.end.column + 1,
        }
    }

    fn with_pragma(&self, locus: Locus) -> Locus {
        let Some(open) = find_pragma(
            &self.lines,
            Position {
                line: get_index(locus.end_line),
                column: get_index(locus.end_column),
            },
        ) else {
            return locus;
        };
        let needle: Vec<u16> = "}*)".encode_utf16().collect();
        for index in open.line..self.lines.len() {
            let from = if index == open.line { open.column } else { 0 };
            if let Some(close) = find_units(&self.lines[index], &needle, from) {
                return Locus {
                    end_line: index as u32 + 1,
                    end_column: close as u32 + 4,
                    ..locus
                };
            }
        }
        locus
    }

    fn get_method(&self, range: Option<&ast::SourceRange>) -> Result<Option<OldMethod>> {
        let Some(range) = range else {
            return Ok(None);
        };
        read_old_method(
            &self.lines,
            Position {
                line: get_index(range.end.line),
                column: range.end.column as usize,
            },
        )
    }

    /// A method pragma belongs to the node it follows, whose locus then takes it in.
    fn with_method(&self, range: &ast::SourceRange) -> Result<ProofProps> {
        let method = self.get_method(Some(range))?;
        let location = self.get_range_locus(range);
        Ok(match method {
            Some(method) => ProofProps {
                location: Some(self.with_pragma(location)),
                method: Some(method),
                ..ProofProps::default()
            },
            None => proof_props(Some(location), None),
        })
    }

    /// Module.Parser's with_meth, which wraps the expression a method follows.
    fn with_expression_method(
        &self,
        expression: Expr,
        range: Option<&ast::SourceRange>,
    ) -> Result<Expr> {
        Ok(match self.get_method(range)? {
            Some(method) => at(
                ExprCore::With {
                    expression: expression.clone(),
                    method,
                },
                &expression,
            ),
            None => expression,
        })
    }

    fn get_point_locus(&self, location: &ast::Location, length: u32) -> Locus {
        Locus {
            file: self.file.clone(),
            start_line: location.line,
            start_column: location.column,
            end_line: location.line,
            end_column: location.column + length,
        }
    }

    fn get_locus(&self, location: &ast::Location) -> Locus {
        match &location.range {
            Some(range) => self.get_range_locus(range),
            None => self.get_point_locus(location, 1),
        }
    }

    fn convert_operator(&self, name: &str, location: Option<Locus>) -> Expr {
        let canonical = get_canonical_name(name);
        let core = match get_builtin(&canonical) {
            Some(builtin) => ExprCore::Internal { builtin },
            None => ExprCore::Opaque { name: canonical },
        };
        located(core, location)
    }

    /// A name with ! selects through instances, which anonymization resolves by joining the names.
    fn convert_name(
        &self,
        name: &str,
        args: Vec<Expr>,
        location: &Locus,
        argument_counts: Option<&[usize]>,
    ) -> Expr {
        let at_location = |core: ExprCore| located(core, Some(location.clone()));
        if name.starts_with('<') {
            let operator = at_location(ExprCore::Opaque {
                name: name.to_owned(),
            });
            return at_location(ExprCore::Bang {
                expression: operator,
                selectors: Vec::new(),
            });
        }
        if let Some(builtin) = get_builtin(name)
            && args.is_empty()
        {
            return at_location(ExprCore::Internal { builtin });
        }
        let names: Vec<&str> = name.split('!').collect();
        if names.len() == 1 {
            let operator = at_location(ExprCore::Opaque {
                name: name.to_owned(),
            });
            return if args.is_empty() {
                operator
            } else {
                at_location(ExprCore::Apply { operator, args })
            };
        }
        let counts: Vec<usize> = argument_counts.map_or_else(
            || {
                (0..names.len())
                    .map(|index| {
                        if index == names.len() - 1 {
                            args.len()
                        } else {
                            0
                        }
                    })
                    .collect()
            },
            <[usize]>::to_vec,
        );
        let get_args = |index: usize| -> Vec<Expr> {
            let (Some(&count), Some(offset)) = (
                counts.get(index),
                counts
                    .get(..index)
                    .map(|before| before.iter().sum::<usize>()),
            ) else {
                return Vec::new();
            };
            let start = offset.min(args.len());
            let end = (offset + count).min(args.len());
            args[start..end].to_vec()
        };
        let head = at_location(ExprCore::Opaque {
            name: names[0].to_owned(),
        });
        at_location(ExprCore::Bang {
            expression: if counts.first() == Some(&0) {
                head
            } else {
                at_location(ExprCore::Apply {
                    operator: head,
                    args: get_args(0),
                })
            },
            selectors: names[1..]
                .iter()
                .enumerate()
                .map(|(index, label)| Selector::Label {
                    label: get_canonical_name(label),
                    args: get_args(index + 1),
                })
                .collect(),
        })
    }

    fn convert_bounds(&self, bounds: &[ast::Bound], is_except: bool) -> Result<Vec<Bound>> {
        bounds
            .iter()
            .enumerate()
            .map(|(index, bound)| {
                let ast::BoundPattern::Name { name, .. } = &bound.pattern else {
                    return Err(get_tuple_error());
                };
                Ok(Bound {
                    name: name.to_string(),
                    level: Level::Constant,
                    domain: if is_ditto(bounds, index) {
                        BoundDomain::Ditto
                    } else {
                        BoundDomain::Domain(self.convert_expression(&bound.set, is_except)?)
                    },
                })
            })
            .collect()
    }

    fn get_tuply_bounds(&self, bounds: &[ast::Bound], is_except: bool) -> Result<Vec<TuplyBound>> {
        bounds
            .iter()
            .enumerate()
            .map(|(index, bound)| {
                let domain = self.convert_expression(&bound.set, is_except)?;
                Ok(match &bound.pattern {
                    ast::BoundPattern::Tuple { names, .. } => TuplyBound::Tuple {
                        names: get_names(names),
                        domain,
                    },
                    ast::BoundPattern::Name { name, .. } => TuplyBound::Name {
                        name: name.to_string(),
                        domain: if is_ditto(bounds, index) {
                            BoundDomain::Ditto
                        } else {
                            BoundDomain::Domain(domain)
                        },
                    },
                })
            })
            .collect()
    }

    fn expand_tuples(&self, expanded: Expr, location: Locus) -> Result<Expr> {
        if !self.is_expanding_tuples {
            return Err(get_tuple_error());
        }
        Ok(at_expr(&expanded, &props(Some(location))))
    }

    fn convert_expressions(&self, expressions: &[ast::Expr], is_except: bool) -> Result<Vec<Expr>> {
        expressions
            .iter()
            .map(|inner| self.convert_expression(inner, is_except))
            .collect()
    }

    fn convert_expression(&self, expression: &ast::Expr, is_except: bool) -> Result<Expr> {
        let location = self.get_locus(&expression.location);
        let recurse = |inner: &ast::Expr| self.convert_expression(inner, is_except);
        let at_location = |core: ExprCore| located(core, Some(location.clone()));
        // tlapm locates an operator application by its operator and operands, and a parenthesized
        // operand by what is inside the parentheses.
        let get_operator_locus = |args: &[Expr], fixity: Fixity| -> Option<Locus> {
            if let [left, right] = args {
                return merge_loci(left.location.as_ref(), right.location.as_ref());
            }
            let [operand] = args else {
                return Some(location.clone());
            };
            let Some(operand_location) = &operand.location else {
                return Some(location.clone());
            };
            match fixity {
                Fixity::Prefix => merge_loci(
                    Some(&Locus {
                        end_line: location.start_line,
                        end_column: location.start_column + 1,
                        ..location.clone()
                    }),
                    Some(operand_location),
                ),
                Fixity::Postfix => merge_loci(
                    Some(&Locus {
                        start_line: location.end_line,
                        start_column: location.end_column - 1,
                        ..location.clone()
                    }),
                    Some(operand_location),
                ),
                _ => Some(location.clone()),
            }
        };
        let apply_builtin = |builtin: Builtin, operand: Expr, fixity: Fixity| {
            let location = get_operator_locus(std::slice::from_ref(&operand), fixity);
            located(
                ExprCore::Apply {
                    operator: expr(ExprCore::Internal { builtin }),
                    args: vec![operand],
                },
                location,
            )
        };
        let modal = |is_box: bool| if is_box { Modal::Box } else { Modal::Dia };
        Ok(match &expression.kind {
            ast::ExpressionKind::Number { text, .. } => at_location(ExprCore::Num {
                integer: text.to_string(),
                fraction: String::new(),
            }),
            ast::ExpressionKind::Decimal { text } => {
                let (integer, fraction) = text.split_once('.').unwrap_or((text, ""));
                let fraction = fraction.split('.').next().unwrap_or_default();
                at_location(ExprCore::Num {
                    integer: integer.to_owned(),
                    fraction: fraction.to_owned(),
                })
            }
            ast::ExpressionKind::String { value } => {
                // tlapm's lexer keeps a string's escapes as written. The location ends at the
                // closing quote.
                let line = self
                    .lines
                    .get(get_index(location.end_line))
                    .map_or(&[][..], Vec::as_slice);
                let end = get_index(location.end_column).min(line.len());
                at_location(ExprCore::String {
                    value: get_written_string(&line[..end]).unwrap_or_else(|| value.to_string()),
                })
            }
            ast::ExpressionKind::Identifier { name, .. } => {
                self.convert_name(name, Vec::new(), &location, None)
            }
            ast::ExpressionKind::Apply {
                operator,
                args,
                argument_counts,
                ..
            } => {
                if args.len() == 2 {
                    let regrouped = regroup(expression);
                    if !Rc::ptr_eq(&regrouped, expression) {
                        return recurse(&regrouped);
                    }
                }
                let args = self.convert_expressions(args, is_except)?;
                let fixity = lookup_operator(operator).fixity;
                if fixity != Fixity::Nonfix {
                    let location = get_operator_locus(&args, fixity);
                    return Ok(located(
                        ExprCore::Apply {
                            operator: self.convert_operator(operator, None),
                            args,
                        },
                        location,
                    ));
                }
                self.convert_name(operator, args, &location, argument_counts.as_deref())
            }
            ast::ExpressionKind::OperatorReference { operator, .. } => {
                self.convert_operator(operator, Some(location))
            }
            ast::ExpressionKind::Lambda { params, body, .. } => at_location(ExprCore::Lambda {
                params: params
                    .iter()
                    .map(|name| Param {
                        name: name.to_string(),
                        shape: 0,
                        location: None,
                    })
                    .collect(),
                body: recurse(body)?,
            }),
            ast::ExpressionKind::Junction {
                is_and,
                operands,
                is_bulleted,
                ..
            } => {
                let items = self.convert_expressions(operands, is_except)?;
                if *is_bulleted {
                    return Ok(at_location(ExprCore::List {
                        bullet: if *is_and { Bullet::And } else { Bullet::Or },
                        items,
                    }));
                }
                let builtin = if *is_and {
                    Builtin::Conj
                } else {
                    Builtin::Disj
                };
                let mut items = items.into_iter();
                let first = items.next().ok_or_else(ObligationError::assert_failure)?;
                items.fold(first, |left, right| {
                    let location = merge_loci(left.location.as_ref(), right.location.as_ref());
                    located(
                        ExprCore::Apply {
                            operator: expr(ExprCore::Internal { builtin }),
                            args: vec![left, right],
                        },
                        location,
                    )
                })
            }
            ast::ExpressionKind::Prime(inner) => {
                apply_builtin(Builtin::Prime, recurse(inner)?, Fixity::Postfix)
            }
            ast::ExpressionKind::Unchanged(inner) => {
                apply_builtin(Builtin::UNCHANGED, recurse(inner)?, Fixity::Prefix)
            }
            ast::ExpressionKind::Enabled(inner) => {
                apply_builtin(Builtin::ENABLED, recurse(inner)?, Fixity::Prefix)
            }
            ast::ExpressionKind::If {
                condition,
                consequent,
                alternative,
            } => at_location(ExprCore::If {
                condition: recurse(condition)?,
                consequent: recurse(consequent)?,
                alternative: recurse(alternative)?,
            }),
            ast::ExpressionKind::Case { arms, other } => at_location(ExprCore::Case {
                arms: arms
                    .iter()
                    .map(|arm| {
                        Ok(CaseArm {
                            condition: recurse(&arm.condition)?,
                            body: recurse(&arm.body)?,
                        })
                    })
                    .collect::<Result<_>>()?,
                other: other.as_ref().map(recurse).transpose()?,
            }),
            ast::ExpressionKind::Let {
                definitions,
                instances,
                body,
                ..
            } => {
                let mut units: Vec<ast::DefinitionUnit> = definitions
                    .iter()
                    .map(|definition| ast::DefinitionUnit::Definition(definition.clone()))
                    .chain(
                        instances
                            .iter()
                            .flatten()
                            .map(|instance| ast::DefinitionUnit::Instance(instance.clone())),
                    )
                    .collect();
                units.sort_by(|left, right| {
                    let left = get_definition_location(left);
                    let right = get_definition_location(right);
                    left.line
                        .cmp(&right.line)
                        .then(left.column.cmp(&right.column))
                });
                at_location(ExprCore::Let {
                    definitions: units
                        .iter()
                        .map(|definition| self.convert_definition(definition, is_except))
                        .collect::<Result<_>>()?,
                    body: recurse(body)?,
                })
            }
            ast::ExpressionKind::Quantified {
                quantifier,
                bounds,
                body,
            } => {
                if has_tuple(bounds) {
                    let tuply = self.get_tuply_bounds(bounds, is_except)?;
                    let expanded =
                        expand_quant(get_quantifier(*quantifier), &tuply, recurse(body)?);
                    return self.expand_tuples(expanded, location);
                }
                at_location(ExprCore::Quant {
                    quantifier: get_quantifier(*quantifier),
                    bounds: self.convert_bounds(bounds, is_except)?,
                    body: recurse(body)?,
                })
            }
            ast::ExpressionKind::UnboundedQuantifier {
                quantifier,
                names,
                is_temporal,
                body,
                ..
            } => {
                let body = recurse(body)?;
                let quantifier = get_quantifier(*quantifier);
                if *is_temporal {
                    at_location(ExprCore::Tquant {
                        quantifier,
                        names: get_names(names),
                        body,
                    })
                } else {
                    at_location(ExprCore::Quant {
                        quantifier,
                        bounds: get_unbounded(&get_names(names)),
                        body,
                    })
                }
            }
            ast::ExpressionKind::Choose { pattern, set, body } => match pattern {
                ast::BoundPattern::Tuple { names, .. } => {
                    let domain = set.as_ref().map(recurse).transpose()?;
                    let expanded = expand_choose(
                        TuplyBinder::Choose { domain },
                        &get_names(names),
                        recurse(body)?,
                    );
                    return self.expand_tuples(expanded, location);
                }
                ast::BoundPattern::Name { name, .. } => at_location(ExprCore::Choose {
                    name: name.to_string(),
                    domain: set.as_ref().map(recurse).transpose()?,
                    body: recurse(body)?,
                }),
            },
            ast::ExpressionKind::SetEnumeration(elements) => at_location(ExprCore::SetEnum {
                elements: self.convert_expressions(elements, is_except)?,
            }),
            ast::ExpressionKind::SetFilter { bound, predicate } => match &bound.pattern {
                ast::BoundPattern::Tuple { names, .. } => {
                    let domain = recurse(&bound.set)?;
                    let expanded = expand_choose(
                        TuplyBinder::SetSt { domain },
                        &get_names(names),
                        recurse(predicate)?,
                    );
                    return self.expand_tuples(expanded, location);
                }
                ast::BoundPattern::Name { name, .. } => at_location(ExprCore::SetSt {
                    name: name.to_string(),
                    domain: recurse(&bound.set)?,
                    body: recurse(predicate)?,
                }),
            },
            ast::ExpressionKind::SetMap {
                expression: element,
                bounds,
            } => {
                if has_tuple(bounds) {
                    let element = recurse(element)?;
                    let expanded =
                        expand_set_of(element, &self.get_tuply_bounds(bounds, is_except)?);
                    return self.expand_tuples(expanded, location);
                }
                at_location(ExprCore::SetOf {
                    element: recurse(element)?,
                    bounds: self.convert_bounds(bounds, is_except)?,
                })
            }
            // tlapm's tuple parser binds as (<< >>> elements) >>= ">>", which keeps only the
            // location of the closing >>.
            ast::ExpressionKind::Tuple(elements) => located(
                ExprCore::Tuple {
                    elements: self.convert_expressions(elements, is_except)?,
                },
                Some(Locus {
                    start_line: location.end_line,
                    start_column: location.end_column - 2,
                    ..location.clone()
                }),
            ),
            ast::ExpressionKind::FunctionConstruction { bounds, body } => {
                if has_tuple(bounds) {
                    let tuply = self.get_tuply_bounds(bounds, is_except)?;
                    let expanded = expand_fcn(&tuply, recurse(body)?);
                    return self.expand_tuples(expanded, location);
                }
                at_location(ExprCore::Fcn {
                    bounds: self.convert_bounds(bounds, is_except)?,
                    body: recurse(body)?,
                })
            }
            ast::ExpressionKind::FunctionSet { domain, range } => at_location(ExprCore::Arrow {
                domain: recurse(domain)?,
                range: recurse(range)?,
            }),
            ast::ExpressionKind::Record { is_set, fields } => {
                let fields = fields
                    .iter()
                    .map(|field| {
                        Ok(Field {
                            name: field.name.to_string(),
                            value: recurse(&field.value)?,
                        })
                    })
                    .collect::<Result<_>>()?;
                at_location(if *is_set {
                    ExprCore::Rect { fields }
                } else {
                    ExprCore::Record { fields }
                })
            }
            ast::ExpressionKind::Except { function, updates } => at_location(ExprCore::Except {
                function: recurse(function)?,
                specs: updates
                    .iter()
                    .map(|update| {
                        Ok(ExceptSpec {
                            trail: update
                                .path
                                .iter()
                                .map(|point| {
                                    Ok(match point {
                                        ast::ExceptPathStep::Field(name) => {
                                            ExceptPoint::Dot(name.to_string())
                                        }
                                        ast::ExceptPathStep::Index(args) => {
                                            ExceptPoint::Apply(match args.as_slice() {
                                                [arg] => recurse(arg)?,
                                                _ => expr(ExprCore::Tuple {
                                                    elements: self
                                                        .convert_expressions(args, is_except)?,
                                                }),
                                            })
                                        }
                                    })
                                })
                                .collect::<Result<_>>()?,
                            value: self.convert_expression(&update.value, true)?,
                        })
                    })
                    .collect::<Result<_>>()?,
            }),
            ast::ExpressionKind::ExceptAt => at_location(ExprCore::At { is_except }),
            ast::ExpressionKind::Bracket(_) => {
                return Err(ObligationError::proof(
                    "Unexpected [ without a function or subscript",
                ));
            }
            ast::ExpressionKind::FunctionApplication { function, args } => {
                at_location(ExprCore::FcnApp {
                    function: recurse(function)?,
                    args: self.convert_expressions(args, is_except)?,
                })
            }
            ast::ExpressionKind::FieldAccess { record, field } => at_location(ExprCore::Dot {
                expression: recurse(record)?,
                field: field.to_string(),
            }),
            ast::ExpressionKind::Product(factors) => at_location(ExprCore::Product {
                factors: self.convert_expressions(factors, is_except)?,
            }),
            ast::ExpressionKind::Always(inner) | ast::ExpressionKind::Eventually(inner) => {
                let is_always = matches!(expression.kind, ast::ExpressionKind::Always(_));
                if let ast::ExpressionKind::Action {
                    is_box,
                    action,
                    subscript,
                } = &inner.kind
                    && *is_box == is_always
                {
                    return Ok(at_location(ExprCore::Tsub {
                        modal: modal(*is_box),
                        action: recurse(action)?,
                        subscript: recurse(subscript)?,
                    }));
                }
                apply_builtin(
                    if is_always {
                        Builtin::BoxTrue
                    } else {
                        Builtin::Diamond
                    },
                    recurse(inner)?,
                    Fixity::Prefix,
                )
            }
            ast::ExpressionKind::Action {
                is_box,
                action,
                subscript,
            } => at_location(ExprCore::Sub {
                modal: modal(*is_box),
                action: recurse(action)?,
                subscript: recurse(subscript)?,
            }),
            ast::ExpressionKind::Fairness {
                is_strong,
                subscript,
                action,
                ..
            } => at_location(ExprCore::Fair {
                fairness: if *is_strong {
                    Fairness::Strong
                } else {
                    Fairness::Weak
                },
                subscript: recurse(subscript)?,
                action: recurse(action)?,
            }),
            ast::ExpressionKind::Label {
                name, params, body, ..
            } => at_location(ExprCore::Parens {
                expression: recurse(body)?,
                form: ParenForm::Nlabel {
                    label: name.to_string(),
                    names: get_names(params),
                },
            }),
            ast::ExpressionKind::Subexpression { selectors, .. } => {
                let Some((ast::Selector::Name { name, args }, selectors)) = selectors.split_first()
                else {
                    return Err(ObligationError::proof("Unexpected subexpression reference"));
                };
                let operator = at_location(ExprCore::Opaque {
                    name: name.to_string(),
                });
                let base = if args.is_empty() {
                    operator
                } else {
                    at_location(ExprCore::Apply {
                        operator,
                        args: self.convert_expressions(args, is_except)?,
                    })
                };
                at_location(ExprCore::Bang {
                    expression: base,
                    selectors: selectors
                        .iter()
                        .map(|selector| {
                            Ok(match selector {
                                ast::Selector::Name { name, args } => Selector::Label {
                                    label: get_canonical_name(name),
                                    args: self.convert_expressions(args, is_except)?,
                                },
                                ast::Selector::Operand(ast::Operand::First) => Selector::Left,
                                ast::Selector::Operand(ast::Operand::Last) => Selector::Right,
                                ast::Selector::Operand(ast::Operand::Index(value)) => {
                                    Selector::Number(*value as usize)
                                }
                                ast::Selector::Bound(args) => {
                                    Selector::Instance(self.convert_expressions(args, is_except)?)
                                }
                                ast::Selector::At => Selector::At,
                                ast::Selector::Colon => Selector::Down,
                            })
                        })
                        .collect::<Result<_>>()?,
                })
            }
        })
    }

    fn convert_instance(&self, instance: &ast::Instance) -> Result<InstanceDefinition> {
        Ok(InstanceDefinition {
            location: Some(
                self.get_range_locus(
                    instance
                        .definition_range
                        .as_ref()
                        .unwrap_or(&instance.instance_range),
                ),
            ),
            args: instance
                .params
                .iter()
                .map(|param| param.name.to_string())
                .collect(),
            module: instance.module.to_string(),
            substitutions: instance
                .substitutions
                .iter()
                .map(|substitution| {
                    Ok(Substitution {
                        name: get_canonical_name(&substitution.name),
                        expression: self.convert_expression(&substitution.expression, false)?,
                    })
                })
                .collect::<Result<_>>()?,
        })
    }

    fn convert_definition(
        &self,
        definition: &ast::DefinitionUnit,
        is_except: bool,
    ) -> Result<Defn> {
        let location = self.get_locus(get_definition_location(definition));
        let definition = match definition {
            ast::DefinitionUnit::Instance(instance) => {
                let Some(name) = &instance.name else {
                    return Err(ObligationError::proof("Unexpected keyword INSTANCE"));
                };
                return Ok(Defn {
                    core: DefnCore::Instance {
                        name: name.to_string(),
                        instance: self.convert_instance(instance)?,
                    },
                    location: Some(location),
                });
            }
            ast::DefinitionUnit::Definition(definition) => definition,
        };
        // A prefix minus is the operator -.
        let name = match &definition.kind {
            ast::DefinitionKind::Operator { params, .. }
                if params.len() == 1 && &*definition.name == "-" =>
            {
                "-.".to_owned()
            }
            _ => get_canonical_name(&definition.name),
        };
        let body = self.convert_expression(&definition.body, is_except)?;
        let params = match &definition.kind {
            ast::DefinitionKind::Function { bounds } => {
                let body = if has_tuple(bounds) {
                    let tuply = self.get_tuply_bounds(bounds, is_except)?;
                    self.expand_tuples(expand_fcn(&tuply, body), location.clone())?
                } else {
                    let bounds = self.convert_bounds(bounds, is_except)?;
                    located(ExprCore::Fcn { bounds, body }, Some(location.clone()))
                };
                return Ok(Defn {
                    core: DefnCore::Operator { name, body },
                    location: Some(location),
                });
            }
            ast::DefinitionKind::Operator { params, .. } => params,
        };
        let operator_body = if params.is_empty() {
            body
        } else {
            located(
                ExprCore::Lambda {
                    params: params
                        .iter()
                        .map(|param| Param {
                            name: get_canonical_name(&param.name),
                            shape: param.arity,
                            location: param.location.as_ref().map(|location| {
                                self.get_point_locus(location, get_utf16_length(&param.name))
                            }),
                        })
                        .collect(),
                    body,
                },
                Some(location.clone()),
            )
        };
        let methods = match &definition.location.range {
            Some(range) => read_new_method(
                &self.lines,
                Position {
                    line: get_index(range.end.line),
                    column: range.end.column as usize,
                },
            )?,
            None => None,
        };
        Ok(Defn {
            core: match methods {
                Some(methods) => DefnCore::Bpragma {
                    name,
                    body: operator_body,
                    methods,
                },
                None => DefnCore::Operator {
                    name,
                    body: operator_body,
                },
            },
            location: Some(location),
        })
    }

    fn convert_new_symbol(&self, symbol: &ast::NewSymbol) -> Result<Hyp> {
        let location = self.get_locus(&symbol.location);
        let core = if symbol.level == ast::SymbolLevel::Variable {
            HypCore::Flex {
                name: symbol.name.to_string(),
            }
        } else {
            HypCore::Fresh {
                name: symbol.name.to_string(),
                shape: symbol.arity,
                level: get_level(symbol.level),
                domain: symbol
                    .set
                    .as_ref()
                    .map(|set| self.convert_expression(set, false))
                    .transpose()?,
                domain_visibility: Visibility::Visible,
            }
        };
        Ok(Rc::new(HypNode {
            core,
            location: Some(location),
        }))
    }

    // Anonymization judges the time of each assumption once it resolves the names in it.
    fn convert_sequent(&self, statement: &ast::Statement) -> Result<Sequent> {
        match statement {
            ast::Statement::Expression(expression) => Ok(Sequent {
                context: Vec::new(),
                active: self.convert_expression(expression, false)?,
            }),
            ast::Statement::AssumeProve(assume_prove) => self.convert_assume_prove(assume_prove),
        }
    }

    fn convert_assume_prove(&self, statement: &ast::AssumeProve) -> Result<Sequent> {
        Ok(Sequent {
            context: statement
                .assumptions
                .iter()
                .map(|assumption| {
                    let expression = match assumption {
                        ast::Assumed::NewSymbol(symbol) => return self.convert_new_symbol(symbol),
                        ast::Assumed::AssumeProve(assume_prove) => located(
                            ExprCore::Sequent {
                                sequent: self.convert_assume_prove(assume_prove)?,
                            },
                            Some(self.get_locus(&assume_prove.location)),
                        ),
                        ast::Assumed::Expression(expression) => {
                            self.convert_fact_label(expression)?
                        }
                        ast::Assumed::Label { .. } => {
                            return Err(ObligationError::unsupported(
                                "labeled ASSUME/PROVE in proof obligations",
                            ));
                        }
                    };
                    let location = expression.location.clone();
                    Ok(get_fact(
                        expression,
                        Visibility::Visible,
                        Time::Now,
                        location,
                    ))
                })
                .collect::<Result<_>>()?,
            active: self.convert_expression(&statement.conclusion, false)?,
        })
    }

    /// A labeled hypothesis is an Xlabel without parameters, not an Nlabel like a labeled
    /// expression.
    fn convert_fact_label(&self, expression: &ast::Expr) -> Result<Expr> {
        let ast::ExpressionKind::Label {
            name, params, body, ..
        } = &expression.kind
        else {
            return self.convert_expression(expression, false);
        };
        if !params.is_empty() {
            return self.convert_expression(expression, false);
        }
        let location = self.get_locus(&expression.location);
        Ok(located(
            ExprCore::Parens {
                expression: self.convert_expression(body, false)?,
                form: ParenForm::Xlabel {
                    label: name.to_string(),
                    indices: Vec::new(),
                },
            },
            Some(location),
        ))
    }

    fn convert_fact(&self, fact: &ast::Fact) -> Result<Expr> {
        let ast::Fact::Expression(fact) = fact else {
            return Err(ObligationError::unsupported(
                "MODULE facts in proof obligations are not supported",
            ));
        };
        let expression = self.convert_expression(fact, false)?;
        Ok(match &expression.core {
            ExprCore::Bang {
                expression,
                selectors,
            } if selectors.is_empty() => expression.clone(),
            _ => expression,
        })
    }

    fn convert_def(&self, fact: &ast::Fact) -> Result<UseDef> {
        let location = Some(self.get_locus(get_fact_location(fact)));
        let name = match fact {
            ast::Fact::Module { name, .. } => name.to_string(),
            ast::Fact::Expression(expression) => match &expression.kind {
                ast::ExpressionKind::Identifier { name, .. } => get_canonical_name(name),
                ast::ExpressionKind::OperatorReference { operator, .. } => {
                    get_canonical_name(operator)
                }
                _ => {
                    return Err(ObligationError::unsupported(
                        "This DEF clause in proof obligations is not supported",
                    ));
                }
            },
        };
        Ok(UseDef {
            core: UseDefCore::Dvar { name },
            location,
        })
    }

    fn convert_usable(&self, facts: &[ast::Fact], defs: &[ast::Fact]) -> Result<Usable> {
        Ok(Usable {
            facts: facts
                .iter()
                .map(|fact| self.convert_fact(fact))
                .collect::<Result<_>>()?,
            defs: defs
                .iter()
                .map(|fact| self.convert_def(fact))
                .collect::<Result<_>>()?,
        })
    }

    fn get_step_number(&self, token: Option<&StepToken>, level: usize) -> StepNumber {
        match token {
            Some(token) if !token.label.is_empty() => StepNumber::Named {
                level,
                label: token.label.clone(),
                is_anonymous: false,
            },
            _ => StepNumber::Unnamed {
                level,
                id: get_unique(&self.counter),
            },
        }
    }

    /// to_proof: a missing proof is implicitly omitted where the enclosing step is.
    fn convert_proof(
        &self,
        proof: Option<&ast::Proof>,
        level: usize,
        enclosing: Option<Locus>,
    ) -> Result<Proof> {
        let Some(proof) = proof else {
            return Ok(Proof {
                core: ProofCore::Omitted(Omission::Implicit),
                props: proof_props(enclosing, None),
            });
        };
        Ok(match &proof.kind {
            ast::ProofKind::Obvious { keyword } => Proof {
                core: ProofCore::Obvious,
                props: self.with_method(keyword)?,
            },
            ast::ProofKind::Omitted { keyword } => Proof {
                core: ProofCore::Omitted(Omission::Explicit),
                props: proof_props(Some(self.get_range_locus(keyword)), None),
            },
            ast::ProofKind::By {
                is_only,
                facts,
                defs,
                keyword,
            } => {
                let usable = self.convert_usable(facts, defs)?;
                let location = self.get_range_locus(keyword);
                Proof {
                    core: ProofCore::By {
                        usable,
                        is_only: *is_only,
                    },
                    props: ProofProps {
                        location: Some(location),
                        step: Some(StepNumber::Unnamed { level, id: 0 }),
                        method: self.get_method(proof.location.range.as_ref())?,
                        ..ProofProps::default()
                    },
                }
            }
            ast::ProofKind::Steps { steps, .. } => {
                // A <*> first step takes the enclosing level only after PROOF, and the top level
                // always counts as PROOF.
                let tokens: Vec<Option<StepToken>> = steps
                    .iter()
                    .map(|step| match_step_token(&step.token))
                    .collect();
                let step_level = match tokens.first() {
                    Some(Some(first)) if first.level != "*" && first.level != "+" => {
                        first.level.parse().unwrap_or(usize::MAX)
                    }
                    _ => level,
                };
                // The parser ends the steps at the first QED.
                let Some((last, before)) = steps.split_last() else {
                    return Err(ObligationError::assert_failure());
                };
                let converted = before
                    .iter()
                    .zip(&tokens)
                    .map(|(step, token)| {
                        let number = self.get_step_number(token.as_ref(), step_level);
                        self.convert_step(step, number, step_level)
                    })
                    .collect::<Result<Vec<_>>>()?;
                let number =
                    self.get_step_number(tokens.last().and_then(Option::as_ref), step_level);
                let head = self.get_range_locus(&last.head);
                let qed_proof =
                    self.convert_proof(last.proof.as_deref(), step_level + 1, Some(head.clone()))?;
                let qed_location = merge_loci(Some(&head), qed_proof.props.location.as_ref());
                let location = converted.iter().fold(qed_location.clone(), |merged, step| {
                    merge_loci(merged.as_ref(), step.props.location.as_ref())
                });
                Proof {
                    core: ProofCore::Steps {
                        steps: converted,
                        qed: Box::new(QedStep {
                            proof: qed_proof,
                            props: proof_props(qed_location, Some(number.clone())),
                        }),
                    },
                    props: proof_props(location, Some(number)),
                }
            }
        })
    }

    /// tlapm locates a USE or HIDE by its keywords and DEF clause, since its parser drops the
    /// facts' location.
    fn get_use_locus(&self, keyword: &ast::SourceRange, defs: &[ast::Fact]) -> Option<Locus> {
        merge_loci(
            Some(&self.get_range_locus(keyword)),
            defs.last()
                .map(|def| self.get_locus(get_fact_location(def)))
                .as_ref(),
        )
    }

    fn convert_step(
        &self,
        step: &ast::ProofStep,
        number: StepNumber,
        level: usize,
    ) -> Result<Step> {
        let head = self.get_range_locus(&step.head);
        let with_proof = |make: &dyn Fn(Proof) -> StepCore| -> Result<Step> {
            let proof = self.convert_proof(step.proof.as_deref(), level + 1, Some(head.clone()))?;
            let location = merge_loci(Some(&head), proof.props.location.as_ref());
            Ok(Step {
                core: make(proof),
                props: proof_props(location, Some(number.clone())),
            })
        };
        let with_step_method = |core: StepCore| -> Result<Step> {
            Ok(Step {
                core,
                props: ProofProps {
                    step: Some(number.clone()),
                    ..self.with_method(&step.head)?
                },
            })
        };
        match &step.body {
            ast::StepBody::UseOrHide(body) => {
                let location = merge_loci(
                    Some(&self.get_range_locus(&ast::SourceRange {
                        end: step.head.start,
                        ..step.head.clone()
                    })),
                    self.get_use_locus(&body.keyword, &body.defs).as_ref(),
                );
                let usable = self.convert_usable(&body.facts, &body.defs)?;
                if body.is_hide {
                    return Ok(Step {
                        core: StepCore::Hide { usable },
                        props: proof_props(location, Some(number)),
                    });
                }
                Ok(Step {
                    core: StepCore::Use {
                        usable,
                        is_only: body.is_only,
                    },
                    props: ProofProps {
                        location,
                        step: Some(number),
                        method: self.get_method(body.location.range.as_ref())?,
                        ..ProofProps::default()
                    },
                })
            }
            ast::StepBody::Instance(_) => {
                Err(ObligationError::proof("Unexpected keyword INSTANCE"))
            }
            ast::StepBody::Define { definitions, .. } => Ok(Step {
                core: StepCore::Define {
                    definitions: definitions
                        .iter()
                        .map(|definition| self.convert_definition(definition, false))
                        .collect::<Result<_>>()?,
                },
                props: proof_props(Some(head), Some(number)),
            }),
            ast::StepBody::Have(expression) => with_step_method(StepCore::Have {
                expression: self.convert_expression(expression, false)?,
            }),
            ast::StepBody::Take { names, bounds, .. } => with_step_method(StepCore::Take {
                bounds: if names.is_empty() {
                    self.convert_bounds(bounds, false)?
                } else {
                    get_unbounded(&get_names(names))
                },
            }),
            ast::StepBody::Witness(expressions) => with_step_method(StepCore::Witness {
                expressions: self.convert_expressions(expressions, false)?,
            }),
            ast::StepBody::Pick {
                names,
                bounds,
                body,
                ..
            } => {
                let bounds = if names.is_empty() {
                    self.convert_bounds(bounds, false)?
                } else {
                    get_unbounded(&get_names(names))
                };
                let expression = self.convert_expression(body, false)?;
                with_proof(&|proof| StepCore::Pick {
                    bounds: bounds.clone(),
                    expression: expression.clone(),
                    proof,
                })
            }
            ast::StepBody::Case(expression) => {
                let expression = self.convert_expression(expression, false)?;
                with_proof(&|proof| StepCore::Pcase {
                    expression: expression.clone(),
                    proof,
                })
            }
            ast::StepBody::Assert {
                is_suffices,
                statement,
            } => {
                let sequent = self.convert_sequent(statement)?;
                with_proof(&|proof| {
                    let sequent = sequent.clone();
                    if *is_suffices {
                        StepCore::Suffices { sequent, proof }
                    } else {
                        StepCore::Assert { sequent, proof }
                    }
                })
            }
            ast::StepBody::Qed => Err(ObligationError::unsupported("QED in the middle of a proof")),
        }
    }

    fn convert_declarations(&self, declarations: &[Rc<ast::Declaration>]) -> Vec<Declaration> {
        declarations
            .iter()
            .map(|declaration| Declaration {
                name: get_canonical_name(&declaration.name),
                shape: declaration.arity,
            })
            .collect()
    }

    fn get_first_locus(&self, declarations: &[Rc<ast::Declaration>]) -> Result<Locus> {
        let first = declarations
            .first()
            .ok_or_else(ObligationError::assert_failure)?;
        Ok(self.get_locus(&first.location))
    }

    pub fn convert_module(&self, module: &ast::Module) -> Result<Mule> {
        let body = module
            .units
            .iter()
            .map(|unit| self.convert_unit(unit))
            .collect::<Result<_>>()?;
        Ok(Mule {
            name: module.name.to_string(),
            extendees: get_names(&module.extends),
            extendee_locations: Some(
                module
                    .extends_ranges
                    .iter()
                    .map(|range| self.get_range_locus(range))
                    .collect(),
            ),
            is_important: false,
            location: Some(self.get_locus(&module.location)),
            body,
            ..Mule::default()
        })
    }

    fn convert_unit(&self, unit: &ast::ModuleUnit) -> Result<ModuleUnit> {
        let (core, location) = match unit {
            ast::ModuleUnit::Constants { declarations, .. } => (
                ModuleUnitCore::Constants {
                    declarations: self.convert_declarations(declarations),
                },
                self.get_first_locus(declarations)?,
            ),
            ast::ModuleUnit::Recursive(declarations) => (
                ModuleUnitCore::Recursives {
                    declarations: self.convert_declarations(declarations),
                },
                self.get_first_locus(declarations)?,
            ),
            ast::ModuleUnit::Variables { declarations, .. } => (
                ModuleUnitCore::Variables {
                    names: declarations
                        .iter()
                        .map(|declaration| declaration.name.to_string())
                        .collect(),
                },
                self.get_first_locus(declarations)?,
            ),
            ast::ModuleUnit::Definition(definition) => (
                ModuleUnitCore::Definition {
                    definition: self.convert_definition(
                        &ast::DefinitionUnit::Definition(definition.clone()),
                        false,
                    )?,
                    where_defined: WhereDefined::User,
                    visibility: Visibility::Hidden,
                    is_local: definition.is_local,
                },
                self.get_locus(&definition.location),
            ),
            ast::ModuleUnit::Instance(instance) => {
                let location = self.get_locus(&instance.location);
                if instance.name.is_none() {
                    (
                        ModuleUnitCore::Anoninst {
                            instance: self.convert_instance(instance)?,
                            is_local: instance.is_local,
                        },
                        location,
                    )
                } else {
                    (
                        ModuleUnitCore::Definition {
                            definition: self.convert_definition(
                                &ast::DefinitionUnit::Instance(instance.clone()),
                                false,
                            )?,
                            where_defined: WhereDefined::User,
                            visibility: Visibility::Hidden,
                            is_local: instance.is_local,
                        },
                        self.get_range_locus(&instance.instance_range),
                    )
                }
            }
            ast::ModuleUnit::Assumption(assumption) => (
                ModuleUnitCore::Axiom {
                    name: assumption.name.as_ref().map(ToString::to_string),
                    expression: self.with_expression_method(
                        self.convert_expression(&assumption.expression, false)?,
                        assumption.location.range.as_ref(),
                    )?,
                },
                self.get_locus(&assumption.location),
            ),
            ast::ModuleUnit::Theorem(theorem) => {
                let location = self.get_locus(&theorem.location);
                let end = self.with_pragma(location.clone());
                let sequent = self.convert_sequent(&theorem.statement)?;
                let sequent = Sequent {
                    active: self.with_expression_method(
                        sequent.active,
                        get_statement_range(&theorem.statement),
                    )?,
                    context: sequent.context,
                };
                (
                    ModuleUnitCore::Theorem {
                        name: theorem.name.as_ref().map(ToString::to_string),
                        sequent,
                        axiom_count: 0,
                        proof: self.convert_proof(
                            theorem.proof.as_ref(),
                            0,
                            Some(Locus {
                                start_line: end.end_line,
                                start_column: end.end_column,
                                ..end
                            }),
                        )?,
                    },
                    location,
                )
            }
            ast::ModuleUnit::Use(use_or_hide) => {
                return Ok(ModuleUnit {
                    core: ModuleUnitCore::Mutate {
                        mode: if use_or_hide.is_hide {
                            MutateMode::Hide
                        } else {
                            MutateMode::Use
                        },
                        usable: self.convert_usable(&use_or_hide.facts, &use_or_hide.defs)?,
                    },
                    location: self.get_use_locus(&use_or_hide.keyword, &use_or_hide.defs),
                });
            }
            ast::ModuleUnit::Module(module) => {
                return Ok(ModuleUnit {
                    core: ModuleUnitCore::Submod {
                        module: Box::new(Mule {
                            is_important: true,
                            ..self.convert_module(module)?
                        }),
                    },
                    location: None,
                });
            }
        };
        Ok(ModuleUnit {
            core,
            location: Some(location),
        })
    }
}

#[cfg(test)]
mod tests {
    // Each case converts a module tla-front parses and expects the canonical JSON that
    // `source.ts` gives under Bun for the TypeScript parser's module.
    use super::*;
    use crate::pragma::{PragmaSetting, PragmaValue};
    use tla_front::dump::Json;

    type Entries = Vec<(&'static str, Option<Json>)>;

    fn text(value: &str) -> Json {
        Json::Text(Rc::from(value))
    }

    fn number(value: usize) -> Json {
        Json::Number(value as f64)
    }

    fn object(fields: Entries) -> Json {
        Json::Object(
            fields
                .into_iter()
                .filter_map(|(key, value)| value.map(|value| (key, value)))
                .collect(),
        )
    }

    fn kind(name: &str, mut fields: Entries) -> Json {
        fields.push(("kind", Some(text(name))));
        object(fields)
    }

    fn list<Item>(items: &[Item], each: impl Fn(&Item) -> Json) -> Json {
        Json::Array(items.iter().map(each).collect())
    }

    fn strings(items: &[String]) -> Json {
        list(items, |item| text(item))
    }

    fn locus(value: &Locus) -> Json {
        object(vec![
            ("file", Some(text(&value.file))),
            ("startLine", Some(number(value.start_line as usize))),
            ("startColumn", Some(number(value.start_column as usize))),
            ("endLine", Some(number(value.end_line as usize))),
            ("endColumn", Some(number(value.end_column as usize))),
        ])
    }

    fn debug(value: impl std::fmt::Debug) -> Json {
        text(&format!("{value:?}"))
    }

    fn bound(value: &Bound) -> Json {
        object(vec![
            ("name", Some(text(&value.name))),
            ("level", Some(debug(value.level))),
            (
                "domain",
                Some(match &value.domain {
                    BoundDomain::NoDomain => kind("NoDomain", vec![]),
                    BoundDomain::Ditto => kind("Ditto", vec![]),
                    BoundDomain::Domain(domain) => {
                        kind("Domain", vec![("expression", Some(expression(domain)))])
                    }
                }),
            ),
        ])
    }

    fn expressions(items: &[Expr]) -> Json {
        list(items, expression)
    }

    fn method(value: &OldMethod) -> Json {
        object(vec![
            ("name", Some(text(&value.name))),
            ("tactic", value.tactic.as_deref().map(text)),
            ("timeout", value.timeout.map(Json::Number)),
        ])
    }

    fn setting(value: &PragmaSetting) -> Json {
        let value_json = match &value.value {
            PragmaValue::Default => kind("Default", vec![]),
            PragmaValue::String(string) => kind("String", vec![("value", Some(text(string)))]),
            PragmaValue::Float(float) => kind("Float", vec![("value", Some(Json::Number(*float)))]),
        };
        object(vec![
            ("hint", Some(text(&value.hint))),
            ("value", Some(value_json)),
        ])
    }

    fn fields(items: &[Field]) -> Json {
        list(items, |field| {
            object(vec![
                ("name", Some(text(&field.name))),
                ("value", Some(expression(&field.value))),
            ])
        })
    }

    fn paren_form(form: &ParenForm) -> Json {
        match form {
            ParenForm::Syntax => kind("Syntax", vec![]),
            ParenForm::Nlabel { label, names } => kind(
                "Nlabel",
                vec![
                    ("label", Some(text(label))),
                    ("names", Some(strings(names))),
                ],
            ),
            ParenForm::Xlabel { label, indices } => kind(
                "Xlabel",
                vec![
                    ("label", Some(text(label))),
                    (
                        "indices",
                        Some(list(indices, |index| {
                            object(vec![
                                ("name", Some(text(&index.name))),
                                ("index", Some(number(index.index))),
                            ])
                        })),
                    ),
                ],
            ),
        }
    }

    fn except_specs(specs: &[ExceptSpec]) -> Json {
        list(specs, |spec| {
            object(vec![
                (
                    "trail",
                    Some(list(&spec.trail, |point| match point {
                        ExceptPoint::Dot(field) => kind("Dot", vec![("field", Some(text(field)))]),
                        ExceptPoint::Apply(inner) => {
                            kind("Apply", vec![("expression", Some(expression(inner)))])
                        }
                    })),
                ),
                ("value", Some(expression(&spec.value))),
            ])
        })
    }

    fn expression_entries(core: &ExprCore) -> (&'static str, Entries) {
        let some = Some;
        match core {
            ExprCore::Ix { index } => ("Ix", vec![("index", some(Json::Number(*index as f64)))]),
            ExprCore::Opaque { name } => ("Opaque", vec![("name", some(text(name)))]),
            ExprCore::Internal { builtin } => {
                ("Internal", vec![("builtin", some(text(builtin.name())))])
            }
            ExprCore::Lambda { params, body } => (
                "Lambda",
                vec![
                    (
                        "params",
                        some(list(params, |param| {
                            object(vec![
                                ("name", some(text(&param.name))),
                                ("shape", some(number(param.shape))),
                                ("location", param.location.as_ref().map(locus)),
                            ])
                        })),
                    ),
                    ("body", some(expression(body))),
                ],
            ),
            ExprCore::Sequent { sequent: inner } => {
                ("Sequent", vec![("sequent", some(sequent(inner)))])
            }
            ExprCore::Bang {
                expression: inner,
                selectors,
            } => (
                "Bang",
                vec![
                    ("expression", some(expression(inner))),
                    ("selectors", some(list(selectors, selector))),
                ],
            ),
            ExprCore::Apply { operator, args } => (
                "Apply",
                vec![
                    ("operator", some(expression(operator))),
                    ("args", some(expressions(args))),
                ],
            ),
            ExprCore::With {
                expression: inner,
                method: used,
            } => (
                "With",
                vec![
                    ("expression", some(expression(inner))),
                    ("method", some(method(used))),
                ],
            ),
            ExprCore::If {
                condition,
                consequent,
                alternative,
            } => (
                "If",
                vec![
                    ("condition", some(expression(condition))),
                    ("consequent", some(expression(consequent))),
                    ("alternative", some(expression(alternative))),
                ],
            ),
            ExprCore::List { bullet, items } => (
                "List",
                vec![
                    ("bullet", some(debug(bullet))),
                    ("items", some(expressions(items))),
                ],
            ),
            ExprCore::Let { definitions, body } => (
                "Let",
                vec![
                    ("definitions", some(list(definitions, defn))),
                    ("body", some(expression(body))),
                ],
            ),
            ExprCore::Quant {
                quantifier,
                bounds,
                body,
            } => (
                "Quant",
                vec![
                    ("quantifier", some(debug(quantifier))),
                    ("bounds", some(list(bounds, bound))),
                    ("body", some(expression(body))),
                ],
            ),
            ExprCore::Tquant {
                quantifier,
                names,
                body,
            } => (
                "Tquant",
                vec![
                    ("quantifier", some(debug(quantifier))),
                    ("names", some(strings(names))),
                    ("body", some(expression(body))),
                ],
            ),
            ExprCore::Choose { name, domain, body } => (
                "Choose",
                vec![
                    ("name", some(text(name))),
                    ("domain", domain.as_ref().map(expression)),
                    ("body", some(expression(body))),
                ],
            ),
            ExprCore::SetSt { name, domain, body } => (
                "SetSt",
                vec![
                    ("name", some(text(name))),
                    ("domain", some(expression(domain))),
                    ("body", some(expression(body))),
                ],
            ),
            ExprCore::SetOf { element, bounds } => (
                "SetOf",
                vec![
                    ("element", some(expression(element))),
                    ("bounds", some(list(bounds, bound))),
                ],
            ),
            ExprCore::SetEnum { elements } => {
                ("SetEnum", vec![("elements", some(expressions(elements)))])
            }
            ExprCore::Product { factors } => {
                ("Product", vec![("factors", some(expressions(factors)))])
            }
            ExprCore::Tuple { elements } => {
                ("Tuple", vec![("elements", some(expressions(elements)))])
            }
            ExprCore::Fcn { bounds, body } => (
                "Fcn",
                vec![
                    ("bounds", some(list(bounds, bound))),
                    ("body", some(expression(body))),
                ],
            ),
            ExprCore::FcnApp { function, args } => (
                "FcnApp",
                vec![
                    ("function", some(expression(function))),
                    ("args", some(expressions(args))),
                ],
            ),
            ExprCore::Arrow { domain, range } => (
                "Arrow",
                vec![
                    ("domain", some(expression(domain))),
                    ("range", some(expression(range))),
                ],
            ),
            ExprCore::Rect { fields: items } => ("Rect", vec![("fields", some(fields(items)))]),
            ExprCore::Record { fields: items } => ("Record", vec![("fields", some(fields(items)))]),
            ExprCore::Except { function, specs } => (
                "Except",
                vec![
                    ("function", some(expression(function))),
                    ("specs", some(except_specs(specs))),
                ],
            ),
            ExprCore::Dot {
                expression: inner,
                field,
            } => (
                "Dot",
                vec![
                    ("expression", some(expression(inner))),
                    ("field", some(text(field))),
                ],
            ),
            ExprCore::Sub {
                modal,
                action,
                subscript,
            } => (
                "Sub",
                vec![
                    ("modal", some(debug(modal))),
                    ("action", some(expression(action))),
                    ("subscript", some(expression(subscript))),
                ],
            ),
            ExprCore::Tsub {
                modal,
                action,
                subscript,
            } => (
                "Tsub",
                vec![
                    ("modal", some(debug(modal))),
                    ("action", some(expression(action))),
                    ("subscript", some(expression(subscript))),
                ],
            ),
            ExprCore::Fair {
                fairness,
                subscript,
                action,
            } => (
                "Fair",
                vec![
                    ("fairness", some(debug(fairness))),
                    ("subscript", some(expression(subscript))),
                    ("action", some(expression(action))),
                ],
            ),
            ExprCore::Case { arms, other } => (
                "Case",
                vec![
                    (
                        "arms",
                        some(list(arms, |arm| {
                            object(vec![
                                ("condition", some(expression(&arm.condition))),
                                ("body", some(expression(&arm.body))),
                            ])
                        })),
                    ),
                    ("other", other.as_ref().map(expression)),
                ],
            ),
            ExprCore::String { value } => ("String", vec![("value", some(text(value)))]),
            ExprCore::Num { integer, fraction } => (
                "Num",
                vec![
                    ("integer", some(text(integer))),
                    ("fraction", some(text(fraction))),
                ],
            ),
            ExprCore::At { is_except } => ("At", vec![("isExcept", some(Json::Bool(*is_except)))]),
            ExprCore::Parens {
                expression: inner,
                form,
            } => (
                "Parens",
                vec![
                    ("expression", some(expression(inner))),
                    ("form", some(paren_form(form))),
                ],
            ),
        }
    }

    fn expression(value: &Expr) -> Json {
        let (name, mut entries) = expression_entries(&value.core);
        entries.push(("location", value.location.as_ref().map(locus)));
        entries.push(("isAtomic", value.is_atomic.then_some(Json::Bool(true))));
        kind(name, entries)
    }

    fn selector(value: &Selector) -> Json {
        match value {
            Selector::Down => kind("Down", vec![]),
            Selector::Number(index) => kind("Number", vec![("value", Some(number(*index)))]),
            Selector::Left => kind("Left", vec![]),
            Selector::Right => kind("Right", vec![]),
            Selector::At => kind("At", vec![]),
            Selector::Instance(args) => kind("Instance", vec![("args", Some(expressions(args)))]),
            Selector::Label { label, args } => kind(
                "Label",
                vec![
                    ("label", Some(text(label))),
                    ("args", Some(expressions(args))),
                ],
            ),
        }
    }

    fn instance(value: &InstanceDefinition) -> Json {
        object(vec![
            ("args", Some(strings(&value.args))),
            ("module", Some(text(&value.module))),
            (
                "substitutions",
                Some(list(&value.substitutions, |substitution| {
                    object(vec![
                        ("name", Some(text(&substitution.name))),
                        ("expression", Some(expression(&substitution.expression))),
                    ])
                })),
            ),
            ("location", value.location.as_ref().map(locus)),
        ])
    }

    fn defn(value: &Defn) -> Json {
        let (name, mut entries): (&str, Entries) = match &value.core {
            DefnCore::Recursive { name, shape } => (
                "Recursive",
                vec![("name", Some(text(name))), ("shape", Some(number(*shape)))],
            ),
            DefnCore::Operator { name, body } => (
                "Operator",
                vec![("name", Some(text(name))), ("body", Some(expression(body)))],
            ),
            DefnCore::Instance {
                name,
                instance: definition,
            } => (
                "Instance",
                vec![
                    ("name", Some(text(name))),
                    ("instance", Some(instance(definition))),
                ],
            ),
            DefnCore::Bpragma {
                name,
                body,
                methods,
            } => (
                "Bpragma",
                vec![
                    ("name", Some(text(name))),
                    ("body", Some(expression(body))),
                    ("methods", Some(list(methods, |group| list(group, setting)))),
                ],
            ),
        };
        entries.push(("location", value.location.as_ref().map(locus)));
        kind(name, entries)
    }

    fn where_defined(value: WhereDefined) -> Json {
        match value {
            WhereDefined::Builtin => text("Builtin"),
            WhereDefined::User => text("User"),
            WhereDefined::Proof(time) => kind("Proof", vec![("time", Some(debug(time)))]),
        }
    }

    fn hyp(value: &Hyp) -> Json {
        let (name, mut entries): (&str, Entries) = match &value.core {
            HypCore::Fresh {
                name,
                shape,
                level,
                domain,
                domain_visibility,
            } => (
                "Fresh",
                vec![
                    ("name", Some(text(name))),
                    ("shape", Some(number(*shape))),
                    ("level", Some(debug(level))),
                    ("domain", domain.as_ref().map(expression)),
                    ("domainVisibility", Some(debug(domain_visibility))),
                ],
            ),
            HypCore::Flex { name } => ("Flex", vec![("name", Some(text(name)))]),
            HypCore::Defn {
                definition,
                where_defined: defined,
                visibility,
                is_local,
                is_constness_unset,
            } => (
                "Defn",
                vec![
                    ("definition", Some(defn(definition))),
                    ("whereDefined", Some(where_defined(*defined))),
                    ("visibility", Some(debug(visibility))),
                    ("isLocal", Some(Json::Bool(*is_local))),
                    (
                        "isConstnessUnset",
                        is_constness_unset.then_some(Json::Bool(true)),
                    ),
                ],
            ),
            HypCore::Fact {
                expression: fact,
                visibility,
                time,
                use_location,
            } => (
                "Fact",
                vec![
                    ("expression", Some(expression(fact))),
                    ("visibility", Some(debug(visibility))),
                    ("time", Some(debug(time))),
                    ("useLocation", use_location.as_ref().map(locus)),
                ],
            ),
        };
        entries.push(("location", value.location.as_ref().map(locus)));
        kind(name, entries)
    }

    fn sequent(value: &Sequent) -> Json {
        object(vec![
            ("context", Some(list(&value.context, hyp))),
            ("active", Some(expression(&value.active))),
        ])
    }

    fn use_def(def: &UseDef) -> Json {
        let (name, mut entries): (&str, Entries) = match &def.core {
            UseDefCore::Dvar { name } => ("Dvar", vec![("name", Some(text(name)))]),
            UseDefCore::Dx { index } => ("Dx", vec![("index", Some(Json::Number(*index as f64)))]),
        };
        entries.push(("location", def.location.as_ref().map(locus)));
        kind(name, entries)
    }

    fn usable(value: &Usable) -> Json {
        object(vec![
            ("facts", Some(expressions(&value.facts))),
            ("defs", Some(list(&value.defs, use_def))),
        ])
    }

    fn step_number(value: &StepNumber) -> Json {
        match value {
            StepNumber::Named {
                level,
                label,
                is_anonymous,
            } => kind(
                "Named",
                vec![
                    ("level", Some(number(*level))),
                    ("label", Some(text(label))),
                    ("isAnonymous", Some(Json::Bool(*is_anonymous))),
                ],
            ),
            StepNumber::Unnamed { level, id } => kind(
                "Unnamed",
                vec![("level", Some(number(*level))), ("id", Some(number(*id)))],
            ),
        }
    }

    fn with_props(mut entries: Entries, props: &ProofProps) -> Entries {
        entries.push(("location", props.location.as_ref().map(locus)));
        entries.push(("step", props.step.as_ref().map(step_number)));
        entries.push(("method", props.method.as_ref().map(method)));
        entries.push(("useLocation", props.use_location.as_ref().map(locus)));
        entries
    }

    fn proof(value: &Proof) -> Json {
        let (name, entries): (&str, Entries) = match &value.core {
            ProofCore::Obvious => ("Obvious", vec![]),
            ProofCore::Omitted(omitted) => ("Omitted", vec![("omission", Some(debug(omitted)))]),
            ProofCore::By {
                usable: used,
                is_only,
            } => (
                "By",
                vec![
                    ("usable", Some(usable(used))),
                    ("isOnly", Some(Json::Bool(*is_only))),
                ],
            ),
            ProofCore::Steps { steps, qed } => (
                "Steps",
                vec![
                    ("steps", Some(list(steps, step))),
                    (
                        "qed",
                        Some(object(with_props(
                            vec![("proof", Some(proof(&qed.proof)))],
                            &qed.props,
                        ))),
                    ),
                ],
            ),
            ProofCore::Error(message) => ("Error", vec![("message", Some(text(message)))]),
        };
        kind(name, with_props(entries, &value.props))
    }

    fn step(value: &Step) -> Json {
        let (name, entries): (&str, Entries) = match &value.core {
            StepCore::Hide { usable: used } => ("Hide", vec![("usable", Some(usable(used)))]),
            StepCore::Define { definitions } => (
                "Define",
                vec![("definitions", Some(list(definitions, defn)))],
            ),
            StepCore::Assert {
                sequent: asserted,
                proof: proved,
            } => (
                "Assert",
                vec![
                    ("sequent", Some(sequent(asserted))),
                    ("proof", Some(proof(proved))),
                ],
            ),
            StepCore::Suffices {
                sequent: asserted,
                proof: proved,
            } => (
                "Suffices",
                vec![
                    ("sequent", Some(sequent(asserted))),
                    ("proof", Some(proof(proved))),
                ],
            ),
            StepCore::Pcase {
                expression: case,
                proof: proved,
            } => (
                "Pcase",
                vec![
                    ("expression", Some(expression(case))),
                    ("proof", Some(proof(proved))),
                ],
            ),
            StepCore::Pick {
                bounds,
                expression: picked,
                proof: proved,
            } => (
                "Pick",
                vec![
                    ("bounds", Some(list(bounds, bound))),
                    ("expression", Some(expression(picked))),
                    ("proof", Some(proof(proved))),
                ],
            ),
            StepCore::Use {
                usable: used,
                is_only,
            } => (
                "Use",
                vec![
                    ("usable", Some(usable(used))),
                    ("isOnly", Some(Json::Bool(*is_only))),
                ],
            ),
            StepCore::Have { expression: had } => {
                ("Have", vec![("expression", Some(expression(had)))])
            }
            StepCore::Take { bounds } => ("Take", vec![("bounds", Some(list(bounds, bound)))]),
            StepCore::Witness { expressions: items } => {
                ("Witness", vec![("expressions", Some(expressions(items)))])
            }
            StepCore::Forget { count } => ("Forget", vec![("count", Some(number(*count)))]),
        };
        kind(name, with_props(entries, &value.props))
    }

    fn declarations(items: &[Declaration]) -> Json {
        list(items, |declaration| {
            object(vec![
                ("name", Some(text(&declaration.name))),
                ("shape", Some(number(declaration.shape))),
            ])
        })
    }

    fn unit(value: &ModuleUnit) -> Json {
        let (name, mut entries): (&str, Entries) = match &value.core {
            ModuleUnitCore::Constants {
                declarations: items,
            } => (
                "Constants",
                vec![("declarations", Some(declarations(items)))],
            ),
            ModuleUnitCore::Recursives {
                declarations: items,
            } => (
                "Recursives",
                vec![("declarations", Some(declarations(items)))],
            ),
            ModuleUnitCore::Variables { names } => {
                ("Variables", vec![("names", Some(strings(names)))])
            }
            ModuleUnitCore::Definition {
                definition,
                where_defined: defined,
                visibility,
                is_local,
            } => (
                "Definition",
                vec![
                    ("definition", Some(defn(definition))),
                    ("whereDefined", Some(where_defined(*defined))),
                    ("visibility", Some(debug(visibility))),
                    ("isLocal", Some(Json::Bool(*is_local))),
                ],
            ),
            ModuleUnitCore::Axiom {
                name,
                expression: axiom,
            } => (
                "Axiom",
                vec![
                    ("name", name.as_deref().map(text)),
                    ("expression", Some(expression(axiom))),
                ],
            ),
            ModuleUnitCore::Theorem {
                name,
                sequent: stated,
                axiom_count,
                proof: proved,
            } => (
                "Theorem",
                vec![
                    ("name", name.as_deref().map(text)),
                    ("sequent", Some(sequent(stated))),
                    ("axiomCount", Some(number(*axiom_count))),
                    ("proof", Some(proof(proved))),
                ],
            ),
            ModuleUnitCore::Submod { module } => ("Submod", vec![("module", Some(mule(module)))]),
            ModuleUnitCore::Mutate { mode, usable: used } => (
                "Mutate",
                vec![("mode", Some(debug(mode))), ("usable", Some(usable(used)))],
            ),
            ModuleUnitCore::Anoninst {
                instance: definition,
                is_local,
            } => (
                "Anoninst",
                vec![
                    ("instance", Some(instance(definition))),
                    ("isLocal", Some(Json::Bool(*is_local))),
                ],
            ),
        };
        entries.push(("location", value.location.as_ref().map(locus)));
        kind(name, entries)
    }

    fn mule(value: &Mule) -> Json {
        object(vec![
            ("name", Some(text(&value.name))),
            ("extendees", Some(strings(&value.extendees))),
            (
                "extendeeLocations",
                value
                    .extendee_locations
                    .as_deref()
                    .map(|items| list(items, locus)),
            ),
            ("body", Some(list(&value.body, unit))),
            ("isImportant", Some(Json::Bool(value.is_important))),
            ("isStandard", value.is_standard.then_some(Json::Bool(true))),
            ("depth", value.depth.map(number)),
            ("location", value.location.as_ref().map(locus)),
        ])
    }

    /// The canonical JSON of the conversion of a module named `M.tla`, or of its error.
    fn convert(source: &str, is_expanding: bool) -> String {
        let module = tla_front::parser::parse_tlapm_module(source, None).expect("parses");
        let counter = Rc::new(Counter::default());
        let json = match create_source("M.tla", source, counter.clone(), is_expanding)
            .convert_module(&module)
        {
            Ok(converted) => object(vec![
                ("mule", Some(mule(&converted))),
                ("counter", Some(number(counter.value.get()))),
            ]),
            Err(error) => {
                let (failure, exception) = match &error {
                    ObligationError::Proof {
                        failure, exception, ..
                    } => (failure.as_deref().map(text), Some(text(exception))),
                    _ => (None, None),
                };
                object(vec![(
                    "error",
                    Some(object(vec![
                        ("name", Some(text(error.name()))),
                        ("message", Some(text(error.message()))),
                        ("failure", failure),
                        ("exception", exception),
                    ])),
                )])
            }
        };
        let mut out = String::new();
        json.write(&mut out);
        out
    }

    /// The name of each case, its module, whether it expands tuples, and what Bun gives.
    const CASES: &[(&str, &str, bool, &str)] = &[
        (
            r"regroup",
            r##"---- MODULE M ----
A == SUBSET S \ T
B == UNION S \cup T /\ []P => Q
C == ENABLED x' \cdot y
D == -a + b * c
===="##,
            true,
            r##"{"counter":0,"mule":{"body":[{"definition":{"body":{"args":[{"args":[{"kind":"Opaque","location":{"endColumn":14,"endLine":2,"file":"M.tla","startColumn":13,"startLine":2},"name":"S"},{"kind":"Opaque","location":{"endColumn":18,"endLine":2,"file":"M.tla","startColumn":17,"startLine":2},"name":"T"}],"kind":"Apply","location":{"endColumn":18,"endLine":2,"file":"M.tla","startColumn":13,"startLine":2},"operator":{"builtin":"Setminus","kind":"Internal"}}],"kind":"Apply","location":{"endColumn":18,"endLine":2,"file":"M.tla","startColumn":6,"startLine":2},"operator":{"builtin":"SUBSET","kind":"Internal"}},"kind":"Operator","location":{"endColumn":18,"endLine":2,"file":"M.tla","startColumn":1,"startLine":2},"name":"A"},"isLocal":false,"kind":"Definition","location":{"endColumn":18,"endLine":2,"file":"M.tla","startColumn":1,"startLine":2},"visibility":"Hidden","whereDefined":"User"},{"definition":{"body":{"args":[{"args":[{"args":[{"args":[{"kind":"Opaque","location":{"endColumn":13,"endLine":3,"file":"M.tla","startColumn":12,"startLine":3},"name":"S"},{"kind":"Opaque","location":{"endColumn":20,"endLine":3,"file":"M.tla","startColumn":19,"startLine":3},"name":"T"}],"kind":"Apply","location":{"endColumn":20,"endLine":3,"file":"M.tla","startColumn":12,"startLine":3},"operator":{"builtin":"Cup","kind":"Internal"}}],"kind":"Apply","location":{"endColumn":20,"endLine":3,"file":"M.tla","startColumn":6,"startLine":3},"operator":{"builtin":"UNION","kind":"Internal"}},{"args":[{"kind":"Opaque","location":{"endColumn":27,"endLine":3,"file":"M.tla","startColumn":26,"startLine":3},"name":"P"}],"kind":"Apply","location":{"endColumn":27,"endLine":3,"file":"M.tla","startColumn":24,"startLine":3},"operator":{"builtin":"BoxTrue","kind":"Internal"}}],"kind":"Apply","location":{"endColumn":27,"endLine":3,"file":"M.tla","startColumn":6,"startLine":3},"operator":{"builtin":"Conj","kind":"Internal"}},{"kind":"Opaque","location":{"endColumn":32,"endLine":3,"file":"M.tla","startColumn":31,"startLine":3},"name":"Q"}],"kind":"Apply","location":{"endColumn":32,"endLine":3,"file":"M.tla","startColumn":6,"startLine":3},"operator":{"builtin":"Implies","kind":"Internal"}},"kind":"Operator","location":{"endColumn":32,"endLine":3,"file":"M.tla","startColumn":1,"startLine":3},"name":"B"},"isLocal":false,"kind":"Definition","location":{"endColumn":32,"endLine":3,"file":"M.tla","startColumn":1,"startLine":3},"visibility":"Hidden","whereDefined":"User"},{"definition":{"body":{"args":[{"args":[{"args":[{"kind":"Opaque","location":{"endColumn":15,"endLine":4,"file":"M.tla","startColumn":14,"startLine":4},"name":"x"}],"kind":"Apply","location":{"endColumn":15,"endLine":4,"file":"M.tla","startColumn":6,"startLine":4},"operator":{"builtin":"ENABLED","kind":"Internal"}}],"kind":"Apply","location":{"endColumn":16,"endLine":4,"file":"M.tla","startColumn":6,"startLine":4},"operator":{"builtin":"Prime","kind":"Internal"}},{"kind":"Opaque","location":{"endColumn":24,"endLine":4,"file":"M.tla","startColumn":23,"startLine":4},"name":"y"}],"kind":"Apply","location":{"endColumn":24,"endLine":4,"file":"M.tla","startColumn":6,"startLine":4},"operator":{"builtin":"Cdot","kind":"Internal"}},"kind":"Operator","location":{"endColumn":24,"endLine":4,"file":"M.tla","startColumn":1,"startLine":4},"name":"C"},"isLocal":false,"kind":"Definition","location":{"endColumn":24,"endLine":4,"file":"M.tla","startColumn":1,"startLine":4},"visibility":"Hidden","whereDefined":"User"},{"definition":{"body":{"args":[{"args":[{"kind":"Opaque","location":{"endColumn":8,"endLine":5,"file":"M.tla","startColumn":7,"startLine":5},"name":"a"}],"kind":"Apply","location":{"endColumn":8,"endLine":5,"file":"M.tla","startColumn":6,"startLine":5},"operator":{"kind":"Opaque","name":"-."}},{"args":[{"kind":"Opaque","location":{"endColumn":12,"endLine":5,"file":"M.tla","startColumn":11,"startLine":5},"name":"b"},{"kind":"Opaque","location":{"endColumn":16,"endLine":5,"file":"M.tla","startColumn":15,"startLine":5},"name":"c"}],"kind":"Apply","location":{"endColumn":16,"endLine":5,"file":"M.tla","startColumn":11,"startLine":5},"operator":{"kind":"Opaque","name":"*"}}],"kind":"Apply","location":{"endColumn":16,"endLine":5,"file":"M.tla","startColumn":6,"startLine":5},"operator":{"kind":"Opaque","name":"+"}},"kind":"Operator","location":{"endColumn":16,"endLine":5,"file":"M.tla","startColumn":1,"startLine":5},"name":"D"},"isLocal":false,"kind":"Definition","location":{"endColumn":16,"endLine":5,"file":"M.tla","startColumn":1,"startLine":5},"visibility":"Hidden","whereDefined":"User"}],"extendeeLocations":[],"extendees":[],"isImportant":false,"location":{"endColumn":5,"endLine":6,"file":"M.tla","startColumn":1,"startLine":1},"name":"M"}}"##,
        ),
        (
            r"expressions",
            r##"---- MODULE M ----
E == "😀\"" = 1.50 /\ \A x, y \in S, z \in S : x
F == [f EXCEPT ![1, 2].a = @, ![3] = {}] # [a |-> 1] \cup [b : S]
G == LET H(p) == p I == INSTANCE N IN CHOOSE v \in S : lab(v) :: v
J == CASE a -> {x \in S : x} [] OTHER -> {x : x \in S}
K == [][A]_v /\ <><<A>>_v /\ WF_v(A) /\ \EE w : LAMBDA q : q
L == G!lab(1)!<< /\ M!N!O
===="##,
            true,
            r##"{"counter":0,"mule":{"body":[{"definition":{"body":{"args":[{"args":[{"kind":"String","location":{"endColumn":12,"endLine":2,"file":"M.tla","startColumn":11,"startLine":2},"value":"😀\\\""},{"fraction":"50","integer":"1","kind":"Num","location":{"endColumn":19,"endLine":2,"file":"M.tla","startColumn":15,"startLine":2}}],"kind":"Apply","location":{"endColumn":19,"endLine":2,"file":"M.tla","startColumn":11,"startLine":2},"operator":{"builtin":"Eq","kind":"Internal"}},{"body":{"kind":"Opaque","location":{"endColumn":49,"endLine":2,"file":"M.tla","startColumn":48,"startLine":2},"name":"x"},"bounds":[{"domain":{"expression":{"kind":"Opaque","location":{"endColumn":36,"endLine":2,"file":"M.tla","startColumn":35,"startLine":2},"name":"S"},"kind":"Domain"},"level":"Constant","name":"x"},{"domain":{"kind":"Ditto"},"level":"Constant","name":"y"},{"domain":{"expression":{"kind":"Opaque","location":{"endColumn":45,"endLine":2,"file":"M.tla","startColumn":44,"startLine":2},"name":"S"},"kind":"Domain"},"level":"Constant","name":"z"}],"kind":"Quant","location":{"endColumn":49,"endLine":2,"file":"M.tla","startColumn":23,"startLine":2},"quantifier":"Forall"}],"kind":"Apply","location":{"endColumn":49,"endLine":2,"file":"M.tla","startColumn":11,"startLine":2},"operator":{"builtin":"Conj","kind":"Internal"}},"kind":"Operator","location":{"endColumn":49,"endLine":2,"file":"M.tla","startColumn":1,"startLine":2},"name":"E"},"isLocal":false,"kind":"Definition","location":{"endColumn":49,"endLine":2,"file":"M.tla","startColumn":1,"startLine":2},"visibility":"Hidden","whereDefined":"User"},{"definition":{"body":{"args":[{"function":{"kind":"Opaque","location":{"endColumn":8,"endLine":3,"file":"M.tla","startColumn":7,"startLine":3},"name":"f"},"kind":"Except","location":{"endColumn":41,"endLine":3,"file":"M.tla","startColumn":6,"startLine":3},"specs":[{"trail":[{"expression":{"elements":[{"fraction":"","integer":"1","kind":"Num","location":{"endColumn":19,"endLine":3,"file":"M.tla","startColumn":18,"startLine":3}},{"fraction":"","integer":"2","kind":"Num","location":{"endColumn":22,"endLine":3,"file":"M.tla","startColumn":21,"startLine":3}}],"kind":"Tuple"},"kind":"Apply"},{"field":"a","kind":"Dot"}],"value":{"isExcept":true,"kind":"At","location":{"endColumn":29,"endLine":3,"file":"M.tla","startColumn":28,"startLine":3}}},{"trail":[{"expression":{"fraction":"","integer":"3","kind":"Num","location":{"endColumn":34,"endLine":3,"file":"M.tla","startColumn":33,"startLine":3}},"kind":"Apply"}],"value":{"elements":[],"kind":"SetEnum","location":{"endColumn":40,"endLine":3,"file":"M.tla","startColumn":38,"startLine":3}}}]},{"args":[{"fields":[{"name":"a","value":{"fraction":"","integer":"1","kind":"Num","location":{"endColumn":52,"endLine":3,"file":"M.tla","startColumn":51,"startLine":3}}}],"kind":"Record","location":{"endColumn":53,"endLine":3,"file":"M.tla","startColumn":44,"startLine":3}},{"fields":[{"name":"b","value":{"kind":"Opaque","location":{"endColumn":65,"endLine":3,"file":"M.tla","startColumn":64,"startLine":3},"name":"S"}}],"kind":"Rect","location":{"endColumn":66,"endLine":3,"file":"M.tla","startColumn":59,"startLine":3}}],"kind":"Apply","location":{"endColumn":66,"endLine":3,"file":"M.tla","startColumn":44,"startLine":3},"operator":{"builtin":"Cup","kind":"Internal"}}],"kind":"Apply","location":{"endColumn":66,"endLine":3,"file":"M.tla","startColumn":6,"startLine":3},"operator":{"builtin":"Neq","kind":"Internal"}},"kind":"Operator","location":{"endColumn":66,"endLine":3,"file":"M.tla","startColumn":1,"startLine":3},"name":"F"},"isLocal":false,"kind":"Definition","location":{"endColumn":66,"endLine":3,"file":"M.tla","startColumn":1,"startLine":3},"visibility":"Hidden","whereDefined":"User"},{"definition":{"body":{"body":{"body":{"expression":{"kind":"Opaque","location":{"endColumn":67,"endLine":4,"file":"M.tla","startColumn":66,"startLine":4},"name":"v"},"form":{"kind":"Nlabel","label":"lab","names":["v"]},"kind":"Parens","location":{"endColumn":67,"endLine":4,"file":"M.tla","startColumn":56,"startLine":4}},"domain":{"kind":"Opaque","location":{"endColumn":53,"endLine":4,"file":"M.tla","startColumn":52,"startLine":4},"name":"S"},"kind":"Choose","location":{"endColumn":67,"endLine":4,"file":"M.tla","startColumn":39,"startLine":4},"name":"v"},"definitions":[{"body":{"body":{"kind":"Opaque","location":{"endColumn":19,"endLine":4,"file":"M.tla","startColumn":18,"startLine":4},"name":"p"},"kind":"Lambda","location":{"endColumn":19,"endLine":4,"file":"M.tla","startColumn":10,"startLine":4},"params":[{"location":{"endColumn":13,"endLine":4,"file":"M.tla","startColumn":12,"startLine":4},"name":"p","shape":0}]},"kind":"Operator","location":{"endColumn":19,"endLine":4,"file":"M.tla","startColumn":10,"startLine":4},"name":"H"},{"instance":{"args":[],"location":{"endColumn":35,"endLine":4,"file":"M.tla","startColumn":22,"startLine":4},"module":"N","substitutions":[]},"kind":"Instance","location":{"endColumn":35,"endLine":4,"file":"M.tla","startColumn":20,"startLine":4},"name":"I"}],"kind":"Let","location":{"endColumn":67,"endLine":4,"file":"M.tla","startColumn":6,"startLine":4}},"kind":"Operator","location":{"endColumn":67,"endLine":4,"file":"M.tla","startColumn":1,"startLine":4},"name":"G"},"isLocal":false,"kind":"Definition","location":{"endColumn":67,"endLine":4,"file":"M.tla","startColumn":1,"startLine":4},"visibility":"Hidden","whereDefined":"User"},{"definition":{"body":{"arms":[{"body":{"body":{"kind":"Opaque","location":{"endColumn":28,"endLine":5,"file":"M.tla","startColumn":27,"startLine":5},"name":"x"},"domain":{"kind":"Opaque","location":{"endColumn":24,"endLine":5,"file":"M.tla","startColumn":23,"startLine":5},"name":"S"},"kind":"SetSt","location":{"endColumn":29,"endLine":5,"file":"M.tla","startColumn":16,"startLine":5},"name":"x"},"condition":{"kind":"Opaque","location":{"endColumn":12,"endLine":5,"file":"M.tla","startColumn":11,"startLine":5},"name":"a"}}],"kind":"Case","location":{"endColumn":55,"endLine":5,"file":"M.tla","startColumn":6,"startLine":5},"other":{"bounds":[{"domain":{"expression":{"kind":"Opaque","location":{"endColumn":54,"endLine":5,"file":"M.tla","startColumn":53,"startLine":5},"name":"S"},"kind":"Domain"},"level":"Constant","name":"x"}],"element":{"kind":"Opaque","location":{"endColumn":44,"endLine":5,"file":"M.tla","startColumn":43,"startLine":5},"name":"x"},"kind":"SetOf","location":{"endColumn":55,"endLine":5,"file":"M.tla","startColumn":42,"startLine":5}}},"kind":"Operator","location":{"endColumn":55,"endLine":5,"file":"M.tla","startColumn":1,"startLine":5},"name":"J"},"isLocal":false,"kind":"Definition","location":{"endColumn":55,"endLine":5,"file":"M.tla","startColumn":1,"startLine":5},"visibility":"Hidden","whereDefined":"User"},{"definition":{"body":{"args":[{"args":[{"args":[{"action":{"kind":"Opaque","location":{"endColumn":10,"endLine":6,"file":"M.tla","startColumn":9,"startLine":6},"name":"A"},"kind":"Tsub","location":{"endColumn":13,"endLine":6,"file":"M.tla","startColumn":6,"startLine":6},"modal":"Box","subscript":{"kind":"Opaque","location":{"endColumn":13,"endLine":6,"file":"M.tla","startColumn":12,"startLine":6},"name":"v"}},{"action":{"kind":"Opaque","location":{"endColumn":22,"endLine":6,"file":"M.tla","startColumn":21,"startLine":6},"name":"A"},"kind":"Tsub","location":{"endColumn":26,"endLine":6,"file":"M.tla","startColumn":17,"startLine":6},"modal":"Dia","subscript":{"kind":"Opaque","location":{"endColumn":26,"endLine":6,"file":"M.tla","startColumn":25,"startLine":6},"name":"v"}}],"kind":"Apply","location":{"endColumn":26,"endLine":6,"file":"M.tla","startColumn":6,"startLine":6},"operator":{"builtin":"Conj","kind":"Internal"}},{"action":{"kind":"Opaque","location":{"endColumn":36,"endLine":6,"file":"M.tla","startColumn":35,"startLine":6},"name":"A"},"fairness":"Weak","kind":"Fair","location":{"endColumn":37,"endLine":6,"file":"M.tla","startColumn":30,"startLine":6},"subscript":{"kind":"Opaque","location":{"endColumn":34,"endLine":6,"file":"M.tla","startColumn":33,"startLine":6},"name":"v"}}],"kind":"Apply","location":{"endColumn":37,"endLine":6,"file":"M.tla","startColumn":6,"startLine":6},"operator":{"builtin":"Conj","kind":"Internal"}},{"body":{"body":{"kind":"Opaque","location":{"endColumn":61,"endLine":6,"file":"M.tla","startColumn":60,"startLine":6},"name":"q"},"kind":"Lambda","location":{"endColumn":61,"endLine":6,"file":"M.tla","startColumn":49,"startLine":6},"params":[{"name":"q","shape":0}]},"kind":"Tquant","location":{"endColumn":61,"endLine":6,"file":"M.tla","startColumn":41,"startLine":6},"names":["w"],"quantifier":"Exists"}],"kind":"Apply","location":{"endColumn":61,"endLine":6,"file":"M.tla","startColumn":6,"startLine":6},"operator":{"builtin":"Conj","kind":"Internal"}},"kind":"Operator","location":{"endColumn":61,"endLine":6,"file":"M.tla","startColumn":1,"startLine":6},"name":"K"},"isLocal":false,"kind":"Definition","location":{"endColumn":61,"endLine":6,"file":"M.tla","startColumn":1,"startLine":6},"visibility":"Hidden","whereDefined":"User"},{"definition":{"body":{"args":[{"expression":{"kind":"Opaque","location":{"endColumn":17,"endLine":7,"file":"M.tla","startColumn":6,"startLine":7},"name":"G"},"kind":"Bang","location":{"endColumn":17,"endLine":7,"file":"M.tla","startColumn":6,"startLine":7},"selectors":[{"args":[{"fraction":"","integer":"1","kind":"Num","location":{"endColumn":13,"endLine":7,"file":"M.tla","startColumn":12,"startLine":7}}],"kind":"Label","label":"lab"},{"kind":"Left"}]},{"expression":{"kind":"Opaque","location":{"endColumn":26,"endLine":7,"file":"M.tla","startColumn":21,"startLine":7},"name":"M"},"kind":"Bang","location":{"endColumn":26,"endLine":7,"file":"M.tla","startColumn":21,"startLine":7},"selectors":[{"args":[],"kind":"Label","label":"N"},{"args":[],"kind":"Label","label":"O"}]}],"kind":"Apply","location":{"endColumn":26,"endLine":7,"file":"M.tla","startColumn":6,"startLine":7},"operator":{"builtin":"Conj","kind":"Internal"}},"kind":"Operator","location":{"endColumn":26,"endLine":7,"file":"M.tla","startColumn":1,"startLine":7},"name":"L"},"isLocal":false,"kind":"Definition","location":{"endColumn":26,"endLine":7,"file":"M.tla","startColumn":1,"startLine":7},"visibility":"Hidden","whereDefined":"User"}],"extendeeLocations":[],"extendees":[],"isImportant":false,"location":{"endColumn":5,"endLine":8,"file":"M.tla","startColumn":1,"startLine":1},"name":"M"}}"##,
        ),
        (
            r"proof",
            r##"---- MODULE M ----
VARIABLE x
f(a) == a (*{ by (prover:"smt"; timeout:5) }*)
THEOREM T == ASSUME NEW c \in S, NEW VARIABLE v, h :: c PROVE c (*{ by (zenon) }*)
<1>1. SUFFICES c OBVIOUS
<1> DEFINE g == 1
<1>a CASE c BY <1>1 DEF f
<1> PICK y \in S : y OMITTED
<1> USE ONLY <1>1 DEF f
<1> HIDE DEF f
<1> QED BY T (*{ by (isabelle "auto") }*)
===="##,
            true,
            r##"{"counter":5,"mule":{"body":[{"kind":"Variables","location":{"endColumn":11,"endLine":2,"file":"M.tla","startColumn":10,"startLine":2},"names":["x"]},{"definition":{"body":{"body":{"kind":"Opaque","location":{"endColumn":10,"endLine":3,"file":"M.tla","startColumn":9,"startLine":3},"name":"a"},"kind":"Lambda","location":{"endColumn":10,"endLine":3,"file":"M.tla","startColumn":1,"startLine":3},"params":[{"location":{"endColumn":4,"endLine":3,"file":"M.tla","startColumn":3,"startLine":3},"name":"a","shape":0}]},"kind":"Bpragma","location":{"endColumn":10,"endLine":3,"file":"M.tla","startColumn":1,"startLine":3},"methods":[[{"hint":"prover","value":{"kind":"String","value":"smt"}},{"hint":"timeout","value":{"kind":"Float","value":5}}]],"name":"f"},"isLocal":false,"kind":"Definition","location":{"endColumn":10,"endLine":3,"file":"M.tla","startColumn":1,"startLine":3},"visibility":"Hidden","whereDefined":"User"},{"axiomCount":0,"kind":"Theorem","location":{"endColumn":13,"endLine":11,"file":"M.tla","startColumn":1,"startLine":4},"name":"T","proof":{"kind":"Steps","location":{"endColumn":11,"endLine":11,"file":"M.tla","startColumn":1,"startLine":5},"qed":{"location":{"endColumn":11,"endLine":11,"file":"M.tla","startColumn":1,"startLine":11},"proof":{"isOnly":false,"kind":"By","location":{"endColumn":11,"endLine":11,"file":"M.tla","startColumn":9,"startLine":11},"method":{"name":"isabelle","tactic":"auto"},"step":{"id":0,"kind":"Unnamed","level":2},"usable":{"defs":[],"facts":[{"kind":"Opaque","location":{"endColumn":13,"endLine":11,"file":"M.tla","startColumn":12,"startLine":11},"name":"T"}]}},"step":{"id":5,"kind":"Unnamed","level":1}},"step":{"id":5,"kind":"Unnamed","level":1},"steps":[{"kind":"Suffices","location":{"endColumn":25,"endLine":5,"file":"M.tla","startColumn":1,"startLine":5},"proof":{"kind":"Obvious","location":{"endColumn":25,"endLine":5,"file":"M.tla","startColumn":18,"startLine":5}},"sequent":{"active":{"kind":"Opaque","location":{"endColumn":17,"endLine":5,"file":"M.tla","startColumn":16,"startLine":5},"name":"c"},"context":[]},"step":{"isAnonymous":false,"kind":"Named","label":"1","level":1}},{"definitions":[{"body":{"fraction":"","integer":"1","kind":"Num","location":{"endColumn":18,"endLine":6,"file":"M.tla","startColumn":17,"startLine":6}},"kind":"Operator","location":{"endColumn":18,"endLine":6,"file":"M.tla","startColumn":12,"startLine":6},"name":"g"}],"kind":"Define","location":{"endColumn":18,"endLine":6,"file":"M.tla","startColumn":1,"startLine":6},"step":{"id":1,"kind":"Unnamed","level":1}},{"expression":{"kind":"Opaque","location":{"endColumn":12,"endLine":7,"file":"M.tla","startColumn":11,"startLine":7},"name":"c"},"kind":"Pcase","location":{"endColumn":15,"endLine":7,"file":"M.tla","startColumn":1,"startLine":7},"proof":{"isOnly":false,"kind":"By","location":{"endColumn":15,"endLine":7,"file":"M.tla","startColumn":13,"startLine":7},"step":{"id":0,"kind":"Unnamed","level":2},"usable":{"defs":[{"kind":"Dvar","location":{"endColumn":26,"endLine":7,"file":"M.tla","startColumn":25,"startLine":7},"name":"f"}],"facts":[{"kind":"Opaque","location":{"endColumn":20,"endLine":7,"file":"M.tla","startColumn":16,"startLine":7},"name":"<1>1"}]}},"step":{"isAnonymous":false,"kind":"Named","label":"a","level":1}},{"bounds":[{"domain":{"expression":{"kind":"Opaque","location":{"endColumn":17,"endLine":8,"file":"M.tla","startColumn":16,"startLine":8},"name":"S"},"kind":"Domain"},"level":"Constant","name":"y"}],"expression":{"kind":"Opaque","location":{"endColumn":21,"endLine":8,"file":"M.tla","startColumn":20,"startLine":8},"name":"y"},"kind":"Pick","location":{"endColumn":29,"endLine":8,"file":"M.tla","startColumn":1,"startLine":8},"proof":{"kind":"Omitted","location":{"endColumn":29,"endLine":8,"file":"M.tla","startColumn":22,"startLine":8},"omission":"Explicit"},"step":{"id":2,"kind":"Unnamed","level":1}},{"isOnly":true,"kind":"Use","location":{"endColumn":24,"endLine":9,"file":"M.tla","startColumn":1,"startLine":9},"step":{"id":3,"kind":"Unnamed","level":1},"usable":{"defs":[{"kind":"Dvar","location":{"endColumn":24,"endLine":9,"file":"M.tla","startColumn":23,"startLine":9},"name":"f"}],"facts":[{"kind":"Opaque","location":{"endColumn":18,"endLine":9,"file":"M.tla","startColumn":14,"startLine":9},"name":"<1>1"}]}},{"kind":"Hide","location":{"endColumn":15,"endLine":10,"file":"M.tla","startColumn":1,"startLine":10},"step":{"id":4,"kind":"Unnamed","level":1},"usable":{"defs":[{"kind":"Dvar","location":{"endColumn":15,"endLine":10,"file":"M.tla","startColumn":14,"startLine":10},"name":"f"}],"facts":[]}}]},"sequent":{"active":{"expression":{"kind":"Opaque","location":{"endColumn":64,"endLine":4,"file":"M.tla","startColumn":63,"startLine":4},"name":"c"},"kind":"With","location":{"endColumn":64,"endLine":4,"file":"M.tla","startColumn":63,"startLine":4},"method":{"name":"zenon"}},"context":[{"domain":{"kind":"Opaque","location":{"endColumn":32,"endLine":4,"file":"M.tla","startColumn":31,"startLine":4},"name":"S"},"domainVisibility":"Visible","kind":"Fresh","level":"Constant","location":{"endColumn":32,"endLine":4,"file":"M.tla","startColumn":21,"startLine":4},"name":"c","shape":0},{"kind":"Flex","location":{"endColumn":48,"endLine":4,"file":"M.tla","startColumn":34,"startLine":4},"name":"v"},{"expression":{"expression":{"kind":"Opaque","location":{"endColumn":56,"endLine":4,"file":"M.tla","startColumn":55,"startLine":4},"name":"c"},"form":{"indices":[],"kind":"Xlabel","label":"h"},"kind":"Parens","location":{"endColumn":56,"endLine":4,"file":"M.tla","startColumn":50,"startLine":4}},"kind":"Fact","location":{"endColumn":56,"endLine":4,"file":"M.tla","startColumn":50,"startLine":4},"time":"Now","visibility":"Visible"}]}}],"extendeeLocations":[],"extendees":[],"isImportant":false,"location":{"endColumn":5,"endLine":12,"file":"M.tla","startColumn":1,"startLine":1},"name":"M"}}"##,
        ),
        (
            r"tuples",
            r##"---- MODULE M ----
P == \A <<a, b>> \in S \X T : a
===="##,
            true,
            r##"{"counter":0,"mule":{"body":[{"definition":{"body":{"body":{"kind":"Opaque","location":{"endColumn":32,"endLine":2,"file":"M.tla","startColumn":31,"startLine":2},"name":"a"},"bounds":[{"domain":{"expression":{"kind":"Opaque","location":{"endColumn":23,"endLine":2,"file":"M.tla","startColumn":22,"startLine":2},"name":"S"},"kind":"Domain"},"level":"Constant","name":"a"},{"domain":{"expression":{"kind":"Opaque","location":{"endColumn":28,"endLine":2,"file":"M.tla","startColumn":27,"startLine":2},"name":"T"},"kind":"Domain"},"level":"Constant","name":"b"}],"kind":"Quant","location":{"endColumn":32,"endLine":2,"file":"M.tla","startColumn":6,"startLine":2},"quantifier":"Forall"},"kind":"Operator","location":{"endColumn":32,"endLine":2,"file":"M.tla","startColumn":1,"startLine":2},"name":"P"},"isLocal":false,"kind":"Definition","location":{"endColumn":32,"endLine":2,"file":"M.tla","startColumn":1,"startLine":2},"visibility":"Hidden","whereDefined":"User"}],"extendeeLocations":[],"extendees":[],"isImportant":false,"location":{"endColumn":5,"endLine":3,"file":"M.tla","startColumn":1,"startLine":1},"name":"M"}}"##,
        ),
        (
            r"tuples",
            r##"---- MODULE M ----
P == \A <<a, b>> \in S \X T : a
===="##,
            false,
            r##"{"error":{"exception":"Failure(\"use instead the class`E_visit.iter_concrete`\")","failure":"use instead the class`E_visit.iter_concrete`","message":"Unexpected tuple declaration","name":"TlaProofError"}}"##,
        ),
        (
            r"units",
            r##"---- MODULE M ----
EXTENDS Naturals, Sequences
CONSTANTS C, D(_)
RECURSIVE R(_)
R(n) == R(n)
I == INSTANCE N WITH a <- 1
INSTANCE N
LOCAL L == 1
ASSUME A == C
---- MODULE Sub ----
USE DEF L
====
===="##,
            true,
            r##"{"counter":0,"mule":{"body":[{"declarations":[{"name":"C","shape":0},{"name":"D","shape":1}],"kind":"Constants","location":{"endColumn":12,"endLine":3,"file":"M.tla","startColumn":11,"startLine":3}},{"declarations":[{"name":"R","shape":1}],"kind":"Recursives","location":{"endColumn":15,"endLine":4,"file":"M.tla","startColumn":11,"startLine":4}},{"definition":{"body":{"body":{"args":[{"kind":"Opaque","location":{"endColumn":12,"endLine":5,"file":"M.tla","startColumn":11,"startLine":5},"name":"n"}],"kind":"Apply","location":{"endColumn":13,"endLine":5,"file":"M.tla","startColumn":9,"startLine":5},"operator":{"kind":"Opaque","location":{"endColumn":13,"endLine":5,"file":"M.tla","startColumn":9,"startLine":5},"name":"R"}},"kind":"Lambda","location":{"endColumn":13,"endLine":5,"file":"M.tla","startColumn":1,"startLine":5},"params":[{"location":{"endColumn":4,"endLine":5,"file":"M.tla","startColumn":3,"startLine":5},"name":"n","shape":0}]},"kind":"Operator","location":{"endColumn":13,"endLine":5,"file":"M.tla","startColumn":1,"startLine":5},"name":"R"},"isLocal":false,"kind":"Definition","location":{"endColumn":13,"endLine":5,"file":"M.tla","startColumn":1,"startLine":5},"visibility":"Hidden","whereDefined":"User"},{"definition":{"instance":{"args":[],"location":{"endColumn":28,"endLine":6,"file":"M.tla","startColumn":3,"startLine":6},"module":"N","substitutions":[{"expression":{"fraction":"","integer":"1","kind":"Num","location":{"endColumn":28,"endLine":6,"file":"M.tla","startColumn":27,"startLine":6}},"name":"a"}]},"kind":"Instance","location":{"endColumn":28,"endLine":6,"file":"M.tla","startColumn":1,"startLine":6},"name":"I"},"isLocal":false,"kind":"Definition","location":{"endColumn":28,"endLine":6,"file":"M.tla","startColumn":6,"startLine":6},"visibility":"Hidden","whereDefined":"User"},{"instance":{"args":[],"location":{"endColumn":11,"endLine":7,"file":"M.tla","startColumn":1,"startLine":7},"module":"N","substitutions":[]},"isLocal":false,"kind":"Anoninst","location":{"endColumn":11,"endLine":7,"file":"M.tla","startColumn":1,"startLine":7}},{"definition":{"body":{"fraction":"","integer":"1","kind":"Num","location":{"endColumn":13,"endLine":8,"file":"M.tla","startColumn":12,"startLine":8}},"kind":"Operator","location":{"endColumn":13,"endLine":8,"file":"M.tla","startColumn":1,"startLine":8},"name":"L"},"isLocal":true,"kind":"Definition","location":{"endColumn":13,"endLine":8,"file":"M.tla","startColumn":1,"startLine":8},"visibility":"Hidden","whereDefined":"User"},{"expression":{"kind":"Opaque","location":{"endColumn":14,"endLine":9,"file":"M.tla","startColumn":13,"startLine":9},"name":"C"},"kind":"Axiom","location":{"endColumn":14,"endLine":9,"file":"M.tla","startColumn":1,"startLine":9},"name":"A"},{"kind":"Submod","module":{"body":[{"kind":"Mutate","location":{"endColumn":10,"endLine":11,"file":"M.tla","startColumn":1,"startLine":11},"mode":"Use","usable":{"defs":[{"kind":"Dvar","location":{"endColumn":10,"endLine":11,"file":"M.tla","startColumn":9,"startLine":11},"name":"L"}],"facts":[]}}],"extendeeLocations":[],"extendees":[],"isImportant":true,"location":{"endColumn":5,"endLine":12,"file":"M.tla","startColumn":1,"startLine":10},"name":"Sub"}}],"extendeeLocations":[{"endColumn":17,"endLine":2,"file":"M.tla","startColumn":9,"startLine":2},{"endColumn":28,"endLine":2,"file":"M.tla","startColumn":19,"startLine":2}],"extendees":["Naturals","Sequences"],"isImportant":false,"location":{"endColumn":5,"endLine":13,"file":"M.tla","startColumn":1,"startLine":1},"name":"M"}}"##,
        ),
        (
            r"moduleFact",
            r##"---- MODULE M ----
THEOREM 1 BY MODULE Naturals
===="##,
            true,
            r##"{"error":{"message":"MODULE facts in proof obligations are not supported","name":"TlaUnsupportedError"}}"##,
        ),
    ];

    #[test]
    fn converts_modules_as_the_typescript_does() {
        for (name, source, is_expanding, expected) in CASES {
            assert_eq!(
                convert(source, *is_expanding),
                *expected,
                "{name} {is_expanding}"
            );
        }
    }

    #[test]
    fn finds_written_strings_as_the_regular_expression_does() {
        let cases = [
            (r#"x = "a\"b""#, Some(r#"a\"b"#)),
            (r#""a" = "b""#, Some("b")),
            (r#"x = "a\""#, None),
            (r#"x = ""#, None),
            (r#""""#, Some("")),
            ("\"a\\\nb\"", None),
            ("\"a\rb\"", Some("a\rb")),
            ("no quote", None),
        ];
        for (text, expected) in cases {
            let units: Vec<u16> = text.encode_utf16().collect();
            assert_eq!(get_written_string(&units).as_deref(), expected, "{text:?}");
        }
    }

    #[test]
    fn matches_step_tokens_as_the_regular_expression_does() {
        let cases = [
            ("<1>1.", Some(("1", "1"))),
            ("<12>a_b..", Some(("12", "a_b"))),
            ("<*>", Some(("*", ""))),
            ("<+>.", Some(("+", ""))),
            ("<1>a.b", None),
            ("<>1", None),
            ("<x>1", None),
            ("1>1", None),
        ];
        for (token, expected) in cases {
            let matched = match_step_token(token);
            assert_eq!(
                matched
                    .as_ref()
                    .map(|token| (token.level.as_str(), token.label.as_str())),
                expected,
                "{token}"
            );
        }
    }
}
