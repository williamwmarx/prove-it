//! The expressions of `generateModule` (`generator.ts` lines 1159–1815): junctions, CASE, EXCEPT,
//! records, LET, CHOOSE, `generateExpression`, bounds, labels and the parameters and spans of
//! definitions.

use std::rc::Rc;

use crate::ast::{
    Bound, BoundPattern, Declaration, Definition, DefinitionKind, ExceptPathStep, Expr,
    ExpressionKind, Instance, Location, Name, OperatorParam, Position, Quantifier, SourceRange,
};
use crate::lexer::TokenKind;
use crate::sany::nodes::{Decimal, DefKind, Label, LetIn, NodeId, NodeKind, SanyLocation};
use crate::sany::source::{
    TokenSpan, find_name_tokens, find_token, get_expression_span, get_matching_index,
    get_parenthesized_span, get_span_location, get_token_index, get_token_location,
    get_token_source, is_token,
};
use crate::sany::{Result, not_yet};

use super::{
    BoundSymbols, LabelGoal, LocalContext, ModuleGenerator, OpApplBinding, get_bound_groups,
    get_numeral_digits, get_operator_node_kind, is_identifier, is_selector, resolve_synonym,
};

/// `LetUnit`: a unit of a LET, in source order.
#[derive(Clone, Debug)]
pub(super) enum LetUnit {
    Recursive(Vec<Rc<Declaration>>),
    Instance(Rc<Instance>),
    Definition(Rc<Definition>),
}

/// What `getUnresolvedOperator` finds: an infix, prefix or postfix operator that no symbol
/// defines, with the token SANY names it by. `fixity` is "prefix", "infix" or "postfix".
#[derive(Clone, Debug)]
pub(super) struct UnresolvedOperator {
    pub(super) index: usize,
    pub(super) name: String,
    pub(super) fixity: &'static str,
}

/// The largest mantissa SANY's DecimalNode keeps as a long.
const LONG_MAX: &str = "9223372036854775807";

/// The `Decimal` case of `generateExpression`: the mantissa `BigInt(integralPart +
/// fractionalPart)` writes, and its exponent, negative where the mantissa fits in a long.
fn get_decimal_parts(integral_part: &str, fractional_part: &str) -> (String, String) {
    let digits = format!("{integral_part}{fractional_part}");
    let trimmed = digits.trim_start_matches('0');
    let mantissa = if trimmed.is_empty() { "0" } else { trimmed };
    let is_long = (mantissa.len(), mantissa) <= (LONG_MAX.len(), LONG_MAX);
    let length = fractional_part.len();
    let exponent = if is_long && length > 0 {
        format!("-{length}")
    } else {
        length.to_string()
    };
    (mantissa.to_owned(), exponent)
}

impl ModuleGenerator<'_> {
    /// `generateJunction` (generator.ts 1159–1180): A /\ B /\ C nests as ((A /\ B) /\ C) in
    /// SANY, and the parser flattens it. `expression` is a `Junction`.
    pub(super) fn generate_junction(&mut self, expression: &Expr) -> Result<NodeId> {
        let ExpressionKind::Junction {
            is_and,
            operands,
            is_bulleted,
            ..
        } = &expression.kind
        else {
            return not_yet("Expected a junction");
        };
        let location = self.get_location(expression);
        if *is_bulleted {
            let nodes = operands
                .iter()
                .map(|operand| self.generate_expression(operand))
                .collect::<Result<Vec<_>>>()?;
            let name = if *is_and { "$ConjList" } else { "$DisjList" };
            return Ok(self.apply_builtin(name, nodes, location, OpApplBinding::default()));
        }
        let file = self.file.clone();
        let span = get_expression_span(&file, expression);
        let name = if *is_and { "\\land" } else { "\\lor" };
        let Some((first, rest)) = operands.split_first() else {
            return not_yet("Expected a junction with operands");
        };
        let mut left = self.generate_expression(first)?;
        for (index, operand) in rest.iter().enumerate() {
            let operand_span = get_parenthesized_span(&file, get_expression_span(&file, operand));
            let end = if index == rest.len() - 1 {
                span.end
            } else {
                operand_span.end
            };
            let right = self.generate_expression(operand)?;
            left = self.apply_builtin(
                name,
                [left, right],
                get_span_location(
                    &file,
                    TokenSpan {
                        start: span.start,
                        end,
                    },
                ),
                OpApplBinding::default(),
            );
        }
        Ok(left)
    }

    /// `generateCase` (generator.ts 1182–1208). `expression` is a `Case`.
    pub(super) fn generate_case(&mut self, expression: &Expr) -> Result<NodeId> {
        let ExpressionKind::Case { arms, other } = &expression.kind else {
            return not_yet("Expected a CASE");
        };
        let file = self.file.clone();
        let span = get_expression_span(&file, expression);
        let mut pairs: Vec<NodeId> = Vec::new();
        for (index, arm) in arms.iter().enumerate() {
            let condition =
                get_parenthesized_span(&file, get_expression_span(&file, &arm.condition));
            let is_last = index == arms.len() - 1 && other.is_none();
            let body = get_parenthesized_span(&file, get_expression_span(&file, &arm.body));
            let operands = [
                self.generate_expression(&arm.condition)?,
                self.generate_expression(&arm.body)?,
            ];
            let end = if is_last { span.end } else { body.end };
            pairs.push(self.apply_builtin(
                "$Pair",
                operands,
                get_span_location(
                    &file,
                    TokenSpan {
                        start: condition.start,
                        end,
                    },
                ),
                OpApplBinding::default(),
            ));
        }
        if let Some(other) = other {
            let body = get_parenthesized_span(&file, get_expression_span(&file, other));
            let other_index = self.find_token_before(body.start, "OTHER");
            let value = self.generate_expression(other)?;
            pairs.push(self.apply_builtin(
                "$Pair",
                [None, Some(value)],
                get_span_location(
                    &file,
                    TokenSpan {
                        start: other_index,
                        end: span.end,
                    },
                ),
                OpApplBinding::default(),
            ));
        }
        Ok(self.apply_builtin(
            "$Case",
            pairs,
            get_span_location(&file, span),
            OpApplBinding::default(),
        ))
    }

    /// `findTokenBefore` (generator.ts 1210–1215).
    pub(super) fn find_token_before(&self, index: usize, text: &str) -> usize {
        (0..=index)
            .rev()
            .find(|&current| is_token(&self.file, current, text))
            .unwrap_or(index)
    }

    /// `generateExcept` (generator.ts 1217–1256). `expression` is an `Except`.
    pub(super) fn generate_except(&mut self, expression: &Expr) -> Result<NodeId> {
        let ExpressionKind::Except { function, updates } = &expression.kind else {
            return not_yet("Expected an EXCEPT");
        };
        let file = self.file.clone();
        let span = get_expression_span(&file, expression);
        let location = get_span_location(&file, span);
        let function_node = self.generate_expression(function)?;
        let except_node = self.apply_builtin(
            "$Except",
            [function_node],
            location,
            OpApplBinding::default(),
        );
        let function_span = get_expression_span(&file, function);
        let mut cursor = find_token(&file, function_span.end + 1, span.end, "EXCEPT")
            .map_or(0, |index| index + 1);
        for update in updates {
            let Some(bang) = find_token(&file, cursor, span.end, "!") else {
                return not_yet("Expected ! in an EXCEPT");
            };
            let value_span =
                get_parenthesized_span(&file, get_expression_span(&file, &update.value));
            let spec_location = get_span_location(
                &file,
                TokenSpan {
                    start: bang,
                    end: value_span.end,
                },
            );
            let mut path_cursor = bang + 1;
            let mut components = Vec::new();
            for step in &update.path {
                let component = match step {
                    ExceptPathStep::Field(name) => {
                        let name_index = self.find_name_or_keyword(path_cursor, name);
                        path_cursor = name_index + 1;
                        self.create_string(name, get_token_location(&file, name_index))
                    }
                    ExceptPathStep::Index(args) => {
                        let Some(open) = find_token(&file, path_cursor, span.end, "[") else {
                            return not_yet("Expected [ in an EXCEPT");
                        };
                        let close = get_matching_index(&file, open);
                        path_cursor = close + 1;
                        if let [argument] = args.as_slice() {
                            self.generate_expression(argument)?
                        } else {
                            let nodes = args
                                .iter()
                                .map(|argument| self.generate_expression(argument))
                                .collect::<Result<Vec<_>>>()?;
                            self.apply_builtin(
                                "$Tuple",
                                nodes,
                                get_span_location(
                                    &file,
                                    TokenSpan {
                                        start: open,
                                        end: close,
                                    },
                                ),
                                OpApplBinding::default(),
                            )
                        }
                    }
                };
                components.push(component);
            }
            let sequence = self.apply_builtin(
                "$Seq",
                components,
                spec_location.clone(),
                OpApplBinding::default(),
            );
            let pair =
                self.apply_builtin("$Pair", [sequence], spec_location, OpApplBinding::default());
            self.except_spec_stack.push(pair);
            self.except_stack.push(except_node);
            let value = self.generate_expression(&update.value)?;
            self.push_operand(pair, value);
            self.except_spec_stack.pop();
            self.except_stack.pop();
            self.push_operand(except_node, pair);
            cursor = value_span.end + 1;
        }
        Ok(except_node)
    }

    /// `node.operands.push(operand)` of an OpAppl, whose operands the TypeScript shares.
    fn push_operand(&mut self, node: NodeId, operand: NodeId) {
        if let NodeKind::OpAppl(application) = &mut self.spec.graph.node_mut(node).kind {
            application.operands.push(Some(operand));
        }
    }

    /// `findNameOrKeyword` (generator.ts 1258–1263).
    pub(super) fn find_name_or_keyword(&self, start: usize, name: &str) -> usize {
        self.file
            .tokens
            .iter()
            .enumerate()
            .skip(start)
            .find(|(_, token)| &*token.text == name && token.kind != TokenKind::String)
            .map_or(start, |(index, _)| index)
    }

    /// `generateRecordFields` (generator.ts 1265–1290): `operator` is "$RcdConstructor" or
    /// "$SetOfRcds", and `expression` a `Record`.
    pub(super) fn generate_record_fields(
        &mut self,
        operator: &str,
        expression: &Expr,
    ) -> Result<NodeId> {
        let ExpressionKind::Record { fields, .. } = &expression.kind else {
            return not_yet("Expected a record");
        };
        let file = self.file.clone();
        let span = get_expression_span(&file, expression);
        let mut cursor = span.start + 1;
        let mut pairs = Vec::new();
        for (field_index, field) in fields.iter().enumerate() {
            let name_index = self.find_name_or_keyword(cursor, &field.name);
            let value_span =
                get_parenthesized_span(&file, get_expression_span(&file, &field.value));
            cursor = value_span.end + 1;
            if fields[..field_index]
                .iter()
                .any(|other| other.name == field.name)
            {
                self.add_error(
                    &get_token_location(&file, name_index),
                    "Non-unique fields in constructor.",
                );
            }
            let name = self.create_string(&field.name, get_token_location(&file, name_index));
            let value = self.generate_expression(&field.value)?;
            pairs.push(self.apply_builtin(
                "$Pair",
                [name, value],
                get_span_location(
                    &file,
                    TokenSpan {
                        start: name_index,
                        end: value_span.end,
                    },
                ),
                OpApplBinding::default(),
            ));
        }
        let record = self.apply_builtin(
            operator,
            pairs,
            get_span_location(&file, span),
            OpApplBinding::default(),
        );
        self.spec
            .graph
            .module_mut(self.module)
            .expect("a module")
            .records
            .push(record);
        Ok(record)
    }

    /// `getTokenPosition` (generator.ts 1292–1297).
    pub(super) fn get_token_position(&self, index: usize) -> Position {
        let token = &self.file.tokens[index];
        Position {
            line: token.line,
            column: token.column,
        }
    }

    /// `getRecursiveDeclarations` (generator.ts 1299–1324): the declarations of a RECURSIVE
    /// statement from the token at `start`, which the syntax tree of a LET leaves out.
    pub(super) fn get_recursive_declarations(&self, start: usize) -> Vec<Rc<Declaration>> {
        let file = &self.file;
        let mut declarations = Vec::new();
        let mut index = start;
        while file
            .tokens
            .get(index)
            .is_some_and(|token| token.kind == TokenKind::Identifier)
        {
            let end = if is_token(file, index + 1, "(") {
                get_matching_index(file, index + 1)
            } else {
                index
            };
            let arity = file
                .tokens
                .get(index + 1..end)
                .unwrap_or_default()
                .iter()
                .filter(|token| &*token.text == "_")
                .count();
            let position = self.get_token_position(index);
            declarations.push(Rc::new(Declaration {
                name: file.tokens[index].text.clone(),
                arity,
                location: Location {
                    line: position.line,
                    column: position.column,
                    range: Some(SourceRange {
                        module: file.name.clone(),
                        start: position,
                        end: self.get_token_position(end),
                    }),
                },
            }));
            if !is_token(file, end + 1, ",") {
                break;
            }
            index = end + 2;
        }
        declarations
    }

    /// `getLetUnits` (generator.ts 1326–1354): the units of a LET in source order, with its
    /// RECURSIVE statements found among its tokens. `expression` is a `Let`.
    pub(super) fn get_let_units(&self, expression: &Expr) -> Vec<LetUnit> {
        let ExpressionKind::Let {
            definitions,
            instances,
            body,
            ..
        } = &expression.kind
        else {
            return Vec::new();
        };
        let file = &self.file;
        let units: Vec<(LetUnit, TokenSpan)> = definitions
            .iter()
            .map(|definition| {
                (
                    LetUnit::Definition(definition.clone()),
                    self.get_definition_span(&definition.location, definition.is_local),
                )
            })
            .chain(instances.iter().flatten().map(|instance| {
                (
                    LetUnit::Instance(instance.clone()),
                    self.get_definition_span(&instance.location, instance.is_local),
                )
            }))
            .collect();
        let let_start = get_expression_span(file, expression).start;
        let body_start = get_parenthesized_span(file, get_expression_span(file, body)).start;
        let recursives: Vec<(LetUnit, TokenSpan)> = (let_start + 1..body_start)
            .filter(|&index| {
                let is_in_unit = units
                    .iter()
                    .any(|(_, span)| span.start <= index && index <= span.end);
                is_token(file, index, "RECURSIVE") && !is_in_unit
            })
            .map(|index| {
                (
                    LetUnit::Recursive(self.get_recursive_declarations(index + 1)),
                    TokenSpan {
                        start: index,
                        end: index,
                    },
                )
            })
            .collect();
        let mut entries: Vec<(LetUnit, TokenSpan)> = units.into_iter().chain(recursives).collect();
        entries.sort_by_key(|(_, span)| span.start);
        entries.into_iter().map(|(unit, _)| unit).collect()
    }

    /// `generateLet` (generator.ts 1356–1384). `expression` is a `Let`.
    pub(super) fn generate_let(&mut self, expression: &Expr) -> Result<NodeId> {
        let ExpressionKind::Let { body, .. } = &expression.kind else {
            return not_yet("Expected a LET");
        };
        let (let_in, context) = self.with_context(LocalContext::default(), |generator| {
            generator.state.cur_level += 1;
            let level = generator.state.cur_level as usize;
            let counts = &mut generator.state.unresolved_count;
            if counts.len() <= level {
                counts.resize(level + 1, 0);
            }
            counts[level] = 0;
            let mut op_defs = Vec::new();
            let mut instances = Vec::new();
            for unit in generator.get_let_units(expression) {
                match unit {
                    LetUnit::Recursive(declarations) => generator.process_recursive(&declarations),
                    LetUnit::Instance(instance) => generator.process_module_definition(
                        &instance,
                        Some(&mut op_defs),
                        Some(&mut instances),
                    )?,
                    LetUnit::Definition(definition) => match definition.kind {
                        DefinitionKind::Function { .. } => {
                            generator.process_function(&definition, Some(&mut op_defs))?
                        }
                        DefinitionKind::Operator { .. } => {
                            generator.process_operator(&definition, Some(&mut op_defs))?
                        }
                    },
                }
            }
            generator.check_for_undefined_recursive_ops();
            generator.state.cur_level = generator.state.cur_level.saturating_sub(1);
            let body = generator.generate_expression(body)?;
            let uid = generator.spec.get_uid();
            let location = generator.get_location(expression);
            Ok(generator.spec.graph.add(
                uid,
                NodeKind::LetIn(LetIn {
                    op_defs,
                    instances,
                    body,
                    context: Default::default(),
                    location,
                }),
            ))
        })?;
        // The LetIn holds its context, which is complete once its body is generated.
        if let NodeKind::LetIn(node) = &mut self.spec.graph.node_mut(let_in).kind {
            node.context = context.context;
        }
        Ok(let_in)
    }

    /// `generateChoose` (generator.ts 1386–1420). `expression` is a `Choose`.
    pub(super) fn generate_choose(&mut self, expression: &Expr) -> Result<NodeId> {
        let ExpressionKind::Choose { pattern, set, body } = &expression.kind else {
            return not_yet("Expected a CHOOSE");
        };
        let file = self.file.clone();
        let span = get_expression_span(&file, expression);
        let location = get_span_location(&file, span);
        let names = pattern.names();
        let is_name = matches!(pattern, BoundPattern::Name { .. });
        let (choose, _) = self.with_context(LocalContext::default(), |generator| {
            let Some(set) = set else {
                let indexes = find_name_tokens(&file, span.start, span.end, names);
                // SANY locates the symbol of CHOOSE x : P at the CHOOSE keyword.
                let params: Vec<NodeId> = names
                    .iter()
                    .enumerate()
                    .map(|(index, name)| {
                        let token = if is_name { span.start } else { indexes[index] };
                        generator.create_formal_param(
                            name.clone(),
                            0,
                            Some(get_token_location(&file, token)),
                            true,
                        )
                    })
                    .collect();
                let body = generator.generate_with_params(params.clone(), body)?;
                return Ok(generator.apply_builtin(
                    "$UnboundedChoose",
                    [body],
                    location,
                    OpApplBinding {
                        unbounded: Some(params),
                        ..OpApplBinding::default()
                    },
                ));
            };
            let range = generator.generate_expression(set)?;
            let set_span = get_expression_span(&file, set);
            let indexes = find_name_tokens(&file, span.start, set_span.start, names);
            let params: Vec<NodeId> = names
                .iter()
                .enumerate()
                .map(|(index, name)| {
                    generator.create_formal_param(
                        name.clone(),
                        0,
                        Some(get_token_location(&file, indexes[index])),
                        true,
                    )
                })
                .collect();
            let body = generator.generate_with_params(params.clone(), body)?;
            Ok(generator.apply_builtin(
                "$BoundedChoose",
                [body],
                location,
                OpApplBinding {
                    unbounded: None,
                    bounded: Some(vec![params]),
                    tuple_ors: Some(vec![!is_name]),
                    ranges: Some(vec![range]),
                },
            ))
        })?;
        Ok(choose)
    }

    /// `getUnresolvedOperator` (generator.ts 1422–1450). `expression` is an `Apply`.
    pub(super) fn get_unresolved_operator(&self, expression: &Expr) -> Option<UnresolvedOperator> {
        let ExpressionKind::Apply { operator, args, .. } = &expression.kind else {
            return None;
        };
        if is_identifier(operator) || is_selector(operator) || args.len() > 2 {
            return None;
        }
        if self.resolve_symbol(&resolve_synonym(operator)).is_some() {
            return None;
        }
        let file = &self.file;
        let span = get_expression_span(file, expression);
        // SANY reports an operator applied like a function, as in op(a, b), as an unknown operator.
        if file.tokens[span.start].text == *operator && is_token(file, span.start + 1, "(") {
            return None;
        }
        let first_span = get_parenthesized_span(file, get_expression_span(file, args.first()?));
        let is_prefix = args.len() == 1 && first_span.start != span.start;
        let index = if is_prefix {
            span.start
        } else {
            first_span.end + 1
        };
        let text = get_token_source(file, index);
        Some(UnresolvedOperator {
            index,
            name: if is_prefix && text == "-" {
                "-.".to_owned()
            } else {
                text.to_owned()
            },
            fixity: if is_prefix {
                "prefix"
            } else if args.len() == 2 {
                "infix"
            } else {
                "postfix"
            },
        })
    }

    /// `{ ...createNullNode(), isAbsent: true }`.
    fn create_absent_node(&mut self) -> NodeId {
        let node = self.create_null_node();
        if let NodeKind::OpAppl(application) = &mut self.spec.graph.node_mut(node).kind {
            application.is_absent = true;
        }
        node
    }

    /// `applyBuiltin` of an operator with the one operand `generateExpression(operand)`.
    fn apply_builtin_to(
        &mut self,
        name: &str,
        operand: &Expr,
        location: SanyLocation,
    ) -> Result<NodeId> {
        let operand = self.generate_expression(operand)?;
        Ok(self.apply_builtin(name, [operand], location, OpApplBinding::default()))
    }

    /// `expressions.map(generateExpression)`.
    fn generate_expressions(&mut self, expressions: &[Expr]) -> Result<Vec<NodeId>> {
        expressions
            .iter()
            .map(|expression| self.generate_expression(expression))
            .collect()
    }

    /// `generateExpression` (generator.ts 1452–1686).
    pub(super) fn generate_expression(&mut self, expression: &Expr) -> Result<NodeId> {
        let location = self.get_location(expression);
        let file = self.file.clone();
        match &expression.kind {
            ExpressionKind::Number { text, .. } => {
                let uid = self.spec.get_uid();
                Ok(self.spec.graph.add(
                    uid,
                    NodeKind::Numeral {
                        value: get_numeral_digits(text),
                        location,
                    },
                ))
            }
            ExpressionKind::Decimal { text } => {
                let (integral_part, fractional_part) =
                    text.split_once('.').unwrap_or((&**text, ""));
                let (mantissa, exponent) = get_decimal_parts(integral_part, fractional_part);
                let uid = self.spec.get_uid();
                Ok(self.spec.graph.add(
                    uid,
                    NodeKind::Decimal(Decimal {
                        mantissa,
                        exponent,
                        integral_part: integral_part.to_owned(),
                        fractional_part: fractional_part.to_owned(),
                        location,
                    }),
                ))
            }
            ExpressionKind::String { value } => Ok(self.create_string(value, location)),
            ExpressionKind::Identifier { .. } => {
                let node = self.generate_selector_expression(expression)?;
                self.check_recursion(node);
                Ok(node)
            }
            ExpressionKind::Apply { operator, .. } => {
                if let Some(unresolved) = self.get_unresolved_operator(expression) {
                    self.add_error(
                        &get_token_location(&file, unresolved.index),
                        format!(
                            "Could not find declaration or definition of symbol '{}'.",
                            unresolved.name
                        ),
                    );
                    self.add_error(
                        &location,
                        format!(
                            "Couldn't resolve {} operator symbol `{}'.",
                            unresolved.fixity, unresolved.name
                        ),
                    );
                    return Ok(self.create_absent_node());
                }
                let node = self.generate_selector_expression(expression)?;
                if is_selector(operator) || is_identifier(operator) {
                    self.check_recursion(node);
                }
                Ok(node)
            }
            ExpressionKind::Bracket(_) => {
                self.add_error(
                    &get_token_location(&file, get_expression_span(&file, expression).start),
                    "Unsupported expression type `['.",
                );
                Ok(self.create_absent_node())
            }
            ExpressionKind::OperatorReference { .. } | ExpressionKind::Lambda { .. } => {
                let text = &file.tokens[get_expression_span(&file, expression).start].text;
                let message = if &**text == "LAMBDA" {
                    "LAMBDA expression used where an expression is required.".to_owned()
                } else {
                    format!(
                        "Unsupported expression type `{}'.",
                        get_operator_node_kind(expression, text)
                    )
                };
                self.add_error(&location, message);
                Ok(self.create_absent_node())
            }
            ExpressionKind::Junction { .. } => self.generate_junction(expression),
            ExpressionKind::Prime(operand) => self.apply_builtin_to("'", operand, location),
            ExpressionKind::Unchanged(operand) => {
                self.apply_builtin_to("UNCHANGED", operand, location)
            }
            ExpressionKind::Enabled(operand) => self.apply_builtin_to("ENABLED", operand, location),
            ExpressionKind::Always(operand) => self.apply_builtin_to("[]", operand, location),
            ExpressionKind::Eventually(operand) => self.apply_builtin_to("<>", operand, location),
            ExpressionKind::If {
                condition,
                consequent,
                alternative,
            } => {
                let operands = [
                    self.generate_expression(condition)?,
                    self.generate_expression(consequent)?,
                    self.generate_expression(alternative)?,
                ];
                Ok(self.apply_builtin("$IfThenElse", operands, location, OpApplBinding::default()))
            }
            ExpressionKind::Case { .. } => self.generate_case(expression),
            ExpressionKind::Let { .. } => self.generate_let(expression),
            ExpressionKind::Quantified {
                quantifier,
                bounds,
                body,
            } => {
                let span = get_expression_span(&file, expression);
                let name = match quantifier {
                    Quantifier::Forall => "$BoundedForall",
                    Quantifier::Exists => "$BoundedExists",
                };
                let (node, _) = self.with_context(LocalContext::default(), |generator| {
                    let bounds = generator.generate_bounds(bounds, span.start)?;
                    let body = generator.generate_with_params(bounds.bounded.concat(), body)?;
                    Ok(generator.apply_builtin(name, [body], location, bounds.into()))
                })?;
                Ok(node)
            }
            ExpressionKind::UnboundedQuantifier {
                quantifier,
                names,
                is_temporal,
                body,
                ..
            } => {
                let span = get_expression_span(&file, expression);
                let body_span = get_expression_span(&file, body);
                let indexes = find_name_tokens(&file, span.start, body_span.start, names);
                let name = match (is_temporal, quantifier) {
                    (true, Quantifier::Forall) => "$TemporalForall",
                    (true, Quantifier::Exists) => "$TemporalExists",
                    (false, Quantifier::Forall) => "$UnboundedForall",
                    (false, Quantifier::Exists) => "$UnboundedExists",
                };
                let (node, _) = self.with_context(LocalContext::default(), |generator| {
                    let params: Vec<NodeId> = names
                        .iter()
                        .enumerate()
                        .map(|(index, param_name)| {
                            generator.create_formal_param(
                                param_name.clone(),
                                0,
                                Some(get_token_location(&file, indexes[index])),
                                true,
                            )
                        })
                        .collect();
                    let body = generator.generate_with_params(params.clone(), body)?;
                    Ok(generator.apply_builtin(
                        name,
                        [body],
                        location,
                        OpApplBinding {
                            unbounded: Some(params),
                            ..OpApplBinding::default()
                        },
                    ))
                })?;
                Ok(node)
            }
            ExpressionKind::Choose { .. } => self.generate_choose(expression),
            ExpressionKind::SetEnumeration(elements) => {
                let nodes = self.generate_expressions(elements)?;
                Ok(self.apply_builtin("$SetEnumerate", nodes, location, OpApplBinding::default()))
            }
            ExpressionKind::Tuple(elements) => {
                let nodes = self.generate_expressions(elements)?;
                Ok(self.apply_builtin("$Tuple", nodes, location, OpApplBinding::default()))
            }
            ExpressionKind::SetFilter { bound, predicate } => {
                let range = self.generate_expression(&bound.set)?;
                let span = get_expression_span(&file, expression);
                let (node, _) = self.with_context(LocalContext::default(), |generator| {
                    let bounds = generator.generate_bounds_with_ranges(
                        std::slice::from_ref(bound),
                        span.start,
                        vec![range],
                    );
                    let body =
                        generator.generate_with_params(bounds.bounded.concat(), predicate)?;
                    Ok(generator.apply_builtin("$SubsetOf", [body], location, bounds.into()))
                })?;
                Ok(node)
            }
            ExpressionKind::SetMap {
                expression: element,
                bounds,
            } => {
                let element_span = get_expression_span(&file, element);
                let (node, _) = self.with_context(LocalContext::default(), |generator| {
                    let bounds = generator.generate_bounds(bounds, element_span.end + 1)?;
                    let body = generator.generate_with_params(bounds.bounded.concat(), element)?;
                    Ok(generator.apply_builtin("$SetOfAll", [body], location, bounds.into()))
                })?;
                Ok(node)
            }
            ExpressionKind::FunctionConstruction { bounds, body } => {
                let span = get_expression_span(&file, expression);
                let (node, _) = self.with_context(LocalContext::default(), |generator| {
                    let bounds = generator.generate_bounds(bounds, span.start)?;
                    let body = generator.generate_with_params(bounds.bounded.concat(), body)?;
                    Ok(generator.apply_builtin("$FcnConstructor", [body], location, bounds.into()))
                })?;
                Ok(node)
            }
            ExpressionKind::FunctionSet { domain, range } => {
                let operands = [
                    self.generate_expression(domain)?,
                    self.generate_expression(range)?,
                ];
                Ok(self.apply_builtin("$SetOfFcns", operands, location, OpApplBinding::default()))
            }
            ExpressionKind::Record { is_set, .. } => self.generate_record_fields(
                if *is_set {
                    "$SetOfRcds"
                } else {
                    "$RcdConstructor"
                },
                expression,
            ),
            ExpressionKind::Except { .. } => self.generate_except(expression),
            ExpressionKind::ExceptAt => {
                let (Some(&except), Some(&component)) =
                    (self.except_stack.last(), self.except_spec_stack.last())
                else {
                    self.add_error(&location, "@ used where its meaning is not defined.");
                    return Ok(self.create_null_node());
                };
                let location = self
                    .spec
                    .graph
                    .node(component)
                    .location()
                    .cloned()
                    .expect("an OpAppl's location");
                let uid = self.spec.get_uid();
                Ok(self.spec.graph.add(
                    uid,
                    NodeKind::At {
                        except,
                        component,
                        location,
                    },
                ))
            }
            ExpressionKind::FunctionApplication { function, args } => {
                let function_node = self.generate_expression(function)?;
                // SANY leaves the whole application null, without generating its arguments.
                if self.spec.graph.node(function_node).is_absent() {
                    return Ok(function_node);
                }
                self.check_recursion(function_node);
                // A user-defined function applied to two or more arguments takes as many as its
                // definition binds; a tuple of bound symbols is one.
                if let Some((name, parameters)) = self.get_function_parameters(function_node)
                    && args.len() >= 2
                    && parameters != args.len()
                {
                    self.add_error(
                        &location,
                        format!(
                            "Function '{name}' is defined with {parameters} parameters, but is applied to {} arguments.",
                            args.len()
                        ),
                    );
                    return Ok(self.create_null_node());
                }
                let argument = if let [argument] = args.as_slice() {
                    self.generate_expression(argument)?
                } else {
                    let nodes = self.generate_expressions(args)?;
                    self.apply_builtin("$Tuple", nodes, location.clone(), OpApplBinding::default())
                };
                Ok(self.apply_builtin(
                    "$FcnApply",
                    [function_node, argument],
                    location,
                    OpApplBinding::default(),
                ))
            }
            ExpressionKind::FieldAccess { record, field } => {
                let record = self.generate_expression(record)?;
                let span = get_expression_span(&file, expression);
                let field = self.create_string(field, get_token_location(&file, span.end));
                Ok(self.apply_builtin(
                    "$RcdSelect",
                    [record, field],
                    location,
                    OpApplBinding::default(),
                ))
            }
            ExpressionKind::Product(factors) => {
                let nodes = self.generate_expressions(factors)?;
                Ok(self.apply_builtin("$CartesianProd", nodes, location, OpApplBinding::default()))
            }
            ExpressionKind::Action {
                is_box,
                action,
                subscript,
            } => {
                let name = if *is_box { "$SquareAct" } else { "$AngleAct" };
                let operands = [
                    self.generate_expression(action)?,
                    self.generate_expression(subscript)?,
                ];
                Ok(self.apply_builtin(name, operands, location, OpApplBinding::default()))
            }
            ExpressionKind::Fairness {
                is_strong,
                subscript,
                action,
                ..
            } => {
                let name = if *is_strong { "$SF" } else { "$WF" };
                let operands = [
                    self.generate_expression(subscript)?,
                    self.generate_expression(action)?,
                ];
                Ok(self.apply_builtin(name, operands, location, OpApplBinding::default()))
            }
            ExpressionKind::Label { .. } => self.generate_label(expression),
            ExpressionKind::Subexpression { .. } => self.generate_selector_expression(expression),
        }
    }

    /// `generateBoundsWithRanges` (generator.ts 1688–1711).
    pub(super) fn generate_bounds_with_ranges(
        &mut self,
        bounds: &[Bound],
        search_start: usize,
        ranges: Vec<NodeId>,
    ) -> BoundSymbols {
        let file = self.file.clone();
        let groups = get_bound_groups(bounds);
        let mut cursor = search_start;
        let bounded = groups
            .iter()
            .map(|group| {
                let set_span = get_expression_span(&file, &group[0].set);
                let names: Vec<_> = group
                    .iter()
                    .flat_map(|bound| bound.pattern.names().iter().cloned())
                    .collect();
                let indexes = find_name_tokens(&file, cursor, set_span.start, &names);
                cursor = set_span.end + 1;
                names
                    .into_iter()
                    .enumerate()
                    .map(|(index, name)| {
                        self.create_formal_param(
                            name,
                            0,
                            Some(get_token_location(&file, indexes[index])),
                            true,
                        )
                    })
                    .collect()
            })
            .collect();
        BoundSymbols {
            bounded,
            tuple_ors: groups
                .iter()
                .map(|group| matches!(group[0].pattern, BoundPattern::Tuple { .. }))
                .collect(),
            ranges,
        }
    }

    /// `generateLabel` (generator.ts 1713–1782). `expression` is a `Label`.
    /// The name of the function `node` applies and how many parameters its definition binds,
    /// where it applies a user-defined function (`$NonRecursiveFcnSpec` or `$RecursiveFcnSpec`).
    fn get_function_parameters(&self, node: NodeId) -> Option<(Name, usize)> {
        let graph = &self.spec.graph;
        let NodeKind::OpAppl(application) = graph.kind(node) else {
            return None;
        };
        let definition = graph.op_def(application.operator)?;
        if definition.def_kind != DefKind::UserDefined {
            return None;
        }
        let NodeKind::OpAppl(body) = graph.kind(definition.body?) else {
            return None;
        };
        let is_function = graph.op_def(body.operator).is_some_and(|operator| {
            matches!(
                &*operator.name,
                "$NonRecursiveFcnSpec" | "$RecursiveFcnSpec"
            )
        });
        if !is_function {
            return None;
        }
        let tuples = body.tuple_ors.as_deref().unwrap_or_default();
        let parameters = body
            .bounded
            .as_deref()
            .unwrap_or_default()
            .iter()
            .enumerate()
            .map(|(index, symbols)| {
                if tuples.get(index).copied().unwrap_or(false) {
                    1
                } else {
                    symbols.len()
                }
            });
        Some((definition.name.clone(), parameters.sum()))
    }

    pub(super) fn generate_label(&mut self, expression: &Expr) -> Result<NodeId> {
        let ExpressionKind::Label {
            name, params, body, ..
        } = &expression.kind
        else {
            return not_yet("Expected a label");
        };
        let file = self.file.clone();
        let param_indexes = find_name_tokens(
            &file,
            get_expression_span(&file, expression).start,
            get_expression_span(&file, body).start,
            params,
        );
        let location = self.get_location(expression);
        self.generate_labeled(name, params, &param_indexes, location, false, |generator| {
            generator.generate_expression(body)
        })
    }

    /// `generateLabel` for a label whose parameters are the tokens at `param_indexes`, and whose
    /// body, an ASSUME/PROVE when `is_assume_prove`, `generate_body` generates.
    pub(super) fn generate_labeled(
        &mut self,
        name: &Name,
        params: &[Name],
        param_indexes: &[usize],
        location: SanyLocation,
        is_assume_prove: bool,
        generate_body: impl FnOnce(&mut Self) -> Result<NodeId>,
    ) -> Result<NodeId> {
        let Some(scope) = self.label_scopes.len().checked_sub(1) else {
            self.add_error(&location, "Label not in definition or proof step.");
            return Ok(self.create_null_node());
        };
        // Generator.noLabelsAllowed: no label lies in the scope of a declaration of a nested
        // ASSUME/PROVE.
        let state = &self.assume_prove_state;
        if state
            .is_declared
            .iter()
            .take(state.depth + 1)
            .skip(2)
            .any(|&is_declared| is_declared)
        {
            self.add_error(
                &location,
                "Label not allowed within scope of declaration in nested ASSUME/PROVE.",
            );
            return Ok(self.create_null_node());
        }
        if !self.except_stack.is_empty() && !self.except_spec_stack.is_empty() {
            self.add_error(
                &location,
                "Labels inside EXCEPT clauses are not yet implemented.",
            );
            return Ok(self.create_null_node());
        }
        self.push_label_scope();
        let body_node = generate_body(self)?;
        let labels = self.pop_labels();
        let file = self.file.clone();
        let param_nodes: Vec<NodeId> = params
            .iter()
            .enumerate()
            .map(|(index, param_name)| {
                let symbol = self.resolve_symbol(param_name);
                if let Some(symbol) = symbol.filter(|&symbol| {
                    matches!(self.spec.graph.kind(symbol), NodeKind::FormalParam(_))
                }) {
                    return symbol;
                }
                let param_location = get_token_location(&file, param_indexes[index]);
                self.add_error(
                    &param_location,
                    format!("Illegal parameter {param_name} of label `{name}'."),
                );
                self.create_formal_param(param_name.clone(), 0, Some(param_location), false)
            })
            .collect();
        let uid = self.spec.get_uid();
        let label = self.spec.graph.add(
            uid,
            NodeKind::Label(Label {
                name: name.clone(),
                params: param_nodes.clone(),
                body: body_node,
                labels,
                is_assume_prove,
                location: location.clone(),
            }),
        );
        let get_param_name = |generator: &Self, param: NodeId| {
            generator
                .spec
                .graph
                .node(param)
                .symbol_name()
                .expect("a formal parameter")
                .clone()
        };
        // Generator.formalParamsEqual: a label names each parameter bound around it once.
        let mut named: Vec<NodeId> = Vec::new();
        for &param in &param_nodes {
            if named.contains(&param) {
                let param_name = get_param_name(self, param);
                self.add_error(
                    &location,
                    format!("Repeated formal parameter {param_name} \nin label `{name}'."),
                );
            } else {
                named.push(param);
            }
        }
        let bound_params: Vec<NodeId> = self.label_scopes[scope].params.concat();
        for param in bound_params {
            match named.iter().position(|&entry| entry == param) {
                Some(position) => {
                    named.remove(position);
                }
                None => {
                    let param_name = get_param_name(self, param);
                    self.add_error(
                        &location,
                        format!("Label {name} must contain formal parameter `{param_name}'."),
                    );
                }
            }
        }
        if !named.is_empty() {
            let extras: String = named
                .iter()
                .map(|&param| format!("{}  ", get_param_name(self, param)))
                .collect();
            self.add_error(
                &location,
                format!("Label {name} declares extra parameter(s)  {extras}"),
            );
        }
        if self.label_scopes[scope].labels.contains_key(name) {
            self.add_error(&location, format!("Duplicate label `{name}'."));
        } else {
            self.label_scopes[scope].labels.insert(name.clone(), label);
        }
        if let Some(goal) = self.assume_prove_state.goal {
            let clause = self.assume_prove_state.goal_clause;
            self.label_goals.insert(
                label,
                LabelGoal {
                    scope: goal,
                    clause,
                },
            );
        }
        Ok(label)
    }

    /// `getParams` (generator.ts 1785–1805): the parameters of a definition's or instance's
    /// left-hand side, located as SANY locates them.
    pub(super) fn get_params(
        &mut self,
        params: &[OperatorParam],
        span: TokenSpan,
        is_added: bool,
    ) -> Vec<NodeId> {
        let file = self.file.clone();
        let mut cursor = span.start;
        params
            .iter()
            .map(|param| {
                let index = match &param.location {
                    Some(location) => get_token_index(&file, location.position()),
                    None => self.find_name_or_keyword(cursor, &param.name),
                };
                let param_span = self.get_operator_span(index, param.arity);
                cursor = param_span.end + 1;
                self.create_formal_param(
                    resolve_synonym(&param.name),
                    param.arity,
                    Some(get_span_location(&file, param_span)),
                    is_added,
                )
            })
            .collect()
    }

    /// `getDefinitionSpan` (generator.ts 1807–1815): the span of a definition or instance at
    /// `location`, with the LOCAL before it.
    pub(super) fn get_definition_span(&self, location: &Location, is_local: bool) -> TokenSpan {
        let span = self.get_unit_span(location);
        let file = &self.file;
        match span.start.checked_sub(1) {
            Some(before)
                if is_local
                    && !is_token(file, span.start, "LOCAL")
                    && is_token(file, before, "LOCAL") =>
            {
                TokenSpan {
                    start: before,
                    end: span.end,
                }
            }
            _ => span,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::get_decimal_parts;

    #[test]
    fn writes_a_decimal_as_its_mantissa_and_exponent() {
        assert_eq!(
            get_decimal_parts("3", "14"),
            ("314".to_owned(), "-2".to_owned())
        );
        assert_eq!(
            get_decimal_parts("007", "50"),
            ("750".to_owned(), "-2".to_owned())
        );
        assert_eq!(
            get_decimal_parts("0", "00"),
            ("0".to_owned(), "-2".to_owned())
        );
        assert_eq!(
            get_decimal_parts("9223372036854775807", ""),
            ("9223372036854775807".to_owned(), "0".to_owned())
        );
        assert_eq!(
            get_decimal_parts("92233720368547758", "08"),
            ("9223372036854775808".to_owned(), "2".to_owned())
        );
    }
}
