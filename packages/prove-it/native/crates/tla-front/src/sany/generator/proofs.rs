//! The proofs of `generateModule` (`generator.ts` lines 2335–2997): facts, DEF clauses, USE and
//! HIDE, NEW, ASSUME/PROVE, theorem definitions, leaf and non-leaf proofs, step bodies, theorems
//! and assumptions.

use std::rc::Rc;

use crate::ast::{
    AssumeProve, Assumed, Assumption, DefinitionKind, DefinitionUnit, Expr, Expression,
    ExpressionKind, Fact, Location, NewSymbol, Proof, ProofKind, ProofStep, Statement, StepBody,
    Theorem, UseOrHide,
};
use crate::lexer::TokenKind;
use crate::ordered_map::OrderedMap;
use crate::sany::nodes::{
    DefKind, LeafProof, Name, NodeId, NodeKind, NonLeafProof, OpDecl, OpDef, SanyLocation,
    ThmOrAssumpDef,
};
use crate::sany::selectors::{get_selector_items, is_general_id};
use crate::sany::source::{
    TokenSpan, find_name_tokens, get_expression_span, get_matching_index, get_parenthesized_span,
    get_range_span, get_span_location, get_token_index, get_token_location, get_token_source,
    is_box_token, is_token,
};
use crate::sany::{Result, not_yet};

use super::{
    AssumeProveScope, ContextSlot, DefEntryParts, LocalContext, ModuleGenerator,
    NESTED_FIRST_CHILD_KINDS, OpApplBinding, ScopeId, add_to_context, get_new_symbol_kind,
    get_syntax_kind_of, resolve_synonym,
};

/// What `generateStepBody` gives: the step's node, and whether it is a PICK, whose context the
/// caller pops.
#[derive(Clone, Copy, Debug)]
pub(super) struct GeneratedStep {
    pub(super) node: NodeId,
    pub(super) is_pick: bool,
}

impl ModuleGenerator<'_> {
    /// `getFactModules` (generator.ts 2335–2345): the module a `Fact::Module` names, which SANY
    /// leaves out after reporting it at the module's name.
    pub(super) fn get_fact_modules(&mut self, name: &Name, location: &Location) -> Vec<NodeId> {
        let module = self.resolve_module(name).or_else(|| {
            let current = &self.spec.graph.module(self.module).expect("a module").name;
            (current == name).then_some(self.module)
        });
        if let Some(module) = module {
            return vec![module];
        }
        let index = get_token_index(&self.file, location.position()) + 1;
        let error_location = get_token_location(&self.file, index);
        self.add_error(
            &error_location,
            format!("Module `{name}' used without being extended or instantiated."),
        );
        Vec::new()
    }

    /// `generateFacts` (generator.ts 2348–2356).
    pub(super) fn generate_facts(&mut self, facts: &[Fact]) -> Result<Vec<NodeId>> {
        let mut nodes = Vec::new();
        for fact in facts {
            let expression = match fact {
                Fact::Module { name, location } => {
                    nodes.extend(self.get_fact_modules(name, location));
                    continue;
                }
                Fact::Expression(expression) => expression,
            };
            if !get_selector_items(expression).is_some_and(|items| is_general_id(&items)) {
                nodes.push(self.generate_expression(expression)?);
                continue;
            }
            let node = self.generate_selector(expression, 0, true, false)?;
            if matches!(self.spec.graph.kind(node), NodeKind::ThmOrAssumpDef(_)) {
                return not_yet("Expected a fact");
            }
            nodes.push(node);
        }
        Ok(nodes)
    }

    /// `isParenthesized` (generator.ts 2358–2359).
    pub(super) fn is_parenthesized(&self, span: TokenSpan) -> bool {
        is_token(&self.file, span.start, "(")
            && get_matching_index(&self.file, span.start) == span.end
    }

    /// `getOperandSpan` (generator.ts 2360–2361).
    pub(super) fn get_operand_span(&self, expression: &Expr) -> TokenSpan {
        get_parenthesized_span(&self.file, get_expression_span(&self.file, expression))
    }

    /// `getApplicationKind` (generator.ts 2363–2368): how SANY's parser shapes an application.
    /// `expression` is an `Apply`.
    pub(super) fn get_application_kind(&self, expression: &Expr, span: TokenSpan) -> &'static str {
        let ExpressionKind::Apply { args, .. } = &expression.kind else {
            unreachable!("an Apply")
        };
        if args
            .first()
            .is_some_and(|first| self.get_operand_span(first).start == span.start)
        {
            return if args.len() == 2 {
                "N_InfixExpr"
            } else {
                "N_PostfixExpr"
            };
        }
        if self.file.tokens[span.start].kind == TokenKind::Identifier {
            "N_OpApplication"
        } else {
            "N_PrefixExpr"
        }
    }

    /// `getSyntaxKind` (generator.ts 2370–2375): the kind of SANY's syntax node for an
    /// expression, or for a token its text.
    pub(super) fn get_syntax_kind(&self, expression: &Expr, span: TokenSpan) -> Option<String> {
        if self.is_parenthesized(span) {
            return Some("N_ParenExpr".to_owned());
        }
        match &expression.kind {
            ExpressionKind::String { .. } => {
                Some(get_token_source(&self.file, span.start).to_owned())
            }
            ExpressionKind::Apply { .. } => {
                Some(self.get_application_kind(expression, span).to_owned())
            }
            _ => get_syntax_kind_of(expression).map(str::to_owned),
        }
    }

    /// `hasChildlessFirstChild` (generator.ts 2378–2383), whose `undefined` is `None`.
    pub(super) fn has_childless_first_child(
        &self,
        expression: &Expr,
        span: TokenSpan,
    ) -> Option<bool> {
        match &expression.kind {
            ExpressionKind::String { .. } if !self.is_parenthesized(span) => return Some(false),
            ExpressionKind::Identifier { name, .. } if !name.contains('!') => return Some(true),
            _ => {}
        }
        match self.get_syntax_kind(expression, span) {
            Some(kind) if !NESTED_FIRST_CHILD_KINDS.contains(&kind.as_str()) => Some(true),
            _ => None,
        }
    }

    /// `getPart` in `getDefEntryParts`: the last part of a DEF clause entry, at `span`.
    fn get_def_entry_part(
        &self,
        has_childless_first_child: Option<bool>,
        operand: &Expr,
        span: TokenSpan,
    ) -> DefEntryParts {
        DefEntryParts {
            has_childless_first_child,
            last: span,
            last_kind: self.get_syntax_kind(operand, span),
        }
    }

    /// `getDefEntryParts` (generator.ts 2386–2474).
    pub(super) fn get_def_entry_parts(
        &self,
        expression: &Expr,
        span: TokenSpan,
    ) -> Option<DefEntryParts> {
        let get_token_part =
            |has_childless_first_child, index: usize, last_kind: String| DefEntryParts {
                has_childless_first_child,
                last: TokenSpan {
                    start: index,
                    end: index,
                },
                last_kind: Some(last_kind),
            };
        let after_first = TokenSpan {
            start: span.start + 1,
            end: span.end,
        };
        if self.is_parenthesized(span) {
            let inner = TokenSpan {
                start: span.start + 1,
                end: span.end - 1,
            };
            return Some(self.get_def_entry_part(Some(false), expression, inner));
        }
        match &expression.kind {
            ExpressionKind::If {
                condition: operand, ..
            }
            | ExpressionKind::Action {
                action: operand, ..
            } => {
                Some(self.get_def_entry_part(Some(false), operand, self.get_operand_span(operand)))
            }
            ExpressionKind::Tuple(elements) | ExpressionKind::SetEnumeration(elements) => {
                Some(match elements.first() {
                    None => get_token_part(
                        Some(false),
                        span.end,
                        self.file.tokens[span.end].text.to_string(),
                    ),
                    Some(first) => {
                        self.get_def_entry_part(Some(false), first, self.get_operand_span(first))
                    }
                })
            }
            ExpressionKind::Always(operand)
            | ExpressionKind::Eventually(operand)
            | ExpressionKind::Enabled(operand)
            | ExpressionKind::Unchanged(operand) => {
                Some(self.get_def_entry_part(Some(true), operand, after_first))
            }
            ExpressionKind::Prime(operand) => Some(get_token_part(
                self.has_childless_first_child(operand, self.get_operand_span(operand)),
                span.end,
                "N_GenPostfixOp".to_owned(),
            )),
            ExpressionKind::FunctionApplication {
                function: operand, ..
            }
            | ExpressionKind::FieldAccess {
                record: operand, ..
            } => {
                let operand_span = self.get_operand_span(operand);
                let next = operand_span.end + 1;
                Some(get_token_part(
                    self.has_childless_first_child(operand, operand_span),
                    next,
                    self.file.tokens[next].text.to_string(),
                ))
            }
            ExpressionKind::Apply { operator, args, .. } => {
                let kind = self.get_application_kind(expression, span);
                if kind == "N_OpApplication" {
                    return (!operator.contains('!')).then(|| DefEntryParts {
                        has_childless_first_child: Some(true),
                        last: after_first,
                        last_kind: Some("N_OpArgs".to_owned()),
                    });
                }
                if kind == "N_PrefixExpr" {
                    return Some(self.get_def_entry_part(Some(true), &args[0], after_first));
                }
                let left = self.get_operand_span(&args[0]);
                let last_kind = if kind == "N_InfixExpr" {
                    "N_GenInfixOp"
                } else {
                    "N_GenPostfixOp"
                };
                Some(get_token_part(
                    self.has_childless_first_child(&args[0], left),
                    left.end + 1,
                    last_kind.to_owned(),
                ))
            }
            _ => None,
        }
    }

    /// `reportDefEntry` (generator.ts 2476–2497).
    pub(super) fn report_def_entry(&mut self, expression: &Expr) -> bool {
        let span = self.get_operand_span(expression);
        let is_name = matches!(
            expression.kind,
            ExpressionKind::Identifier { .. }
                | ExpressionKind::Subexpression { .. }
                | ExpressionKind::OperatorReference { .. }
        );
        if is_name && !self.is_parenthesized(span) {
            return false;
        }
        let Some(DefEntryParts {
            has_childless_first_child: Some(has_childless_first_child),
            last,
            last_kind: Some(last_kind),
        }) = self.get_def_entry_parts(expression, span)
        else {
            return false;
        };
        let last_location = get_span_location(&self.file, last);
        let location = get_span_location(&self.file, span);
        if has_childless_first_child {
            self.add_error(&location, "Was expecting a GeneralId.");
        }
        if last_kind == "N_OpArgs" {
            self.add_error(
                &last_location,
                "Selector `!(...)' should not have argument(s).",
            );
        } else {
            self.add_error(&last_location, "Unexpected token found.");
            self.add_error(
                &last_location,
                format!("Need name or step number here, not `{last_kind}'."),
            );
        }
        self.add_error(
            &location,
            "DEF clause entry should describe a defined operator.",
        );
        true
    }

    /// `generateDefs` (generator.ts 2499–2521).
    pub(super) fn generate_defs(&mut self, defs: &[Fact]) -> Result<Vec<NodeId>> {
        let mut nodes = Vec::new();
        for fact in defs {
            let expression = match fact {
                Fact::Module { name, location } => {
                    nodes.extend(self.get_fact_modules(name, location));
                    continue;
                }
                Fact::Expression(expression) => expression,
            };
            if self.report_def_entry(expression) {
                continue;
            }
            let symbol = match &expression.kind {
                ExpressionKind::OperatorReference { operator, .. } => {
                    let name = Rc::new(Expression::new(
                        ExpressionKind::Identifier {
                            name: operator.clone(),
                            spelling: None,
                            selector_ranges: None,
                        },
                        expression.location.clone(),
                    ));
                    self.generate_selector(&name, -1, false, true)?
                }
                _ => self.generate_selector(expression, -1, false, true)?,
            };
            // SANY rejects the name of a proof step in a DEF clause, and leaves out an entry it
            // rejects. Errors.addMessage drops the message when selectorToNode already reported it.
            let is_definition = match self.spec.graph.kind(symbol) {
                NodeKind::OpDef(_) => true,
                NodeKind::ThmOrAssumpDef(definition) => !definition.name.starts_with('<'),
                _ => false,
            };
            if !is_definition {
                let location = self.get_location(expression);
                self.add_error(
                    &location,
                    "DEF clause entry should describe a defined operator.",
                );
                continue;
            }
            nodes.push(symbol);
        }
        Ok(nodes)
    }

    /// `checkKeywordOnly` (generator.ts 2525–2531), of a USE, HIDE or BY with `is_only`, `facts`
    /// and `defs`.
    pub(super) fn check_keyword_only(
        &mut self,
        is_only: bool,
        facts: &[Fact],
        defs: &[Fact],
        location: &SanyLocation,
    ) {
        if is_only || facts.len() + defs.len() > 0 {
            return;
        }
        self.add_error(location, "Empty BY, USE, or HIDE");
    }

    /// `generateUseOrHide` (generator.ts 2533–2559).
    pub(super) fn generate_use_or_hide(&mut self, use_or_hide: &UseOrHide) -> Result<NodeId> {
        let location = get_span_location(&self.file, self.get_unit_span(&use_or_hide.location));
        self.check_keyword_only(
            use_or_hide.is_only,
            &use_or_hide.facts,
            &use_or_hide.defs,
            &location,
        );
        let facts = self.generate_facts(&use_or_hide.facts)?;
        let defs = self.generate_defs(&use_or_hide.defs)?;
        if facts.len() + defs.len() == 0 {
            self.add_error(&location, "Empty USE or HIDE statement.");
        }
        // UseOrHideNode.factCheck, after SANY generates the node: a HIDE cites facts by name only.
        if use_or_hide.is_hide {
            for &fact in &facts {
                let graph = &self.spec.graph;
                let NodeKind::OpAppl(application) = graph.kind(fact) else {
                    continue;
                };
                if matches!(
                    graph.kind(application.operator),
                    NodeKind::ThmOrAssumpDef(_)
                ) {
                    continue;
                }
                let fact_location = application.location.clone();
                self.add_error(
                    &fact_location,
                    "The only expression allowed as a fact in a HIDE is \nthe name of a theorem, assumption, or step.",
                );
            }
        }
        let uid = self.spec.get_uid();
        Ok(self.spec.graph.add(
            uid,
            NodeKind::UseOrHide(crate::sany::nodes::UseOrHide {
                facts,
                defs,
                is_only: use_or_hide.is_only,
                is_hide: use_or_hide.is_hide,
                location,
            }),
        ))
    }

    /// `generateNewSymbol` (generator.ts 2562–2586).
    pub(super) fn generate_new_symbol(&mut self, symbol: &NewSymbol) -> Result<NodeId> {
        let span = self.get_unit_span(&symbol.location);
        let set = symbol
            .set
            .as_ref()
            .map(|set| self.generate_expression(set))
            .transpose()?;
        // The declaration begins at an infix or postfix operator's first `_`.
        let declaration_start = match &symbol.name_range {
            Some(range) => get_range_span(&self.file, range).start,
            None => self.find_name_or_keyword(span.start, &symbol.name),
        };
        let (decl_kind, level) = get_new_symbol_kind(symbol.level);
        let declaration_uid = self.spec.get_uid();
        let location = get_span_location(
            &self.file,
            self.get_operator_span(declaration_start, symbol.arity),
        );
        let declaration = self.spec.graph.add(
            declaration_uid,
            NodeKind::OpDecl(OpDecl {
                name: resolve_synonym(&symbol.name),
                arity: symbol.arity,
                decl_kind,
                location,
                module: self.module,
            }),
        );
        let levels = self.spec.graph.levels_mut(declaration);
        levels.level_checked = 1;
        levels.level = level;
        self.add_symbol(declaration);
        let uid = self.spec.get_uid();
        Ok(self.spec.graph.add(
            uid,
            NodeKind::NewSymb {
                declaration,
                set,
                location: get_span_location(&self.file, span),
            },
        ))
    }

    /// `assumeProveState.isDeclared[depth] = is_declared`.
    fn set_declared(&mut self, depth: usize, is_declared: bool) {
        let declared = &mut self.assume_prove_state.is_declared;
        if declared.len() <= depth {
            declared.resize(depth + 1, false);
        }
        declared[depth] = is_declared;
    }

    /// `generateAssumeProve` (generator.ts 2589–2667): `goal` is the TypeScript's
    /// `goal?.isSuffices`, `None` without a goal.
    pub(super) fn generate_assume_prove(
        &mut self,
        assume_prove: &AssumeProve,
        depth: usize,
        goal: Option<bool>,
    ) -> Result<NodeId> {
        let file = self.file.clone();
        let span = self.get_unit_span(&assume_prove.location);
        let is_boxed = span
            .start
            .checked_sub(1)
            .is_some_and(|index| is_box_token(&file, index));
        let conclusion_start = get_expression_span(&file, &assume_prove.conclusion).start;
        let prove_index = file.tokens[..conclusion_start.min(file.tokens.len())]
            .iter()
            .rposition(|token| token.kind == TokenKind::Keyword && &*token.text == "PROVE");
        let start = if is_boxed { span.start - 1 } else { span.start };
        let assume_location = get_span_location(
            &file,
            TokenSpan {
                start,
                end: span.start,
            },
        );
        let is_prove_boxed = prove_index
            .and_then(|index| index.checked_sub(1))
            .is_some_and(|index| is_box_token(&file, index));
        if is_boxed != is_prove_boxed {
            self.add_error(
                &assume_location,
                if is_boxed {
                    "[]ASSUME matched by PROVE instead of []PROVE"
                } else {
                    "ASSUME matched by []PROVE instead of PROVE"
                },
            );
        }
        // SANY creates the AssumeProveNode, numbering it, before it generates its clauses.
        let uid = self.spec.get_uid();
        if depth > 1 {
            self.symbol_table
                .contexts
                .push(ContextSlot::Local(LocalContext::default()));
        }
        let is_in_assume = self
            .symbol_table
            .contexts
            .iter()
            .any(|slot| matches!(slot, ContextSlot::Local(local) if local.is_assume));
        if is_boxed && is_in_assume {
            self.add_error(
                &assume_location,
                "[]ASSUME used within the scope of an ordinary ASSUME's assumptions",
            );
        }
        if !is_boxed && let Some(ContextSlot::Local(local)) = self.symbol_table.contexts.last_mut()
        {
            local.is_assume = true;
        }
        let scope = ScopeId(self.scopes.len());
        self.scopes.push(AssumeProveScope {
            is_declared_before: vec![false],
            has_goal: goal.is_some(),
            is_suffices: goal.unwrap_or(false),
            is_in_proof: true,
        });
        self.assume_prove_state.depth = depth;
        self.set_declared(depth, false);
        if depth == 1 {
            self.assume_prove_state.goal = goal.map(|_| scope);
            self.assume_prove_state.goal_clause = 0;
        }
        let mut assumptions = Vec::new();
        for (index, assumption) in assume_prove.assumptions.iter().enumerate() {
            let is_new = matches!(assumption, Assumed::NewSymbol(_));
            let node = match assumption {
                Assumed::AssumeProve(inner) => {
                    self.generate_assume_prove(inner, depth + 1, None)?
                }
                Assumed::NewSymbol(symbol) => self.generate_new_symbol(symbol)?,
                Assumed::Expression(expression) => self.generate_expression(expression)?,
                Assumed::Label {
                    name,
                    body,
                    location,
                    ..
                } => {
                    let label_location = get_span_location(&file, self.get_unit_span(location));
                    self.generate_labeled(name, &[], &[], label_location, true, |generator| {
                        generator.generate_assume_prove(body, depth + 1, None)
                    })?
                }
            };
            self.assume_prove_state.depth = depth;
            if is_new {
                self.set_declared(depth, true);
            }
            let declared_before = &mut self.scopes[scope.0].is_declared_before;
            declared_before.push(declared_before[index] || is_new);
            if depth == 1 {
                self.assume_prove_state.goal_clause += 1;
            }
            assumptions.push(node);
        }
        let conclusion = self.generate_expression(&assume_prove.conclusion)?;
        if depth > 1 {
            self.pop_local_context()?;
        }
        self.assume_prove_state.depth = depth - 1;
        if depth == 1 {
            self.assume_prove_state.goal = None;
        }
        let node = self.spec.graph.add(
            uid,
            NodeKind::AssumeProve(crate::sany::nodes::AssumeProve {
                assumptions,
                goal: conclusion,
                is_suffices: self.scopes[scope.0].is_suffices,
                is_boxed,
                location: get_span_location(
                    &file,
                    TokenSpan {
                        start,
                        end: span.end,
                    },
                ),
            }),
        );
        self.assume_prove_scopes.insert(node, scope);
        Ok(node)
    }

    /// `createTheoremDefinition` (generator.ts 2671–2695). The TypeScript's default `isTheorem` is
    /// true.
    pub(super) fn create_theorem_definition(
        &mut self,
        uid: u32,
        name: Name,
        body: NodeId,
        location: SanyLocation,
        labels: OrderedMap<Name, NodeId>,
        is_theorem: bool,
    ) -> NodeId {
        self.spec.graph.add(
            uid,
            NodeKind::ThmOrAssumpDef(Box::new(ThmOrAssumpDef {
                name,
                is_theorem,
                body,
                params: Vec::new(),
                is_local: false,
                location,
                module: self.module,
                source: None,
                labels,
                is_leibniz_arg: Vec::new(),
                is_leibniz: false,
                op_level_cond: Vec::new(),
                max_levels: Vec::new(),
                min_max_level: Vec::new(),
            })),
        )
    }

    /// `generateLeafProof` (generator.ts 2697–2713). `proof` is not `Steps`.
    pub(super) fn generate_leaf_proof(&mut self, proof: &Proof) -> Result<NodeId> {
        let location = get_span_location(&self.file, self.get_unit_span(&proof.location));
        let (facts, defs, is_only) = match &proof.kind {
            ProofKind::By {
                is_only,
                facts,
                defs,
                ..
            } => {
                self.check_keyword_only(*is_only, facts, defs, &location);
                let facts = self.generate_facts(facts)?;
                let defs = self.generate_defs(defs)?;
                // SANY reads a BY proof's facts and definitions from the UseOrHideNode it makes of
                // them.
                self.spec.get_uid();
                if facts.len() + defs.len() == 0 {
                    self.add_error(&location, "Empty BY");
                }
                (facts, defs, *is_only)
            }
            _ => (Vec::new(), Vec::new(), false),
        };
        let uid = self.spec.get_uid();
        Ok(self.spec.graph.add(
            uid,
            NodeKind::LeafProof(LeafProof {
                facts,
                defs,
                is_omitted: matches!(proof.kind, ProofKind::Omitted { .. }),
                is_only,
                location,
            }),
        ))
    }

    /// `generateStepBody` (generator.ts 2716–2758), whose `undefined` is `None`.
    pub(super) fn generate_step_body(
        &mut self,
        step: &ProofStep,
        body_span: TokenSpan,
    ) -> Result<Option<GeneratedStep>> {
        let file = self.file.clone();
        let body_location = get_span_location(&file, body_span);
        let node = match &step.body {
            StepBody::Have(expression) => {
                let operand = self.generate_expression(expression)?;
                self.apply_builtin("$Have", [operand], body_location, OpApplBinding::default())
            }
            StepBody::Case(expression) => {
                let operand = self.generate_expression(expression)?;
                self.apply_builtin(
                    "$Pfcase",
                    [operand],
                    body_location,
                    OpApplBinding::default(),
                )
            }
            StepBody::Witness(expressions) => {
                let operands = expressions
                    .iter()
                    .map(|expression| self.generate_expression(expression))
                    .collect::<Result<Vec<_>>>()?;
                self.apply_builtin(
                    "$Witness",
                    operands,
                    body_location,
                    OpApplBinding::default(),
                )
            }
            StepBody::Qed => self.apply_builtin(
                "$Qed",
                Vec::<NodeId>::new(),
                body_location,
                OpApplBinding::default(),
            ),
            StepBody::Take { names, bounds, .. } | StepBody::Pick { names, bounds, .. } => {
                let pick_body = match &step.body {
                    StepBody::Pick { body, .. } => Some(body),
                    _ => None,
                };
                let is_pick = pick_body.is_some();
                let name = if is_pick { "$Pick" } else { "$Take" };
                if is_pick {
                    self.symbol_table
                        .contexts
                        .push(ContextSlot::Local(LocalContext::default()));
                }
                if !bounds.is_empty() {
                    let bounds = self.generate_bounds(bounds, body_span.start)?;
                    let operands = match pick_body {
                        Some(body) => {
                            let params = bounds.bounded.iter().flatten().copied().collect();
                            vec![self.generate_with_params(params, body)?]
                        }
                        None => Vec::new(),
                    };
                    let node = self.apply_builtin(name, operands, body_location, bounds.into());
                    return Ok(Some(GeneratedStep { node, is_pick }));
                }
                let indexes = find_name_tokens(&file, body_span.start, body_span.end + 1, names);
                let unbounded: Vec<NodeId> = names
                    .iter()
                    .enumerate()
                    .map(|(index, param_name)| {
                        let location = get_token_location(&file, indexes[index]);
                        self.create_formal_param(param_name.clone(), 0, Some(location), true)
                    })
                    .collect();
                let operands = match pick_body {
                    Some(body) => vec![self.generate_with_params(unbounded.clone(), body)?],
                    None => Vec::new(),
                };
                let binding = OpApplBinding {
                    unbounded: Some(unbounded),
                    ..OpApplBinding::default()
                };
                let node = self.apply_builtin(name, operands, body_location, binding);
                return Ok(Some(GeneratedStep { node, is_pick }));
            }
            _ => return Ok(None),
        };
        Ok(Some(GeneratedStep {
            node,
            is_pick: false,
        }))
    }

    /// `isInfixExpression` (generator.ts 2761–2769): an expression SANY parses as N_InfixExpr.
    pub(super) fn is_infix_expression(&self, expression: &Expr) -> bool {
        match &expression.kind {
            ExpressionKind::Junction { is_bulleted, .. } => !is_bulleted,
            ExpressionKind::Apply { args, .. } if args.len() == 2 => {
                let left = self.get_operand_span(&args[0]);
                let start = get_expression_span(&self.file, expression).start;
                left.start == start && !is_token(&self.file, left.end + 1, "(")
            }
            _ => false,
        }
    }

    /// `generateProof` (generator.ts 2772–2930).
    pub(super) fn generate_proof(&mut self, proof: &Proof) -> Result<NodeId> {
        let ProofKind::Steps { level, steps } = &proof.kind else {
            return self.generate_leaf_proof(proof);
        };
        let file = self.file.clone();
        self.symbol_table
            .contexts
            .push(ContextSlot::Local(LocalContext::default()));
        let proof_context = self.symbol_table.contexts.len() - 1;
        let mut instances = Vec::new();
        let mut suffices_count = 0;
        // An assertion step @ = e continues the infix assertion of the step before it, whose right
        // side the @ stands for.
        let mut previous_right = None;
        let mut step_nodes = Vec::new();
        for step in steps {
            let step_span = self.get_unit_span(&step.location);
            let head_span = get_range_span(&file, &step.head);
            let body_span = TokenSpan {
                start: head_span.start + 1,
                end: head_span.end,
            };
            // Since 2014, SANY's generator names no step whose number is <*> or <+>.
            let is_implicitly_numbered = file.tokens.get(step_span.start).is_some_and(|token| {
                token.text.starts_with("<*>") || token.text.starts_with("<+>")
            });
            if is_implicitly_numbered && step.name.is_some() {
                let location = get_token_location(&file, step_span.start);
                self.add_error(&location, "<*> and <+> cannot be used for a named step.");
            }
            let body = &step.body;
            if step.name.is_some() {
                self.push_label_scope();
            }
            let definition_uid = step.name.as_ref().map(|_| self.spec.get_uid());
            if !matches!(body, StepBody::Assert { .. }) {
                previous_right = None;
            }
            if let Some(other_step) =
                self.generate_other_step(body, step_span, body_span, &mut instances)?
            {
                // SANY puts a NumberedProofStep definition for a named step that asserts nothing in
                // the symbol table, for a DEF clause to name.
                if let Some(name) = &step.name {
                    let definition = OpDef {
                        def_kind: DefKind::NumberedProofStep,
                        labels: self.pop_labels(),
                        step: Some(other_step),
                        ..self.new_op_def(
                            name.clone(),
                            Vec::new(),
                            get_span_location(&file, step_span),
                        )
                    };
                    let definition = self.create_op_def(definition);
                    self.add_symbol(definition);
                }
                step_nodes.push(other_step);
                continue;
            }
            let (is_assume_prove, is_suffices) = match body {
                StepBody::Assert {
                    is_suffices,
                    statement,
                } => (matches!(statement, Statement::AssumeProve(_)), *is_suffices),
                _ => (false, false),
            };
            if is_assume_prove {
                previous_right = None;
            }
            let mut assume_context = LocalContext::default();
            let generated = match body {
                StepBody::Assert { statement, .. } => Some(GeneratedStep {
                    node: self.generate_assertion(
                        statement,
                        step,
                        is_suffices,
                        body_span,
                        &mut assume_context,
                        &mut previous_right,
                    )?,
                    is_pick: false,
                }),
                _ => self.generate_step_body(step, body_span)?,
            };
            let Some(generated) = generated else {
                return not_yet("Unexpected proof step");
            };
            let pick_context = if generated.is_pick {
                Some(self.pop_local_context()?)
            } else {
                None
            };
            let definition = match (&step.name, definition_uid) {
                (Some(name), Some(uid)) => {
                    let location =
                        get_token_location(&file, get_token_index(&file, step.location.position()));
                    let labels = self.pop_labels();
                    Some(self.create_theorem_definition(
                        uid,
                        name.clone(),
                        generated.node,
                        location,
                        labels,
                        true,
                    ))
                }
                _ => None,
            };
            if let Some(definition) = definition {
                self.add_symbol(definition);
            }
            let is_scoped = is_assume_prove && !is_suffices;
            if is_scoped {
                self.symbol_table
                    .contexts
                    .push(ContextSlot::Local(std::mem::take(&mut assume_context)));
            }
            let step_proof = step
                .proof
                .as_ref()
                .map(|proof| self.generate_proof(proof))
                .transpose()?;
            if is_scoped {
                self.pop_local_context()?;
            }
            self.end_proof(generated.node);
            if is_assume_prove && is_suffices {
                suffices_count += 1;
                self.symbol_table
                    .contexts
                    .push(ContextSlot::Local(assume_context));
            }
            if let Some(pick_context) = pick_context {
                pick_context
                    .context
                    .symbols
                    .iter()
                    .for_each(|&symbol| self.add_symbol(symbol));
            }
            let uid = self.spec.get_uid();
            step_nodes.push(self.spec.graph.add(
                uid,
                NodeKind::Theorem(crate::sany::nodes::Theorem {
                    definition,
                    body: generated.node,
                    proof: step_proof,
                    is_suffices,
                    location: get_span_location(&file, step_span),
                }),
            ));
        }
        for _ in 0..suffices_count {
            let suffices_context = self.pop_local_context()?;
            let ContextSlot::Local(proof_context) = &mut self.symbol_table.contexts[proof_context]
            else {
                return not_yet("a proof's context that is a module's");
            };
            for &symbol in &suffices_context.context.symbols {
                add_to_context(&self.spec.graph, &mut proof_context.context, symbol);
            }
        }
        self.pop_local_context()?;
        let Ok(proof_level) = u32::try_from(*level) else {
            return not_yet("a proof without a level");
        };
        let uid = self.spec.get_uid();
        Ok(self.spec.graph.add(
            uid,
            NodeKind::NonLeafProof(NonLeafProof {
                steps: step_nodes,
                instances,
                proof_level,
                location: get_span_location(&file, self.get_unit_span(&proof.location)),
            }),
        ))
    }

    /// `generateOtherStep` in `generateProof` (generator.ts 2784–2815): a DEFINE, USE, HIDE or
    /// INSTANCE step, whose instances join the proof's `instances`.
    pub(super) fn generate_other_step(
        &mut self,
        body: &StepBody,
        step_span: TokenSpan,
        body_span: TokenSpan,
        instances: &mut Vec<NodeId>,
    ) -> Result<Option<NodeId>> {
        match body {
            StepBody::Define { definitions, .. } => {
                let mut defs = Vec::new();
                for definition in definitions {
                    let mut defined = Vec::new();
                    let last = match definition {
                        DefinitionUnit::Instance(instance) => {
                            self.process_module_definition(
                                instance,
                                Some(&mut defined),
                                Some(instances),
                            )?;
                            defined.last().copied()
                        }
                        DefinitionUnit::Definition(definition) => {
                            match definition.kind {
                                DefinitionKind::Function { .. } => {
                                    self.process_function(definition, Some(&mut defined))?
                                }
                                DefinitionKind::Operator { .. } => {
                                    self.process_operator(definition, Some(&mut defined))?
                                }
                            }
                            defined.first().copied()
                        }
                    };
                    match last {
                        Some(last) if self.spec.graph.op_def(last).is_some() => defs.push(last),
                        _ => return not_yet("A DEFINE step defines no operator"),
                    }
                }
                let uid = self.spec.get_uid();
                Ok(Some(self.spec.graph.add(
                    uid,
                    NodeKind::DefStep {
                        defs,
                        location: get_span_location(&self.file, body_span),
                    },
                )))
            }
            StepBody::UseOrHide(use_or_hide) => {
                let node = self.generate_use_or_hide(use_or_hide)?;
                if let NodeKind::UseOrHide(use_or_hide) = &mut self.spec.graph.node_mut(node).kind {
                    use_or_hide.location = get_span_location(&self.file, step_span);
                }
                Ok(Some(node))
            }
            StepBody::Instance(instance) => {
                let location = get_span_location(&self.file, body_span);
                Ok(Some(self.generate_instance(
                    instance,
                    false,
                    Some(location),
                )?))
            }
            _ => Ok(None),
        }
    }

    /// `generateAssertion` in `generateProof` (generator.ts 2846–2880). `previous_right` is
    /// `infixStep.previousRight`, and `assume_context` the step's `assumeContext`, which the
    /// assertion takes for the context of an ASSUME/PROVE and gives back.
    pub(super) fn generate_assertion(
        &mut self,
        statement: &Statement,
        step: &ProofStep,
        is_suffices: bool,
        body_span: TokenSpan,
        assume_context: &mut LocalContext,
        previous_right: &mut Option<NodeId>,
    ) -> Result<NodeId> {
        let statement = match statement {
            Statement::AssumeProve(assume_prove) => {
                let goal = step.name.as_ref().map(|_| is_suffices);
                let (node, context) = self
                    .with_context(std::mem::take(assume_context), |generator| {
                        generator.generate_assume_prove(assume_prove, 1, goal)
                    })?;
                *assume_context = context;
                if let NodeKind::AssumeProve(node) = &mut self.spec.graph.node_mut(node).kind {
                    node.is_suffices = is_suffices;
                }
                return Ok(node);
            }
            Statement::Expression(expression) => expression,
        };
        if is_suffices {
            let expression = self.generate_expression(statement)?;
            let location = get_span_location(&self.file, body_span);
            return Ok(self.apply_builtin(
                "$Suffices",
                [expression],
                location,
                OpApplBinding::default(),
            ));
        }
        let at_step = match (&statement.kind, *previous_right) {
            (ExpressionKind::Apply { operator, args, .. }, Some(previous))
                if self.is_infix_expression(statement)
                    && matches!(args[0].kind, ExpressionKind::ExceptAt) =>
            {
                Some((operator, args, previous))
            }
            _ => None,
        };
        let expression = match at_step {
            // SANY generates an @ step's right side before the $Nop that stands for its @.
            Some((operator, args, previous)) => {
                let at_right = self.generate_expression(&args[1])?;
                let location = self.get_location(statement);
                let resolved = self.resolve_name(operator, &location)?;
                let at_location = self.get_location(&args[0]);
                let at =
                    self.apply_builtin("$Nop", [previous], at_location, OpApplBinding::default());
                self.create_op_appl(resolved, [at, at_right], location, OpApplBinding::default())
            }
            None => self.generate_expression(statement)?,
        };
        let right = match self.spec.graph.kind(expression) {
            NodeKind::OpAppl(application) => application.operands.get(1).copied().flatten(),
            _ => None,
        };
        *previous_right = if self.is_infix_expression(statement) {
            right
        } else {
            None
        };
        Ok(expression)
    }

    /// `processTheorem` (generator.ts 2934–2972).
    pub(super) fn process_theorem(&mut self, theorem: &Theorem) -> Result<()> {
        let location = get_span_location(&self.file, self.get_unit_span(&theorem.location));
        let assume_prove = match &theorem.statement {
            Statement::AssumeProve(assume_prove) => Some(assume_prove),
            Statement::Expression(_) => None,
        };
        if theorem.name.is_some() {
            self.push_label_scope();
        }
        let definition_uid = theorem.name.as_ref().map(|_| self.spec.get_uid());
        if assume_prove.is_some() {
            self.symbol_table
                .contexts
                .push(ContextSlot::Local(LocalContext::default()));
        }
        let body = match &theorem.statement {
            Statement::AssumeProve(assume_prove) => {
                let goal = theorem.name.as_ref().map(|_| false);
                self.generate_assume_prove(assume_prove, 1, goal)?
            }
            Statement::Expression(expression) => self.generate_expression(expression)?,
        };
        let definition = match (&theorem.name, definition_uid) {
            (Some(name), Some(uid)) => {
                let labels = self.pop_labels();
                Some(self.create_theorem_definition(
                    uid,
                    name.clone(),
                    body,
                    location.clone(),
                    labels,
                    true,
                ))
            }
            _ => None,
        };
        if let Some(definition) = definition {
            let assume_context = assume_prove.map(|_| self.pop_local_context()).transpose()?;
            self.add_symbol(definition);
            self.module_node_mut().definitions.push(definition);
            if let Some(assume_context) = assume_context {
                self.symbol_table
                    .contexts
                    .push(ContextSlot::Local(assume_context));
            }
        }
        let proof = theorem
            .proof
            .as_ref()
            .map(|proof| self.generate_proof(proof))
            .transpose()?;
        if assume_prove.is_some() {
            self.pop_local_context()?;
        }
        self.end_proof(body);
        let uid = self.spec.get_uid();
        let node = self.spec.graph.add(
            uid,
            NodeKind::Theorem(crate::sany::nodes::Theorem {
                definition,
                body,
                proof,
                is_suffices: false,
                location,
            }),
        );
        self.module_node_mut().top_level.push(node);
        Ok(())
    }

    /// `processAssumption` (generator.ts 2974–2995).
    pub(super) fn process_assumption(&mut self, assumption: &Assumption) -> Result<()> {
        let span = self.get_unit_span(&assumption.location);
        let location = get_span_location(&self.file, span);
        if assumption.name.is_some() {
            self.push_label_scope();
        }
        let body = self.generate_expression(&assumption.expression)?;
        let definition = match &assumption.name {
            Some(name) => {
                let uid = self.spec.get_uid();
                let labels = self.pop_labels();
                Some(self.create_theorem_definition(
                    uid,
                    name.clone(),
                    body,
                    location.clone(),
                    labels,
                    false,
                ))
            }
            None => None,
        };
        if let Some(definition) = definition {
            self.add_symbol(definition);
            self.module_node_mut().definitions.push(definition);
        }
        let uid = self.spec.get_uid();
        let node = self.spec.graph.add(
            uid,
            NodeKind::Assume {
                definition,
                body,
                location,
            },
        );
        self.module_node_mut().top_level.push(node);
        Ok(())
    }

    /// `currentModule`, to change.
    fn module_node_mut(&mut self) -> &mut crate::sany::nodes::Module {
        self.spec.graph.module_mut(self.module).expect("a module")
    }
}
