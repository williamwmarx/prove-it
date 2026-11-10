//! The definitions, instances and units of `generateModule` (`generator.ts` lines 1816–2334 and
//! 2999–3139): operators, functions, RECURSIVE, substitutions, instances, declarations, the
//! EXTENDS list and the loop over the module's units.

use std::mem::discriminant;
use std::rc::Rc;

use crate::ast::{Declaration, Definition, DefinitionKind, Instance, Location, ModuleUnit};
use crate::levels::TEMPORAL_LEVEL;
use crate::sany::nodes::{
    CONSTANT_DECL_KIND, DefKind, MessageLocation, NodeId, NodeKind, OpDecl, OpDef, SanyLocation,
    Subst, SubstIn, ThmOrAssumpDef, VARIABLE_DECL_KIND, format_sany_location,
};
use crate::sany::source::{
    TokenSpan, find_token, get_expression_span, get_matching_index, get_pre_comments,
    get_span_location, get_token_location, get_token_source, is_token,
};
use crate::sany::{Result, not_yet};

use super::{
    ContextSlot, LocalContext, ModuleGenerator, OpApplBinding, RecursiveFunction, get_kind_name,
    get_slot_context, get_symbol_arity, is_parameter_free, is_same_origin, resolve_synonym,
};

impl ModuleGenerator<'_> {
    /// Whether a symbol is an OpDefNode declared RECURSIVE and not yet defined.
    fn is_pending_recursive(&self, symbol: NodeId) -> bool {
        self.spec
            .graph
            .op_def(symbol)
            .is_some_and(|definition| definition.in_recursive && !definition.is_defined)
    }

    /// `currentModule.definitions.push(node)` and `definitions?.push(node)`.
    fn add_definition(&mut self, node: NodeId, definitions: Option<&mut Vec<NodeId>>) {
        self.spec
            .graph
            .module_mut(self.module)
            .expect("a module")
            .definitions
            .push(node);
        if let Some(definitions) = definitions {
            definitions.push(node);
        }
    }

    /// `(definitions ?? currentModule.definitions).push(node)`.
    fn push_definition(&mut self, node: NodeId, definitions: Option<&mut Vec<NodeId>>) {
        match definitions {
            Some(definitions) => definitions.push(node),
            None => self
                .spec
                .graph
                .module_mut(self.module)
                .expect("a module")
                .definitions
                .push(node),
        }
    }

    /// `processOperator` (generator.ts 1816–1880). `definition` is an operator definition, and
    /// `definitions` the definitions of the LET or DEFINE step that holds it, if any.
    pub(super) fn process_operator(
        &mut self,
        definition: &Rc<Definition>,
        definitions: Option<&mut Vec<NodeId>>,
    ) -> Result<()> {
        let DefinitionKind::Operator {
            params: definition_params,
            ..
        } = &definition.kind
        else {
            return not_yet("Expected an operator definition");
        };
        let span = self.get_definition_span(&definition.location, definition.is_local);
        let location = get_span_location(&self.file, span);
        let name = resolve_synonym(&definition.name);
        let params_span = TokenSpan {
            start: if definition.is_local {
                span.start + 1
            } else {
                span.start
            },
            end: span.end,
        };
        let ((params, body, existing), _) =
            self.with_context(LocalContext::default(), |generator| {
                let params = generator.get_params(definition_params, params_span, true);
                let existing = generator.resolve_symbol(&name);
                match existing {
                    Some(pending) if generator.is_pending_recursive(pending) => {
                        let graph = &generator.spec.graph;
                        let pending = graph.op_def(pending).expect("a definition");
                        // SANY compares only the arity of the last parameter.
                        let is_matching = pending.params.as_ref().map(Vec::len)
                            == Some(params.len())
                            && params
                                .last()
                                .is_none_or(|&last| graph.node(last).symbol_arity() == 0);
                        let pending_name = pending.name.clone();
                        if pending.let_in_level != generator.state.cur_level {
                            generator.add_error(
                                &location,
                                format!("Recursive operator {name} defined at wrong LET/IN level."),
                            );
                        } else if !is_matching {
                            generator.add_error(
                                &location,
                                format!(
                                    "Definition of {pending_name} has different arity than its RECURSIVE declaration."
                                ),
                            );
                        }
                    }
                    Some(_) => generator.add_error(
                        &location,
                        format!("Operator {name} already defined or declared."),
                    ),
                    None => {}
                }
                generator.push_label_scope();
                let body = generator.generate_expression(&definition.body)?;
                Ok((params, body, existing))
            })?;
        let labels = self.pop_labels();
        let pre_comments = get_pre_comments(&self.file, span.start);
        let recursive = existing.filter(|&symbol| {
            self.is_pending_recursive(symbol)
                && self
                    .spec
                    .graph
                    .op_def(symbol)
                    .expect("a definition")
                    .let_in_level
                    == self.state.cur_level
        });
        if let Some(recursive) = recursive {
            // OpDefNode.setParams keeps the arity of the RECURSIVE declaration.
            let count = params.len();
            let node = self.spec.graph.op_def_mut(recursive).expect("a definition");
            node.params = Some(params);
            node.weights = vec![0; count];
            node.max_levels = vec![TEMPORAL_LEVEL; count];
            node.is_leibniz_arg = Some(vec![true; count]);
            node.labels = labels;
            self.end_op_def_node(recursive, body, location, pre_comments);
            self.add_definition(recursive, definitions);
            return Ok(());
        }
        let node = self.create_op_def(OpDef {
            body: Some(body),
            is_local: definition.is_local,
            pre_comments,
            labels,
            ..self.new_op_def(name, params, location)
        });
        self.add_symbol(node);
        self.set_recursion_fields(node);
        self.add_definition(node, definitions);
        Ok(())
    }

    /// `endOpDefNode` (generator.ts 1882–1896).
    pub(super) fn end_op_def_node(
        &mut self,
        node: NodeId,
        body: NodeId,
        location: SanyLocation,
        pre_comments: Vec<String>,
    ) {
        let definition = self.spec.graph.op_def_mut(node).expect("a definition");
        definition.is_defined = true;
        definition.body = Some(body);
        definition.location = location;
        definition.pre_comments = pre_comments;
        if definition.in_recursive {
            self.state.unresolved_count[self.state.cur_level as usize] -= 1;
            self.state.unresolved_sum -= 1;
        }
    }

    /// `processFunction` (generator.ts 1898–1969). `definition` is a function definition.
    pub(super) fn process_function(
        &mut self,
        definition: &Rc<Definition>,
        definitions: Option<&mut Vec<NodeId>>,
    ) -> Result<()> {
        let DefinitionKind::Function { bounds } = &definition.kind else {
            return not_yet("Expected a function definition");
        };
        let span = self.get_definition_span(&definition.location, definition.is_local);
        let location = get_span_location(&self.file, span);
        let name_index = if definition.is_local {
            span.start + 1
        } else {
            span.start
        };
        let (bounds, context) = self.with_context(LocalContext::default(), |generator| {
            generator.generate_bounds(bounds, name_index + 1)
        })?;
        let existing = self.resolve_symbol(&definition.name);
        let (recursion_param, context) = self.with_context(context, |generator| {
            Ok(generator.create_formal_param(
                definition.name.clone(),
                0,
                Some(location.clone()),
                existing.is_none(),
            ))
        })?;
        let bounded = bounds.bounded.clone();
        let node = self.apply_builtin(
            "$NonRecursiveFcnSpec",
            Vec::<NodeId>::new(),
            location.clone(),
            OpApplBinding {
                unbounded: Some(vec![recursion_param]),
                ..OpApplBinding::from(bounds)
            },
        );
        let is_pending_recursive = existing.is_some_and(|symbol| self.is_pending_recursive(symbol));
        let recursive = existing.filter(|&symbol| {
            is_pending_recursive
                && self
                    .spec
                    .graph
                    .op_def(symbol)
                    .expect("a definition")
                    .let_in_level
                    == self.state.cur_level
        });
        if let Some(recursive) = recursive {
            let recursive = self.spec.graph.op_def(recursive).expect("a definition");
            if recursive.arity != 0 {
                let text = format!(
                    "Function {} has operator arguments in its RECURSIVE declaration.",
                    recursive.name
                );
                self.add_error(&location, text);
            }
        } else if is_pending_recursive {
            self.add_error(
                &location,
                format!(
                    "Recursive function {} defined at wrong LET/IN level.",
                    definition.name
                ),
            );
        } else if existing.is_some() {
            self.add_error(
                &location,
                format!(
                    "Function name `{}' already defined or declared.",
                    definition.name
                ),
            );
        }
        let pre_comments = get_pre_comments(&self.file, span.start);
        // Generator.processFunction's OpDefNode: a new one, or the one the name already has, though
        // defined, unless that is declared RECURSIVE at another level.
        let definition_node = match existing {
            None => Some(self.create_op_def(OpDef {
                body: Some(node),
                is_local: definition.is_local,
                pre_comments: pre_comments.clone(),
                ..self.new_op_def(definition.name.clone(), Vec::new(), location.clone())
            })),
            Some(symbol)
                if self.spec.graph.op_def(symbol).is_some()
                    && (recursive.is_some() || !is_pending_recursive) =>
            {
                Some(symbol)
            }
            Some(_) => None,
        };
        // A function whose RECURSIVE declaration has parameters stays undefined.
        if let Some(recursive) = recursive {
            if self
                .spec
                .graph
                .op_def(recursive)
                .expect("a definition")
                .arity
                == 0
            {
                self.end_op_def_node(recursive, node, location, pre_comments);
            }
        } else if existing.is_none()
            && let Some(definition_node) = definition_node
        {
            self.add_symbol(definition_node);
            self.set_recursion_fields(definition_node);
        }
        if let Some(definition_node) = definition_node {
            self.add_definition(definition_node, definitions);
        }
        self.functions.insert(
            0,
            RecursiveFunction {
                name: definition.name.clone(),
                node,
            },
        );
        self.push_label_scope();
        // The bound identifiers are bound in the body only of a function with an OpDefNode.
        let params: Vec<NodeId> = bounded.into_iter().flatten().collect();
        let body = match definition_node {
            None => self.generate_with_params(params, &definition.body)?,
            Some(_) => {
                self.with_context(context, |generator| {
                    generator.generate_with_params(params, &definition.body)
                })?
                .0
            }
        };
        let labels = self.pop_labels();
        if let Some(definition_node) = definition_node {
            self.spec
                .graph
                .op_def_mut(definition_node)
                .expect("a definition")
                .labels = labels;
        }
        self.functions.remove(0);
        let non_recursive = self.get_builtin("$NonRecursiveFcnSpec");
        if let NodeKind::OpAppl(application) = &mut self.spec.graph.node_mut(node).kind {
            application.operands = vec![Some(body)];
            if application.operator == non_recursive {
                application.unbounded = None;
            }
        }
        Ok(())
    }

    /// `processRecursive` (generator.ts 1971–1996).
    pub(super) fn process_recursive(&mut self, declarations: &[Rc<Declaration>]) {
        if self.state.unresolved_sum == 0 {
            self.state.recursive_section_count += 1;
        }
        let count = i32::try_from(declarations.len()).expect("fewer than 2^31 declarations");
        self.state.unresolved_count[self.state.cur_level as usize] += count;
        self.state.unresolved_sum += count;
        for declaration in declarations {
            let span = self.get_declaration_span(declaration);
            // The OpDeclNode buildParameter makes of the declaration to read its name and arity.
            self.spec.get_uid();
            let params = (0..declaration.arity)
                .map(|_| self.create_formal_param(Rc::from(""), 0, None, false))
                .collect();
            let node = self.create_op_def(OpDef {
                is_defined: false,
                in_recursive: true,
                in_recursive_section: true,
                recursive_section: self.state.recursive_section_count,
                let_in_level: self.state.cur_level,
                ..self.new_op_def(
                    resolve_synonym(&declaration.name),
                    params,
                    get_span_location(&self.file, span),
                )
            });
            self.add_symbol(node);
            self.recursive_declarations.push(node);
            self.spec
                .graph
                .module_mut(self.module)
                .expect("a module")
                .op_defs_in_recursive_section
                .push(node);
        }
    }

    /// `checkForUndefinedRecursiveOps` (generator.ts 1998–2010).
    pub(super) fn check_for_undefined_recursive_ops(&mut self) {
        let level = self.state.cur_level as usize;
        if self.state.unresolved_count[level] == 0 {
            return;
        }
        let undefined: Vec<(SanyLocation, String)> = self
            .recursive_declarations
            .iter()
            .filter_map(|&node| self.spec.graph.op_def(node))
            .filter(|node| node.let_in_level == self.state.cur_level && !node.is_defined)
            .map(|node| {
                (
                    node.location.clone(),
                    format!(
                        "Symbol {} declared in RECURSIVE statement but not defined.",
                        node.name
                    ),
                )
            })
            .collect();
        for (location, text) in undefined {
            self.add_error(&location, text);
        }
        self.state.unresolved_sum -= self.state.unresolved_count[level];
    }

    /// `processSubstitutions` (generator.ts 2014–2099): SubstInNode's constructor and
    /// processSubst, for an instance of `instancee`, the module whose context the TypeScript
    /// passes. An implicit substitution for each declaration of the instantiated module whose name
    /// the instantiating module can resolve, in the order of the instantiated module's Hashtable,
    /// then the explicit WITH substitutions.
    pub(super) fn process_substitutions(
        &mut self,
        instance: &Instance,
        instancee: NodeId,
        location: &SanyLocation,
    ) -> Result<Vec<Subst>> {
        // The SubstInNode processSubst creates to hold the substitutions, which only their
        // templates use.
        self.spec.get_uid();
        let declarations: Vec<(NodeId, OpDecl)> = self
            .spec
            .graph
            .module(instancee)
            .expect("a module")
            .context
            .get_hashtable_values()
            .into_iter()
            .filter_map(|symbol| match self.spec.graph.kind(symbol) {
                NodeKind::OpDecl(declaration) => Some((symbol, declaration.clone())),
                _ => None,
            })
            .collect();
        let mut substs = Vec::new();
        for (op, declaration) in &declarations {
            let op = *op;
            let Some(symbol) = self.resolve_symbol(&declaration.name) else {
                continue;
            };
            let is_expression = declaration.decl_kind == VARIABLE_DECL_KIND
                || (declaration.decl_kind == CONSTANT_DECL_KIND && declaration.arity == 0);
            let expr = if is_expression {
                self.create_op_appl(
                    symbol,
                    Vec::<NodeId>::new(),
                    location.clone(),
                    OpApplBinding::default(),
                )
            } else {
                self.create_op_arg(symbol, location.clone())
            };
            substs.push(Subst {
                op,
                expr,
                is_implicit: true,
            });
        }
        let file = self.file.clone();
        let span = self.get_definition_span(&instance.location, instance.is_local);
        // The targets follow WITH, after the parameters of a definition that instantiates.
        let mut cursor =
            find_token(&file, span.start, span.end, "WITH").map_or(0, |index| index + 1);
        for substitution in &instance.substitutions {
            let target_index = find_token(&file, cursor, span.end, &substitution.name);
            // The next target follows this substitution's expression, which may name it too.
            if target_index.is_some() {
                cursor = get_expression_span(&file, &substitution.expression).end + 1;
            }
            let target = self
                .spec
                .graph
                .module(instancee)
                .expect("a module")
                .context
                .get_symbol(&resolve_synonym(&substitution.name))
                .filter(|&target| matches!(self.spec.graph.kind(target), NodeKind::OpDecl(_)));
            let Some(target) = target else {
                let (error_location, identifier) = match target_index {
                    None => (location.clone(), substitution.name.to_string()),
                    Some(index) => (
                        get_token_location(&file, index),
                        get_token_source(&file, index).to_owned(),
                    ),
                };
                self.add_error(
                    &error_location,
                    format!(
                        "Identifier '{identifier}' is not a legal target of a substitution. \nA legal target must be a declared CONSTANT or VARIABLE in the module being instantiated. \n(Also, check for warnings about multiple declarations of this same identifier.)"
                    ),
                );
                continue;
            };
            let target_name = self
                .spec
                .graph
                .node(target)
                .symbol_name()
                .expect("a symbol")
                .clone();
            let substitute = if self.spec.graph.node(target).symbol_arity() == 0 {
                self.generate_expression(&substitution.expression)?
            } else {
                self.generate_operator_argument(&substitution.expression, target)?
            };
            self.check_arity(target, substitute);
            let existing = substs.iter().position(|subst| {
                self.spec.graph.node(subst.op).symbol_name() == Some(&target_name)
            });
            match existing {
                Some(existing) if !substs[existing].is_implicit => {
                    let error_location = self.get_location(&substitution.expression);
                    self.add_error(
                        &error_location,
                        format!(
                            "Multiple substitutions for symbol '{target_name}' in substitution."
                        ),
                    );
                }
                Some(existing) => {
                    substs[existing].expr = substitute;
                    substs[existing].is_implicit = false;
                }
                None => substs.push(Subst {
                    op: target,
                    expr: substitute,
                    is_implicit: false,
                }),
            }
        }
        for subst in substs.iter().filter(|subst| subst.is_implicit) {
            self.check_arity(subst.op, subst.expr);
        }
        // SubstInNode.matchAll.
        let module_name = self
            .spec
            .graph
            .module(self.module)
            .expect("a module")
            .name
            .clone();
        for (_, declaration) in &declarations {
            let is_substituted = substs.iter().any(|subst| {
                self.spec.graph.node(subst.op).symbol_name() == Some(&declaration.name)
            });
            if !is_substituted {
                self.add_error(
                    location,
                    format!(
                        "Substitution missing for symbol {} declared at {} \nand instantiated in module {module_name}.",
                        declaration.name,
                        format_sany_location(&MessageLocation::At(declaration.location.clone()))
                    ),
                );
            }
        }
        Ok(substs)
    }

    /// `checkArity` in `processSubstitutions` (generator.ts 2041–2051):
    /// Generator.checkSubstitutionForCorrectArity, which SANY locates in its builtins for the
    /// nullOpArg it substitutes after an error.
    pub(super) fn check_arity(&mut self, target: NodeId, substitute: NodeId) {
        let graph = &self.spec.graph;
        let NodeKind::OpDecl(declaration) = graph.kind(target) else {
            return;
        };
        let target_arity = i32::try_from(declaration.arity).expect("an arity below 2^31");
        let arity = match graph.kind(substitute) {
            NodeKind::OpArg { op, .. } => get_symbol_arity(graph, *op),
            _ => 0,
        };
        let is_null_op_arg = target_arity > 0
            && matches!(graph.kind(substitute), NodeKind::OpAppl(application) if application.is_null);
        if arity != target_arity && !is_null_op_arg {
            let text = format!(
                "An operator must be substituted for symbol '{}', and it must have arity {target_arity}.",
                declaration.name
            );
            let location = graph
                .node(substitute)
                .location()
                .cloned()
                .expect("a location");
            self.add_error(&location, text);
        }
    }

    /// `createSubstIn` (generator.ts 2101–2126): a SubstIn, or an APSubstIn when
    /// `is_assume_prove`. The TypeScript's default `instantiatingModule` is `self.module`.
    pub(super) fn create_subst_in(
        &mut self,
        is_assume_prove: bool,
        substs: Vec<Subst>,
        body: NodeId,
        instantiated_module: NodeId,
        location: SanyLocation,
        instantiating_module: NodeId,
    ) -> NodeId {
        if self.spec.graph.node(body).is_absent() {
            self.add_error(
                &location,
                if is_assume_prove {
                    "Substitution error, probably due to error in module being instantiated."
                } else {
                    "Substitution error, probably due to error \nin module being instantiated."
                },
            );
        }
        let uid = self.spec.get_uid();
        self.spec.graph.add(
            uid,
            NodeKind::SubstIn(SubstIn {
                is_assume_prove,
                substs,
                body,
                instantiating_module,
                instantiated_module,
                location,
            }),
        )
    }

    /// `processModuleDefinition` (generator.ts 2128–2235): a named instance, `I == INSTANCE M`.
    /// `None` for `definitions` and `instances` is the TypeScript's `undefined`.
    pub(super) fn process_module_definition(
        &mut self,
        instance: &Rc<Instance>,
        mut definitions: Option<&mut Vec<NodeId>>,
        instances: Option<&mut Vec<NodeId>>,
    ) -> Result<()> {
        let span = self.get_definition_span(&instance.location, instance.is_local);
        let location = get_span_location(&self.file, span);
        let pre_comments = get_pre_comments(&self.file, span.start);
        let name = instance.name.clone().unwrap_or_else(|| Rc::from(""));
        let name_index = if instance.is_local {
            span.start + 1
        } else {
            span.start
        };
        let has_params = !instance.params.is_empty();
        if has_params {
            self.symbol_table
                .contexts
                .push(ContextSlot::Local(LocalContext::default()));
        }
        let args = self.get_params(
            &instance.params,
            TokenSpan {
                start: name_index,
                end: span.end,
            },
            has_params,
        );
        let instancee = self.get_module(&instance.module)?;
        let substs = self.process_substitutions(instance, instancee, &location)?;
        if has_params {
            self.pop_local_context()?;
        }
        let symbols = self
            .spec
            .graph
            .module(instancee)
            .expect("a module")
            .context
            .get_hashtable_values();
        for &symbol in &symbols {
            let Some(definition) = self.spec.graph.op_def(symbol).cloned() else {
                continue;
            };
            if definition.is_local
                || !matches!(
                    definition.def_kind,
                    DefKind::UserDefined | DefKind::ModuleInstance
                )
            {
                continue;
            }
            let params: Vec<NodeId> = args
                .iter()
                .copied()
                .chain(definition.params.clone().unwrap_or_default())
                .collect();
            let qualified_name: Rc<str> = Rc::from(format!("{name}!{}", definition.name));
            let source = Some(definition.source.unwrap_or(symbol));
            let node = if definition.def_kind == DefKind::UserDefined {
                let body = match definition.body {
                    Some(body) if !substs.is_empty() => Some(self.create_subst_in(
                        false,
                        substs.clone(),
                        body,
                        instancee,
                        location.clone(),
                        self.module,
                    )),
                    body => body,
                };
                self.create_op_def(OpDef {
                    body,
                    is_local: instance.is_local,
                    source,
                    pre_comments: pre_comments.clone(),
                    labels: definition.labels.clone(),
                    ..self.new_op_def(qualified_name, params, location.clone())
                })
            } else {
                self.create_op_def(OpDef {
                    def_kind: DefKind::ModuleInstance,
                    is_local: instance.is_local,
                    module: definition.module,
                    source,
                    pre_comments: pre_comments.clone(),
                    ..self.new_op_def(qualified_name, params, location.clone())
                })
            };
            self.add_symbol(node);
            if definition.def_kind == DefKind::UserDefined {
                self.set_recursion_fields(node);
            }
            self.push_definition(node, definitions.as_deref_mut());
        }
        for &symbol in &symbols {
            let NodeKind::ThmOrAssumpDef(definition) = self.spec.graph.kind(symbol) else {
                continue;
            };
            let definition = definition.as_ref().clone();
            if definition.is_local {
                continue;
            }
            // SANY creates the APSubstInNode before the ThmOrAssumpDefNode that holds it.
            let body = if substs.is_empty() {
                definition.body
            } else {
                self.create_subst_in(
                    true,
                    substs.clone(),
                    definition.body,
                    instancee,
                    location.clone(),
                    self.module,
                )
            };
            let uid = self.spec.get_uid();
            let node = self.spec.graph.add(
                uid,
                NodeKind::ThmOrAssumpDef(Box::new(ThmOrAssumpDef {
                    name: Rc::from(format!("{name}!{}", definition.name)),
                    is_theorem: definition.is_theorem,
                    body,
                    params: args.iter().copied().chain(definition.params).collect(),
                    is_local: instance.is_local,
                    location: location.clone(),
                    module: self.module,
                    source: Some(definition.source.unwrap_or(symbol)),
                    labels: definition.labels,
                    is_leibniz_arg: Vec::new(),
                    is_leibniz: false,
                    op_level_cond: Vec::new(),
                    max_levels: Vec::new(),
                    min_max_level: Vec::new(),
                })),
            );
            self.add_symbol(node);
            self.push_definition(node, definitions.as_deref_mut());
        }
        let uid = self.spec.get_uid();
        let instance_node = self.spec.graph.add(
            uid,
            NodeKind::Instance(crate::sany::nodes::Instance {
                name: Some(name.clone()),
                is_local: instance.is_local,
                params: args.clone(),
                module: instancee,
                substs,
                location: location.clone(),
            }),
        );
        match instances {
            Some(instances) => instances.push(instance_node),
            None => self
                .spec
                .graph
                .module_mut(self.module)
                .expect("a module")
                .top_level
                .push(instance_node),
        }
        let module_definition = self.create_op_def(OpDef {
            def_kind: DefKind::ModuleInstance,
            is_local: instance.is_local,
            pre_comments,
            ..self.new_op_def(name, args, location)
        });
        self.add_symbol(module_definition);
        if let Some(definitions) = definitions {
            definitions.push(module_definition);
        }
        Ok(())
    }

    /// `generateInstance` (generator.ts 2237–2332): an unnamed INSTANCE, at the top level or as a
    /// proof step located at `step_location`, which adds no theorem definitions or instance to the
    /// module. The TypeScript's default `isTopLevel` is true.
    pub(super) fn generate_instance(
        &mut self,
        instance: &Rc<Instance>,
        is_top_level: bool,
        step_location: Option<SanyLocation>,
    ) -> Result<NodeId> {
        let span = self.get_definition_span(&instance.location, instance.is_local);
        let location = step_location.unwrap_or_else(|| get_span_location(&self.file, span));
        let pre_comments = get_pre_comments(&self.file, span.start);
        let instancee = self.get_module(&instance.module)?;
        let substs = self.process_substitutions(instance, instancee, &location)?;
        let is_local = instance.is_local;
        let is_instancee_parameter_free = is_parameter_free(&self.spec.graph, instancee);
        let symbols = self
            .spec
            .graph
            .module(instancee)
            .expect("a module")
            .context
            .get_hashtable_values();
        for &symbol in &symbols {
            let Some(definition) = self.spec.graph.op_def(symbol).cloned() else {
                continue;
            };
            if definition.def_kind != DefKind::UserDefined || definition.is_local {
                continue;
            }
            let is_origin_parameter_free = definition
                .module
                .is_none_or(|module| is_parameter_free(&self.spec.graph, module));
            let copy = if is_instancee_parameter_free || is_origin_parameter_free {
                is_local.then_some((definition.module, definition.body))
            } else {
                let body = definition.body.map(|body| {
                    self.create_subst_in(
                        false,
                        substs.clone(),
                        body,
                        instancee,
                        location.clone(),
                        self.module,
                    )
                });
                Some((Some(self.module), body))
            };
            let node = match copy {
                Some((module, body)) => {
                    let node = self.create_op_def(OpDef {
                        body,
                        is_local,
                        module,
                        source: Some(definition.source.unwrap_or(symbol)),
                        pre_comments: pre_comments.clone(),
                        labels: definition.labels.clone(),
                        ..self.new_op_def(
                            definition.name.clone(),
                            definition.params.clone().unwrap_or_default(),
                            location.clone(),
                        )
                    });
                    self.add_symbol(node);
                    node
                }
                None => {
                    self.add_symbol(symbol);
                    symbol
                }
            };
            self.spec
                .graph
                .module_mut(self.module)
                .expect("a module")
                .definitions
                .push(node);
            self.set_recursion_fields(node);
        }
        // SANY reuses a theorem of a parameter-free module without adding it to the symbol table
        // when the instantiated module has parameters.
        for &symbol in &symbols {
            let NodeKind::ThmOrAssumpDef(definition) = self.spec.graph.kind(symbol) else {
                continue;
            };
            let definition = definition.as_ref().clone();
            if definition.is_local {
                continue;
            }
            let copy = if !is_instancee_parameter_free {
                if is_parameter_free(&self.spec.graph, definition.module) {
                    is_local.then_some((self.module, definition.body))
                } else {
                    let body = self.create_subst_in(
                        true,
                        substs.clone(),
                        definition.body,
                        instancee,
                        location.clone(),
                        self.module,
                    );
                    Some((self.module, body))
                }
            } else {
                is_local.then_some((definition.module, definition.body))
            };
            let node = match copy {
                Some((module, body)) => {
                    let uid = self.spec.get_uid();
                    let source = Some(definition.source.unwrap_or(symbol));
                    let node = self.spec.graph.add(
                        uid,
                        NodeKind::ThmOrAssumpDef(Box::new(ThmOrAssumpDef {
                            body,
                            is_local,
                            location: location.clone(),
                            module,
                            source,
                            ..definition
                        })),
                    );
                    self.add_symbol(node);
                    node
                }
                None if is_instancee_parameter_free => {
                    self.add_symbol(symbol);
                    symbol
                }
                None => symbol,
            };
            if is_top_level {
                self.spec
                    .graph
                    .module_mut(self.module)
                    .expect("a module")
                    .definitions
                    .push(node);
            }
        }
        let uid = self.spec.get_uid();
        let instance_node = self.spec.graph.add(
            uid,
            NodeKind::Instance(crate::sany::nodes::Instance {
                name: None,
                is_local,
                params: Vec::new(),
                module: instancee,
                substs,
                location,
            }),
        );
        if is_top_level {
            self.spec
                .graph
                .module_mut(self.module)
                .expect("a module")
                .top_level
                .push(instance_node);
        }
        Ok(instance_node)
    }

    /// `getOperatorSpan` (generator.ts 2999–3006): a declared operator or operator parameter is
    /// located with its arguments: F(_, _), _ + _, -. _ or _ ^+.
    pub(super) fn get_operator_span(&self, start: usize, arity: usize) -> TokenSpan {
        let file = &self.file;
        if arity == 0 {
            return TokenSpan { start, end: start };
        }
        if is_token(file, start, "_") {
            let end = if is_token(file, start + 2, "_") {
                start + 2
            } else {
                start + 1
            };
            return TokenSpan { start, end };
        }
        if is_token(file, start + 1, "(") {
            return TokenSpan {
                start,
                end: get_matching_index(file, start + 1),
            };
        }
        let end = if is_token(file, start + 1, "_") {
            start + 1
        } else {
            start
        };
        TokenSpan { start, end }
    }

    /// `getDeclarationSpan` (generator.ts 3008–3009).
    pub(super) fn get_declaration_span(&self, declaration: &Declaration) -> TokenSpan {
        self.get_operator_span(
            self.get_unit_span(&declaration.location).start,
            declaration.arity,
        )
    }

    /// `createDeclaration` (generator.ts 3011–3035).
    pub(super) fn create_declaration(
        &mut self,
        declaration: &Declaration,
        decl_kind: u32,
    ) -> NodeId {
        let location = get_span_location(&self.file, self.get_declaration_span(declaration));
        // Generator.processParameters makes the same check of a constant, of the name of its
        // declaration's syntax node, which is never @.
        if &*declaration.name == "@" && decl_kind == VARIABLE_DECL_KIND {
            self.add_error(&location, "Attempted to declare '@' as a variable.");
        }
        let uid = self.spec.get_uid();
        let node = self.spec.graph.add(
            uid,
            NodeKind::OpDecl(OpDecl {
                name: resolve_synonym(&declaration.name),
                arity: declaration.arity,
                decl_kind,
                location,
                module: self.module,
            }),
        );
        let levels = self.spec.graph.levels_mut(node);
        levels.level_checked = 1;
        levels.level = u8::from(decl_kind == VARIABLE_DECL_KIND);
        if decl_kind == CONSTANT_DECL_KIND {
            levels.level_params.insert(node, ());
            levels.all_params.insert(node, ());
        }
        self.add_symbol(node);
        node
    }

    /// processExtendsList, `ast.extends.forEach` (generator.ts 3037–3071), of `self.ast`: the
    /// extended module's symbols join this module's context in the order they joined the extended
    /// module's, apart from LOCAL ones and those already present.
    pub(super) fn process_extends_list(&mut self) -> Result<()> {
        let ast = self.ast.clone();
        for name in &ast.extends {
            let extendee = self.get_module(name)?;
            self.spec
                .graph
                .module_mut(self.module)
                .expect("a module")
                .extendees
                .push(extendee);
            let symbols = self
                .spec
                .graph
                .module(extendee)
                .expect("a module")
                .context
                .symbols
                .clone();
            for symbol in symbols {
                let graph = &self.spec.graph;
                let is_local = match graph.kind(symbol) {
                    NodeKind::OpDef(definition) => definition.is_local,
                    NodeKind::ThmOrAssumpDef(definition) => definition.is_local,
                    _ => false,
                };
                if is_local {
                    continue;
                }
                let symbol_node = graph.node(symbol);
                let symbol_name = symbol_node.symbol_name().expect("a symbol").clone();
                let context =
                    get_slot_context(graph, self.symbol_table.contexts.last().expect("a context"));
                let existing = match symbol_node.kind {
                    NodeKind::Module(_) => context.get_module(&symbol_name),
                    _ => context.get_symbol(&symbol_name),
                };
                let Some(existing) = existing else {
                    self.add_to_top_context(symbol);
                    continue;
                };
                if existing == symbol {
                    continue;
                }
                let existing_node = graph.node(existing);
                if discriminant(&existing_node.kind) != discriminant(&symbol_node.kind) {
                    let text = format!(
                        "The {} of '{symbol_name}' conflicts with \nits {} at {}.",
                        get_kind_name(symbol_node),
                        get_kind_name(existing_node),
                        self.format_symbol_location(existing)
                    );
                    self.add_symbol_message(symbol, text, false);
                } else if !is_same_origin(graph, existing, symbol) {
                    // Context.mergeExtendContext names the kind of the existing symbol twice.
                    let kind_name = get_kind_name(existing_node);
                    let text = format!(
                        "Warning: the {kind_name} of '{symbol_name}' conflicts with \nits {kind_name} at {}.",
                        self.format_symbol_location(existing)
                    );
                    self.add_symbol_message(symbol, text, true);
                }
            }
            let top_level = self
                .spec
                .graph
                .module(extendee)
                .expect("a module")
                .top_level
                .clone();
            self.spec
                .graph
                .module_mut(self.module)
                .expect("a module")
                .top_level
                .extend(top_level);
        }
        Ok(())
    }

    /// `checkRecursiveSection` (generator.ts 3073–3081): Generator.checkIfInRecursiveSection, only
    /// definitions and instances may come between a RECURSIVE declaration and the definition of
    /// what it declares. `kind` is the TypeScript's `type`.
    pub(super) fn check_recursive_section(&mut self, location: &Location, kind: &str) {
        if self.state.unresolved_sum == 0 {
            return;
        }
        let location = get_span_location(&self.file, self.get_unit_span(location));
        self.add_error(
            &location,
            format!("{kind} may not appear within a recursive definition section."),
        );
    }

    /// `ast.units.forEach` and the `checkForUndefinedRecursiveOps` after it (generator.ts
    /// 3083–3138), over `self.ast`. An inner module is `generate_inner_module`.
    pub(super) fn process_units(&mut self) -> Result<()> {
        let ast = self.ast.clone();
        for unit in &ast.units {
            match unit {
                ModuleUnit::Variables {
                    declarations,
                    location,
                } => {
                    self.check_recursive_section(location, "A VARIABLE declaration");
                    for declaration in declarations {
                        self.create_declaration(declaration, VARIABLE_DECL_KIND);
                    }
                }
                ModuleUnit::Constants {
                    declarations,
                    location,
                } => {
                    self.check_recursive_section(location, "A declaration");
                    for declaration in declarations {
                        self.create_declaration(declaration, CONSTANT_DECL_KIND);
                    }
                }
                ModuleUnit::Recursive(declarations) => self.process_recursive(declarations),
                ModuleUnit::Definition(definition) => match definition.kind {
                    DefinitionKind::Function { .. } => self.process_function(definition, None)?,
                    DefinitionKind::Operator { .. } => self.process_operator(definition, None)?,
                },
                ModuleUnit::Instance(instance) => {
                    if instance.name.is_none() {
                        self.generate_instance(instance, true, None)?;
                    } else {
                        self.process_module_definition(instance, None, None)?;
                    }
                }
                ModuleUnit::Assumption(assumption) => {
                    self.check_recursive_section(&assumption.location, "An ASSUME");
                    self.process_assumption(assumption)?;
                }
                ModuleUnit::Theorem(theorem) => {
                    self.check_recursive_section(&theorem.location, "A THEOREM");
                    self.process_theorem(theorem)?;
                }
                ModuleUnit::Use(use_or_hide) => {
                    self.check_recursive_section(&use_or_hide.location, "A USE or HIDE");
                    let node = self.generate_use_or_hide(use_or_hide)?;
                    self.spec
                        .graph
                        .module_mut(self.module)
                        .expect("a module")
                        .top_level
                        .push(node);
                }
                ModuleUnit::Module(module) => {
                    self.check_recursive_section(&module.location, "A MODULE ");
                    let inner = self.generate_inner_module(module)?;
                    // SymbolTable.addModule: an inner module's name must not be taken by another
                    // module, inner or external.
                    let inner_module = self.spec.graph.module(inner).expect("a module");
                    let inner_name = inner_module.name.clone();
                    let inner_location = inner_module.location.clone();
                    match self.resolve_module(&inner_name) {
                        None => self.add_to_top_context(inner),
                        Some(binding) if binding != inner => {
                            let text = format!(
                                "Multiply-defined module '{inner_name}': this definition or declaration conflicts \nwith the one at {}.",
                                self.format_symbol_location(binding)
                            );
                            self.add_error(&inner_location, text);
                        }
                        Some(_) => {}
                    }
                }
            }
        }
        self.check_for_undefined_recursive_ops();
        Ok(())
    }
}
